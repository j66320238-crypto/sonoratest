'use strict';
/* ============================================================
   /api/download  --  build a real, playable file out of an HLS stream.

   The provider hands us adaptive playlists, not files. A "download"
   button therefore has to do the work a player normally does live:
   pick a video rendition, pick an audio rendition in the language the
   user asked for, pull every segment, and stitch them into one
   container. We stream the result straight to the client as it is
   built, so a 24-minute episode starts saving within a second or two
   and never occupies more than a segment of memory on the server.

   Video and audio arrive as separate single-track streams that both
   claim PID 256, so they are remapped onto distinct PIDs and given a
   fresh PAT/PMT -- see lib/tsmux.js for why that beats shelling out to
   ffmpeg here. When a rendition is already muxed (some providers do
   that for the default language) we pass it through untouched.
   ============================================================ */

const tsmux = require('./tsmux');

/* ISO-639-2 codes so players label the track properly. Anything not
   listed falls back to 'und', which is still valid. */
const LANG3 = {
  hindi: 'hin', hin: 'hin', hi: 'hin',
  english: 'eng', eng: 'eng', en: 'eng',
  japanese: 'jpn', jpn: 'jpn', ja: 'jpn',
  tamil: 'tam', tam: 'tam', ta: 'tam',
  telugu: 'tel', tel: 'tel', te: 'tel',
  bengali: 'ben', ben: 'ben', bn: 'ben',
  marathi: 'mar', kannada: 'kan', malayalam: 'mal',
  korean: 'kor', kor: 'kor', ko: 'kor',
  spanish: 'spa', french: 'fre', german: 'ger',
  arabic: 'ara', portuguese: 'por', russian: 'rus',
};

function lang3(name) {
  if (!name) return 'und';
  return LANG3[String(name).trim().toLowerCase()] || 'und';
}

function attrs(line) {
  const out = {};
  const re = /([A-Z0-9-]+)=("[^"]*"|[^,]*)/g;
  let m;
  while ((m = re.exec(line))) out[m[1]] = m[2].replace(/^"|"$/g, '');
  return out;
}

/* Parse a master playlist into its video renditions and audio tracks.
   Media URIs are resolved against the FULL master URL, never its
   directory: this provider emits root-relative "/hls/<blob>" URIs and a
   dirname join silently produces 404s. */
function parseMaster(text, masterUrl) {
  const lines = text.split(/\r?\n/);
  const videos = [];
  const audios = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (line.startsWith('#EXT-X-MEDIA:')) {
      const a = attrs(line.slice(13));
      if ((a.TYPE || '').toUpperCase() !== 'AUDIO' || !a.URI) continue;
      audios.push({
        name: a.NAME || a.LANGUAGE || 'Audio',
        language: a.LANGUAGE || '',
        isDefault: /yes/i.test(a.DEFAULT || ''),
        group: a['GROUP-ID'] || '',
        url: new URL(a.URI, masterUrl).toString(),
      });
    } else if (line.startsWith('#EXT-X-STREAM-INF:')) {
      const a = attrs(line.slice(18));
      let uri = '';
      for (let j = i + 1; j < lines.length; j++) {
        const nxt = lines[j].trim();
        if (!nxt || nxt.startsWith('#')) continue;
        uri = nxt; i = j; break;
      }
      if (!uri) continue;
      const res = a.RESOLUTION || '';
      const height = res.includes('x') ? parseInt(res.split('x')[1], 10) : 0;
      videos.push({
        height: Number.isFinite(height) ? height : 0,
        bandwidth: parseInt(a.BANDWIDTH || '0', 10) || 0,
        audioGroup: a.AUDIO || '',
        url: new URL(uri, masterUrl).toString(),
      });
    }
  }
  videos.sort((x, y) => (y.height - x.height) || (y.bandwidth - x.bandwidth));
  return { videos, audios };
}

function parseMediaPlaylist(text, playlistUrl) {
  const segments = [];
  let duration = 0;
  let pending = 0;
  for (const raw of text.split(/\r?\n/)) {
    const line = raw.trim();
    if (!line) continue;
    if (line.startsWith('#EXTINF:')) {
      const d = parseFloat(line.slice(8));
      if (Number.isFinite(d)) { duration += d; pending = d; }
      continue;
    }
    if (line.startsWith('#EXT-X-KEY') && !/METHOD=NONE/i.test(line)) {
      // Encrypted segments would need the key and an AES-128-CBC pass.
      // Rather than emit a corrupt file, refuse clearly.
      const err = new Error('This stream is encrypted and cannot be downloaded.');
      err.status = 415;
      throw err;
    }
    if (line.startsWith('#')) continue;
    segments.push({ url: new URL(line, playlistUrl).toString(), duration: pending || 0 });
    pending = 0;
  }
  return { segments, duration };
}

function pickVideo(videos, wanted) {
  if (!videos.length) return null;
  if (!wanted || wanted === 'best') return videos[0];
  if (wanted === 'worst') return videos[videos.length - 1];
  const target = parseInt(String(wanted).replace(/\D/g, ''), 10);
  if (!Number.isFinite(target)) return videos[0];
  // Closest rendition at or below the request, else the smallest above it,
  // so asking for 720 on a 1080/480 stream gives 480 rather than a 1080
  // file the user did not want to pay for in data.
  const atOrBelow = videos.filter((v) => v.height <= target);
  return atOrBelow.length ? atOrBelow[0] : videos[videos.length - 1];
}

function pickAudio(audios, wanted) {
  if (!audios.length) return null;
  if (wanted) {
    const want = String(wanted).trim().toLowerCase();
    const hit = audios.find((a) =>
      a.name.toLowerCase() === want ||
      a.language.toLowerCase() === want ||
      lang3(a.name) === lang3(want));
    if (hit) return hit;
  }
  return audios.find((a) => a.isDefault) || audios[0];
}

function safeName(s) {
  return String(s || 'video')
    .replace(/[^\w\s.-]+/g, ' ')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 90) || 'video';
}

/* Pull one segment with a bounded number of retries. A single flaky
   segment must not abort a download the user has been waiting on. */
async function fetchSegment(url, fetchUpstream, req, attempts = 3) {
  let lastErr;
  for (let i = 0; i < attempts; i++) {
    try {
      const { response } = await fetchUpstream(url, req);
      if (!response.ok) throw new Error('segment ' + response.status);
      return Buffer.from(await response.arrayBuffer());
    } catch (e) {
      lastErr = e;
      if (i < attempts - 1) await new Promise((r) => setTimeout(r, 400 * (i + 1)));
    }
  }
  throw lastErr;
}

/* Fetch ahead so the network is never idle while we write, but keep the
   window small: each slot is a whole segment held in memory, and the
   point of streaming is to stay flat regardless of episode length. */
const LOOKAHEAD = 4;

async function* segmentStream(urls, fetchUpstream, req, shouldStop) {
  const queue = [];
  let next = 0;
  const fill = () => {
    while (queue.length < LOOKAHEAD && next < urls.length) {
      const seg = urls[next++];
      queue.push(fetchSegment(seg.url, fetchUpstream, req)
        .then((data) => ({ data, duration: seg.duration }))
        .catch((e) => ({ __error: e })));
    }
  };
  fill();
  while (queue.length) {
    if (shouldStop()) return;
    const chunk = await queue.shift();
    fill();
    if (chunk && chunk.__error) throw chunk.__error;
    yield chunk;
  }
}

/**
 * @param {object} deps  { fetchHlsUpstream, securityHeaders, httpError }
 */
function createDownloadHandler(deps) {
  const { fetchHlsUpstream, securityHeaders } = deps;

  async function getText(url, req) {
    const { response, finalUrl } = await fetchHlsUpstream(url, req);
    if (!response.ok) {
      const err = new Error('Could not read the stream playlist.');
      err.status = 502;
      throw err;
    }
    return { text: await response.text(), finalUrl: finalUrl.toString() };
  }

  /* GET /api/download/info?url=<master> -> what can be downloaded. */
  async function info(req, res, u) {
    const target = u.searchParams.get('url');
    if (!target) {
      res.writeHead(400, securityHeaders({ 'Content-Type': 'application/json' }));
      return res.end(JSON.stringify({ ok: false, error: 'url required' }));
    }
    try {
      const { text, finalUrl } = await getText(target, req);
      if (!/#EXTM3U/.test(text)) throw Object.assign(new Error('not a playlist'), { status: 415 });

      if (!/#EXT-X-STREAM-INF/.test(text)) {
        // A media playlist on its own: one quality, one (muxed) track.
        const { duration } = parseMediaPlaylist(text, finalUrl);
        const body = {
          ok: true, master: false, duration,
          qualities: [{ label: 'Original', value: 'best', height: 0 }],
          audio: [],
        };
        res.writeHead(200, securityHeaders({ 'Content-Type': 'application/json', 'Cache-Control': 'no-store' }));
        return res.end(JSON.stringify(body));
      }

      const { videos, audios } = parseMaster(text, finalUrl);
      const body = {
        ok: true,
        master: true,
        qualities: videos.map((v) => ({
          label: v.height ? v.height + 'p' : 'Auto',
          value: v.height ? String(v.height) : 'best',
          height: v.height,
          bandwidth: v.bandwidth,
        })),
        audio: audios.map((a) => ({
          label: a.name,
          value: a.name,
          language: a.language,
          code: lang3(a.name || a.language),
          default: a.isDefault,
        })),
      };
      res.writeHead(200, securityHeaders({ 'Content-Type': 'application/json', 'Cache-Control': 'no-store' }));
      return res.end(JSON.stringify(body));
    } catch (e) {
      res.writeHead(e.status || 502, securityHeaders({ 'Content-Type': 'application/json', 'Cache-Control': 'no-store' }));
      return res.end(JSON.stringify({ ok: false, error: e.message || 'download info failed' }));
    }
  }

  /* GET /api/download?url=<master>&quality=720&audio=Hindi&name=Title */
  async function download(req, res, u) {
    const target = u.searchParams.get('url');
    if (!target) {
      res.writeHead(400, securityHeaders({ 'Content-Type': 'text/plain; charset=utf-8' }));
      return res.end('url required');
    }
    const wantQuality = u.searchParams.get('quality') || 'best';
    const wantAudio = u.searchParams.get('audio') || '';
    const filename = safeName(u.searchParams.get('name')) + '.ts';

    try {
      const { text, finalUrl } = await getText(target, req);
      if (!/#EXTM3U/.test(text)) throw Object.assign(new Error('not a playlist'), { status: 415 });

      let videoUrl = finalUrl;
      let audioTrack = null;
      if (/#EXT-X-STREAM-INF/.test(text)) {
        const { videos, audios } = parseMaster(text, finalUrl);
        const video = pickVideo(videos, wantQuality);
        if (!video) throw Object.assign(new Error('no video rendition'), { status: 415 });
        videoUrl = video.url;
        // Only graft audio when the master actually offers separate
        // tracks; otherwise the video rendition is already muxed.
        if (audios.length) audioTrack = pickAudio(audios, wantAudio);
      }

      const videoPl = await getText(videoUrl, req);
      const videoSegs = parseMediaPlaylist(videoPl.text, videoPl.finalUrl).segments;
      if (!videoSegs.length) throw Object.assign(new Error('empty stream'), { status: 502 });

      let audioSegs = null;
      let audioLang = 'und';
      if (audioTrack) {
        const audioPl = await getText(audioTrack.url, req);
        audioSegs = parseMediaPlaylist(audioPl.text, audioPl.finalUrl).segments;
        audioLang = lang3(audioTrack.name || audioTrack.language);
        if (!audioSegs.length) audioSegs = null;
      }

      // Length is unknowable up front (segments are variable size), so the
      // browser shows a growing byte count instead of a percentage. That is
      // the honest trade for starting the save immediately.
      res.writeHead(200, securityHeaders({
        'Content-Type': 'video/mp2t',
        'Content-Disposition': `attachment; filename="${filename}"`,
        'Cache-Control': 'no-store',
        'X-Accel-Buffering': 'no',
      }));
      if (req.method === 'HEAD') return res.end();

      const stop = () => res.destroyed || res.writableEnded || !res.writable;

      const write = async (buf) => {
        if (!buf || !buf.length) return true;
        if (stop()) return false;
        if (res.write(buf)) return true;
        return new Promise((resolve) => {
          let settled = false;
          const finish = (ok) => { if (!settled) { settled = true; cleanup(); resolve(ok); } };
          const timer = setTimeout(() => finish(false), 30000);
          function cleanup() {
            clearTimeout(timer);
            res.off('drain', onDrain); res.off('close', onStop); res.off('error', onStop);
          }
          const onDrain = () => finish(true);
          const onStop = () => finish(false);
          res.once('drain', onDrain); res.once('close', onStop); res.once('error', onStop);
        });
      };

      if (!audioSegs) {
        // Already muxed: straight concatenation is a valid TS file.
        for await (const chunk of segmentStream(videoSegs, fetchHlsUpstream, req, stop)) {
          if (!(await write(chunk.data))) break;
        }
        if (!res.writableEnded) res.end();
        return;
      }

      // Separate tracks: emit our own tables, then interleave the two
      // streams so a player can start decoding immediately.
      await write(tsmux.buildPat());
      await write(tsmux.buildPmt([
        { type: 0x1b, pid: tsmux.VIDEO_PID },
        { type: 0x0f, pid: tsmux.AUDIO_PID, lang: audioLang },
      ]));

      const vState = { cc: 15 };
      const aState = { cc: 15 };
      const vIter = segmentStream(videoSegs, fetchHlsUpstream, req, stop)[Symbol.asyncIterator]();
      const aIter = segmentStream(audioSegs, fetchHlsUpstream, req, stop)[Symbol.asyncIterator]();
      let vDone = false; let aDone = false;
      let vClock = 0; let aClock = 0;

      /* Interleave by MEDIA TIME, not by segment count. The two renditions
         are cut on completely different boundaries -- this provider ships
         720 video segments of ~2 s against 145 audio segments of ~10 s --
         so pulling one of each per turn raced the audio roughly 1,000
         seconds ahead of the video by the end of an episode. Players that
         trust the PTS then desync badly, and players that buffer ahead run
         out of memory. Emitting whichever track is furthest behind keeps
         the two clocks within one segment of each other for the whole file. */
      while (!vDone || !aDone) {
        if (stop()) break;
        const takeVideo = !vDone && (aDone || vClock <= aClock);
        if (takeVideo) {
          const next = await vIter.next();
          if (next.done) { vDone = true; continue; }
          vClock += next.value.duration || 0;
          if (!(await write(tsmux.remapSegment(next.value.data, tsmux.VIDEO_PID, vState)))) break;
        } else {
          const next = await aIter.next();
          if (next.done) { aDone = true; continue; }
          aClock += next.value.duration || 0;
          if (!(await write(tsmux.remapSegment(next.value.data, tsmux.AUDIO_PID, aState)))) break;
        }
      }
      if (!res.writableEnded) res.end();
    } catch (e) {
      if (!res.headersSent) {
        res.writeHead(e.status || 502, securityHeaders({ 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' }));
        res.end(e.message || 'download failed');
      } else if (!res.writableEnded) {
        // Headers are already out, so the file is partial. Destroying the
        // socket makes the browser mark the download as failed rather than
        // leaving the user with a truncated file that looks complete.
        res.destroy();
      }
    }
  }

  return { info, download };
}

module.exports = { createDownloadHandler, parseMaster, parseMediaPlaylist, pickVideo, pickAudio, lang3, safeName };

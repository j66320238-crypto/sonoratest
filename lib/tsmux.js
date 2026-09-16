'use strict';
/* ============================================================
   Minimal MPEG-TS remuxer.

   WHY THIS EXISTS
   The multi-audio anime provider serves video and audio as SEPARATE
   HLS renditions: the 720p playlist carries only H.264 (stream type
   0x1b) and the Hindi playlist carries only AAC (stream type 0x0f).
   Both label their elementary stream PID 256, so you cannot simply
   concatenate the two byte streams -- the PIDs collide and a player
   sees one broken track instead of two good ones.

   ffmpeg would solve this in one line, but it is a ~70 MB dependency
   that is not installed on Render's free tier, so downloads would work
   on a dev box and silently fail in production. Instead we do the only
   part of the job that is actually needed: rewrite the PID field of the
   audio packets, renumber their continuity counters, and emit a fresh
   PAT/PMT that declares both tracks. Everything else -- the PES
   payloads, the timestamps, the AAC and H.264 bitstreams -- passes
   through untouched, so there is no re-encode, no quality loss and
   almost no CPU cost.

   The output is a single .ts file that plays in VLC, MX Player and
   every mobile gallery player, with the chosen language as its audio.
   ============================================================ */

const PACKET = 188;
const SYNC = 0x47;

const PAT_PID = 0x0000;
const PMT_PID = 0x1000;
const VIDEO_PID = 0x0100;
const AUDIO_PID = 0x0101;

/* CRC-32/MPEG-2, the variant the transport stream tables use. */
const CRC_TABLE = (() => {
  const table = new Int32Array(256);
  for (let i = 0; i < 256; i++) {
    let crc = i << 24;
    for (let bit = 0; bit < 8; bit++) {
      crc = (crc & 0x80000000) ? ((crc << 1) ^ 0x04c11db7) : (crc << 1);
    }
    table[i] = crc;
  }
  return table;
})();

function crc32(buf) {
  let crc = -1;
  for (let i = 0; i < buf.length; i++) {
    crc = (crc << 8) ^ CRC_TABLE[((crc >>> 24) ^ buf[i]) & 0xff];
  }
  return crc >>> 0;
}

/* Wrap a PSI section in a 188-byte packet. Sections here are far
   shorter than a packet, so no continuation is ever needed. */
function psiPacket(pid, section, continuity) {
  const pkt = Buffer.alloc(PACKET, 0xff);
  pkt[0] = SYNC;
  pkt[1] = 0x40 | ((pid >> 8) & 0x1f); // payload_unit_start_indicator
  pkt[2] = pid & 0xff;
  pkt[3] = 0x10 | (continuity & 0x0f); // payload only
  pkt[4] = 0x00; // pointer_field
  section.copy(pkt, 5);
  return pkt;
}

function buildPat() {
  // table_id .. last_section_number, then one program entry, then CRC.
  const body = Buffer.from([
    0x00, 0xb0, 0x0d, 0x00, 0x01, 0xc1, 0x00, 0x00,
    0x00, 0x01, 0xe0 | ((PMT_PID >> 8) & 0x1f), PMT_PID & 0xff,
  ]);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(body), 0);
  return psiPacket(PAT_PID, Buffer.concat([body, crc]), 0);
}

/* streams: [{ type, pid, lang }] -- lang is an optional ISO-639-2 code
   written as an ISO_639_language_descriptor so players show a proper
   track name ("Hindi") instead of "Track 1". */
function buildPmt(streams) {
  const entries = streams.map((s) => {
    let desc = Buffer.alloc(0);
    if (s.lang && s.lang.length === 3) {
      desc = Buffer.concat([
        Buffer.from([0x0a, 0x04]),
        Buffer.from(s.lang, 'ascii'),
        Buffer.from([0x00]), // audio_type: undefined
      ]);
    }
    return Buffer.concat([
      Buffer.from([
        s.type,
        0xe0 | ((s.pid >> 8) & 0x1f), s.pid & 0xff,
        0xf0 | ((desc.length >> 8) & 0x0f), desc.length & 0xff,
      ]),
      desc,
    ]);
  });
  const payload = Buffer.concat(entries);
  // 9 bytes of PMT header after section_length + 4 bytes CRC.
  const sectionLength = 9 + payload.length + 4;
  const header = Buffer.from([
    0x02,
    0xb0 | ((sectionLength >> 8) & 0x0f), sectionLength & 0xff,
    0x00, 0x01, // program_number
    0xc1, 0x00, 0x00,
    0xe0 | ((VIDEO_PID >> 8) & 0x1f), VIDEO_PID & 0xff, // PCR_PID
    0xf0, 0x00, // program_info_length
  ]);
  const body = Buffer.concat([header, payload]);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(body), 0);
  return psiPacket(PMT_PID, Buffer.concat([body, crc]), 0);
}

function pidOf(pkt, off) {
  return ((pkt[off + 1] & 0x1f) << 8) | pkt[off + 2];
}
function hasPayload(pkt, off) {
  return (pkt[off + 3] & 0x10) !== 0;
}

/* Rewrite one segment's packets onto a target PID.

   `state` carries the continuity counter across segments, because a
   player treats a counter jump as a discontinuity and drops audio.
   PSI packets (PAT/PMT) from the source are discarded -- we emit our
   own -- and null packets are dropped to save bytes. */
function remapSegment(buf, targetPid, state) {
  const out = [];
  for (let off = 0; off + PACKET <= buf.length; off += PACKET) {
    if (buf[off] !== SYNC) {
      // Resync rather than abandon: a truncated read mid-segment would
      // otherwise throw away the rest of a perfectly good file.
      let next = off + 1;
      while (next + PACKET <= buf.length && buf[next] !== SYNC) next++;
      if (next + PACKET > buf.length) break;
      off = next - PACKET;
      continue;
    }
    const pid = pidOf(buf, off);
    if (pid === 0x1fff) continue;               // null padding
    if (pid === PAT_PID || pid === PMT_PID) continue; // our tables win
    if (pid === 0x0011 || pid === 0x0012) continue;   // SDT/EIT: noise

    const pkt = Buffer.from(buf.subarray(off, off + PACKET));
    pkt[1] = (pkt[1] & 0xe0) | ((targetPid >> 8) & 0x1f);
    pkt[2] = targetPid & 0xff;
    if (hasPayload(pkt, 0)) {
      state.cc = (state.cc + 1) & 0x0f;
      pkt[3] = (pkt[3] & 0xf0) | state.cc;
    } else {
      pkt[3] = (pkt[3] & 0xf0) | state.cc;
    }
    out.push(pkt);
  }
  return out.length ? Buffer.concat(out) : Buffer.alloc(0);
}

/* Strip a source stream down to its elementary packets without changing
   the PID -- used when the source is already muxed and we only need to
   drop its tables so our own PAT/PMT stay authoritative. */
function passthroughSegment(buf) {
  const out = [];
  for (let off = 0; off + PACKET <= buf.length; off += PACKET) {
    if (buf[off] !== SYNC) break;
    const pid = pidOf(buf, off);
    if (pid === 0x1fff) continue;
    out.push(buf.subarray(off, off + PACKET));
  }
  return out.length ? Buffer.concat(out) : Buffer.alloc(0);
}

module.exports = {
  PACKET, VIDEO_PID, AUDIO_PID,
  buildPat, buildPmt, remapSegment, passthroughSegment, crc32,
};

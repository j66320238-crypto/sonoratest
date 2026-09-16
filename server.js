/* ============================================================
   StreamVerse v11.1 — backend (Node.js, ZERO npm dependencies)
   Primary: TMDB (movies/TV), AniList (anime)
   Backup : Cinemeta (movies/TV), Jikan (anime), ipapi.co (geo)
   + stale-if-error cache, gzip/br compression, security headers
   ============================================================ */
'use strict';

const http = require('http');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const dns = require('dns').promises;
const net = require('net');
const crypto = require('crypto');
const { extractMovieStreams } = require('./movie-extract');
const { createDownloadHandler } = require('./lib/download');

const VERSION = '12.14.1';
const PORT = process.env.PORT || 3000;
const HOST = '0.0.0.0';
const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/126 Safari/537.36';

const PUBLIC_DIR = fs.existsSync(path.join(__dirname, 'public', 'index.html'))
  ? path.join(__dirname, 'public')
  : __dirname;

// Keep the TMDB credential on the server. Never commit a fallback key.
const TMDB_KEY = String(process.env.TMDB_KEY || '').trim();
const TMDB_BASE = 'https://api.themoviedb.org/3';
const CINEMETA = 'https://v3-cinemeta.strem.io';
const ANILIST = 'https://graphql.anilist.co';
const WATCH_REGION = process.env.WATCH_REGION || 'IN';

/* ---------------- stats + online presence ---------------- */
const stats = {
  started: Date.now(),
  requests: 0,
  apiBytes: 0,
  hlsBytes: 0,
  rateLimited: 0,
  backupsUsed: { cinemeta: 0, anilist: 0, ipapi: 0, staleCache: 0 },
  top: {},
};
const apiHealth = { tmdb: '?', jikan: '?', cinemeta: '?', anilist: '?', geo: '?' };

// online presence: heartbeats live for 75s; sweep every 15s.
const presence = new Map(); // token -> lastSeen
let anonCounter = 0;
function sweepPresence() {
  const now = Date.now();
  for (const [k, v] of presence) if (now - v > 75000) presence.delete(k);
}
function onlineCount() { sweepPresence(); return presence.size; }
setInterval(sweepPresence, 15000).unref?.();

/* ---------------- cache (stale-if-error) ---------------- */
const CACHE_MAX_ITEMS = Math.max(100, Number(process.env.CACHE_MAX_ITEMS) || 900);
const cache = new Map();
const inFlight = new Map();

function touchCache(key, entry) {
  cache.delete(key);
  cache.set(key, entry);
}

async function cached(key, ttl, fn, staleOnError = true) {
  const hit = cache.get(key);
  if (hit && Date.now() - hit.t < ttl) {
    touchCache(key, hit); // small LRU: frequently used entries survive
    return hit.v;
  }
  // Coalesce identical requests so a cold Render instance does not spend the
  // TMDB quota several times while the home page is opening.
  if (inFlight.has(key)) return inFlight.get(key);

  const job = (async () => {
    try {
      const v = await fn();
      touchCache(key, { t: Date.now(), v });
      while (cache.size > CACHE_MAX_ITEMS) cache.delete(cache.keys().next().value);
      return v;
    } catch (e) {
      if (staleOnError && hit) {
        stats.backupsUsed.staleCache++;
        touchCache(key, hit);
        return hit.v && !Array.isArray(hit.v) && typeof hit.v === 'object'
          ? { ...hit.v, _stale: true }
          : hit.v;
      }
      throw e;
    } finally {
      inFlight.delete(key);
    }
  })();
  inFlight.set(key, job);
  return job;
}

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

/* ---------------- circuit breaker ----------------
   AniList has been globally 403 ("temporarily disabled") for a while. Every
   anime route calls it as the PRIMARY, so each request burned ~12s of retries
   before falling through to Jikan. Once an upstream has failed N times in a
   row we fail instantly for a cool-off window instead of hammering it. */
const breakers = new Map();
function breaker(name, { threshold = 3, coolOffMs = 5 * 60 * 1000 } = {}) {
  let b = breakers.get(name);
  if (!b) { b = { fails: 0, openUntil: 0, threshold, coolOffMs }; breakers.set(name, b); }
  return b;
}
function breakerOpen(name) {
  const b = breaker(name);
  if (b.openUntil && b.openUntil <= Date.now()) {
    /* cool-off elapsed -> HALF-OPEN. Reset the failure counter so a single
       hiccup does not instantly re-open the circuit for another 5 minutes
       (that bug pinned AniList "open" forever while it was actually healthy). */
    b.openUntil = 0;
    b.fails = 0;
    b.halfOpen = true;
  }
  return b.openUntil > Date.now();
}
function breakerFail(name) {
  const b = breaker(name);
  b.fails++;
  b.halfOpen = false;
  if (b.fails >= b.threshold) b.openUntil = Date.now() + b.coolOffMs;
}
function breakerOk(name) {
  const b = breaker(name);
  b.fails = 0; b.openUntil = 0; b.halfOpen = false;
}
function breakerState(name) {
  const b = breaker(name);
  const open = b.openUntil > Date.now();
  return { name, open, halfOpen: !!b.halfOpen, fails: b.fails, retryInMs: open ? b.openUntil - Date.now() : 0 };
}
function breakerReset(name) {
  if (name) { breakerOk(name); return 1; }
  let n = 0;
  for (const k of breakers.keys()) { breakerOk(k); n++; }
  return n;
}
async function viaBreaker(name, fn) {
  if (breakerOpen(name)) {
    const e = new Error(name + ' circuit open');
    e.circuitOpen = true;
    throw e;
  }
  try { const v = await fn(); breakerOk(name); return v; }
  catch (e) { breakerFail(name); throw e; }
}

/* ---------------- global outbound rate limiter ----------------
   Jikan allows ~60 req/min / 3 req/s PER IP. On Render every user shares one
   egress IP, so unthrottled traffic 429s almost immediately and cold cache
   keys throw -> the client shows "Could not load. Try again.".
   This queue is process-wide (not per-user) and serialises outbound calls. */
function rateLimiter({ minIntervalMs, burst = 1, maxQueue = 120 }) {
  let queue = [];
  let tokens = burst;
  let last = Date.now();
  let timer = null;
  function refill() {
    const now = Date.now();
    const gained = Math.floor((now - last) / minIntervalMs);
    if (gained > 0) { tokens = Math.min(burst, tokens + gained); last += gained * minIntervalMs; }
    // While idle, `last` stays up to one interval in the past. Without this
    // line the next few schedule() calls each "gain" a backdated token and the
    // burst silently becomes 8-9 instead of 3 - which is exactly what let the
    // storm test blow past Jikan's limit.
    if (tokens >= burst) last = now;
  }
  function pump() {
    refill();
    while (tokens > 0 && queue.length) { tokens--; queue.shift().go(); }
    if (queue.length && !timer) {
      timer = setTimeout(() => { timer = null; pump(); }, minIntervalMs);
      if (timer.unref) timer.unref();
    }
  }
  return function schedule(fn) {
    return new Promise((resolve, reject) => {
      if (queue.length >= maxQueue) { reject(new Error('rate limiter queue full')); return; }
      queue.push({ go: () => { Promise.resolve().then(fn).then(resolve, reject); } });
      pump();
    });
  };
}
// ~1.2 req/s sustained with a small burst: comfortably inside Jikan's budget.
const jikanLimit = rateLimiter({ minIntervalMs: 850, burst: 3, maxQueue: 150 });
/* AniList advertises x-ratelimit-limit: 30 per minute and had no limiter at
   all, so a burst of chip taps (each one a fresh GraphQL call) blew through it
   and the extra requests came back as errors - which is why unrelated, valid
   genres like Comedy/Drama/Fantasy intermittently rendered an empty grid.
   30/min is one per 2000ms *on average*, not a 2s wall between calls: a plain
   serial limiter made the 12th chip tap wait 25s. A token bucket matches the
   real policy - up to `burst` requests answered instantly, then refilling at
   the sustained rate - so interactive taps stay snappy and only sustained
   load is throttled. Burst sits just under 30 to leave headroom. */
const anilistLimit = rateLimiter({ minIntervalMs: 2100, burst: 26, maxQueue: 150 });

async function jfetch(url, { method = 'GET', body, headers = {}, timeout = 12000, retries = 2 } = {}) {
  let lastErr;
  for (let attempt = 0; attempt <= retries; attempt++) {
    const ctrl = new AbortController();
    const timer = setTimeout(() => ctrl.abort(), timeout);
    try {
      const r = await fetch(url, {
        method, body, signal: ctrl.signal, redirect: 'follow',
        headers: { 'User-Agent': UA, Accept: 'application/json', ...headers },
      });
      clearTimeout(timer);
      if (!r.ok) {
        const err = new Error('HTTP ' + r.status);
        err.status = r.status;
        // Retry only transient upstream failures. Retrying a 404/401 wastes
        // quota and makes the UI feel slow.
        if ((r.status === 429 || r.status >= 500) && attempt < retries) {
          const retryAfter = Number(r.headers.get('retry-after')) || 0;
          await sleep(Math.min(4000, retryAfter * 1000 || 650 * (attempt + 1)));
          lastErr = err;
          continue;
        }
        throw err;
      }
      return await r.json();
    } catch (e) {
      clearTimeout(timer);
      lastErr = e;
      const retryable = e.name === 'AbortError' || !e.status || e.status === 429 || e.status >= 500;
      if (attempt < retries && retryable) {
        await sleep(500 * (attempt + 1));
        continue;
      }
      break;
    }
  }
  throw lastErr || new Error('fetch failed');
}

/* ---------------- TMDB ---------------- */
function tmdb(p, params = {}, ttl = 15 * 60 * 1000) {
  if (!TMDB_KEY) {
    apiHealth.tmdb = 'missing-key';
    throw httpError(503, 'TMDB_KEY is not configured on the server');
  }
  const safeParams = { language: 'en-US', ...params, api_key: TMDB_KEY };
  const q = new URLSearchParams(safeParams).toString();
  const url = `${TMDB_BASE}${p}?${q}`;
  return cached('tmdb:' + url, ttl, async () => {
    try { const v = await jfetch(url); apiHealth.tmdb = 'ok'; return v; }
    catch (e) { apiHealth.tmdb = e.status === 401 ? 'bad-key' : 'error'; throw e; }
  });
}
const SUPPORTED_LOCALE = /^[a-z]{2}(?:-[A-Z]{2})?$/;
const langOf = (q) => {
  const value = q.get('lang') || 'en-US';
  return SUPPORTED_LOCALE.test(value) ? value : 'en-US';
};

/* ---------------- Cinemeta backup ---------------- */
function cinemetaToTmdbList(metas, mediaType) {
  return {
    results: (metas || []).map((m) => ({
      // v12.13.1: prefer the IMDB id. moviedb_id only resolves through TMDB,
      // so on a keyless deploy the card carried a numeric id that /api/details
      // then looked up against Cinemeta -- which speaks IMDB ids -- and 404'd,
      // leaving every detail modal empty. The IMDB id works for BOTH backends.
      id: m.imdb_id || m.id || m.moviedb_id,
      media_type: mediaType,
      title: m.name, name: m.name,
      poster_path: m.poster || '', backdrop_path: m.background || '',
      vote_average: parseFloat(m.imdbRating) || 0,
      // Only populate the date field that matches the media type. Setting both
      // made the client's mediaOf() -- which treats any first_air_date as a
      // series marker -- classify every Cinemeta movie as 'tv', so details and
      // stream lookups were requested with the wrong media kind.
      release_date: mediaType === 'movie' ? (m.released ? String(m.released).slice(0, 10) : (m.year || '')) : '',
      first_air_date: mediaType === 'tv' ? (m.released ? String(m.released).slice(0, 10) : (m.year || '')) : '',
      overview: m.description || '',
      /* Carried through for the Drama tab, which filters by origin country.
         Underscore-prefixed because it is not part of the TMDB shape the
         client renders -- it exists purely for server-side filtering. */
      _country: m.country || '',
      _genres: Array.isArray(m.genres) ? m.genres : [],
    })),
  };
}
/* ============================================================
   Keyless genre support (v12.13.1).

   /api/genres and the two /genre browse routes were raw TMDB calls with
   no backup, so without a key they 503'd and the genre filters on the
   Movies/TV pages were dead. Cinemeta exposes genre-filtered catalogues
   (?genre=Action), but keys them by NAME while the client speaks TMDB
   numeric ids -- so we keep a small id<->name bridge for the genres the
   two services share.
   ============================================================ */
const TMDB_GENRE_IDS = {
  movie: [
    [28, 'Action'], [12, 'Adventure'], [16, 'Animation'], [35, 'Comedy'],
    [80, 'Crime'], [99, 'Documentary'], [18, 'Drama'], [10751, 'Family'],
    [14, 'Fantasy'], [36, 'History'], [27, 'Horror'], [9648, 'Mystery'],
    [10749, 'Romance'], [878, 'Sci-Fi'], [53, 'Thriller'], [10752, 'War'],
    [37, 'Western'],
  ],
  tv: [
    [10759, 'Action'], [16, 'Animation'], [35, 'Comedy'], [80, 'Crime'],
    [99, 'Documentary'], [18, 'Drama'], [10751, 'Family'], [9648, 'Mystery'],
    [10764, 'Reality-TV'], [10765, 'Sci-Fi'], [37, 'Western'], [10767, 'Talk-Show'],
    [10763, 'Documentary'], [10762, 'Family'],
  ],
};
function genreNameFor(media, id) {
  const row = (TMDB_GENRE_IDS[media === 'tv' ? 'tv' : 'movie'] || []).find((g) => g[0] === Number(id));
  return row ? row[1] : '';
}
function cinemetaGenres(media) {
  const seen = new Set();
  const genres = [];
  for (const [id, name] of TMDB_GENRE_IDS[media === 'tv' ? 'tv' : 'movie'] || []) {
    if (seen.has(name)) continue;
    seen.add(name);
    genres.push({ id, name });
  }
  return { genres };
}
function cinemetaMeta(kind, id) {
  return cached(`cinmeta:${kind}:${id}`, 60 * 60 * 1000, () =>
    jfetch(`${CINEMETA}/meta/${kind}/${id}.json`).then((d) => (d && d.meta) || null), true);
}
/* Keyless deploys only ever hold IMDB ids, but every direct-stream provider
   (videasy, vidrock, ...) is keyed by a numeric TMDB id. Cinemeta's meta
   record carries moviedb_id, so it doubles as a free imdb -> tmdb bridge. */
async function tmdbIdFromImdb(imdbId, media) {
  const kind = media === 'tv' ? 'series' : 'movie';
  const tryKinds = kind === 'series' ? ['series', 'movie'] : ['movie', 'series'];
  for (const k of tryKinds) {
    try {
      const meta = await cinemetaMeta(k, imdbId);
      const n = parseInt(meta && meta.moviedb_id, 10);
      if (n > 0) return n;
    } catch (e) { /* try the other catalogue */ }
  }
  return 0;
}
/* Cinemeta ships every episode of a series in meta.videos; reshape the
   requested season into the TMDB /tv/{id}/season/{n} envelope the client
   already renders. */
async function cinemetaSeason(id, season) {
  const meta = await cinemetaMeta('series', id);
  const videos = (meta && meta.videos) || [];
  const episodes = videos
    .filter((v) => Number(v.season) === Number(season))
    .sort((a, b) => Number(a.number) - Number(b.number))
    .map((v) => ({
      id: `${id}:${v.season}:${v.number}`,
      episode_number: Number(v.number),
      season_number: Number(v.season),
      name: v.name || `Episode ${v.number}`,
      overview: v.overview || '',
      still_path: v.thumbnail || '',
      air_date: v.firstAired ? String(v.firstAired).slice(0, 10) : '',
      vote_average: Number(v.rating) || 0,
    }));
  return {
    id, name: `Season ${season}`, season_number: Number(season),
    overview: '', poster_path: (meta && meta.poster) || '',
    episodes, _backup: true,
  };
}
/* Genre-matched fallback recommendations: Cinemeta has no "similar to"
   endpoint, so pull the title's own genres and return that catalogue
   minus the title itself. */
async function cinemetaRecommendations(media, id) {
  const kind = media === 'tv' ? 'series' : 'movie';
  const meta = await cinemetaMeta(kind, id);
  const genres = (meta && (meta.genres || meta.genre)) || [];
  const picked = Array.isArray(genres) ? genres.slice(0, 2) : [];
  // cinemetaGenreList returns a TMDB-shaped envelope ({results:[...]}),
  // not a bare array.
  const lists = await Promise.all(picked.map((g) =>
    cinemetaGenreList(kind, g, 0).then((d) => (d && d.results) || []).catch(() => [])));
  const seen = new Set([String(id)]);
  const results = [];
  for (const list of lists) {
    for (const item of list || []) {
      if (!item || seen.has(String(item.id))) continue;
      seen.add(String(item.id));
      results.push({ ...item, media_type: media, recommendation_reason: 'Similar story and genres' });
    }
  }
  // Some Cinemeta entries carry no genres at all. "Recommendations must
  // show" is a standing requirement, so fall back to the plain top
  // catalogue rather than rendering an empty rail.
  if (!results.length) {
    const top = await cinemetaGenreList(kind, '', 0).then((d) => (d && d.results) || []).catch(() => []);
    for (const item of top) {
      if (!item || seen.has(String(item.id))) continue;
      seen.add(String(item.id));
      results.push({ ...item, media_type: media, recommendation_reason: 'Popular right now' });
    }
  }
  return { results: results.slice(0, 30), based_on: { genres: picked }, _backup: true };
}

function cinemetaGenreList(kind, genreName, skip) {
  const q = [];
  if (genreName) q.push('genre=' + encodeURIComponent(genreName));
  if (skip) q.push('skip=' + skip);
  const p = `/catalog/${kind}/top${q.length ? '/' + q.join('&') : ''}.json`;
  return cached('cin:' + p, 20 * 60 * 1000, () =>
    jfetch(CINEMETA + p).then((d) => {
      apiHealth.cinemeta = 'ok';
      return cinemetaToTmdbList(d.metas, kind === 'series' ? 'tv' : 'movie');
    }).catch((e) => { apiHealth.cinemeta = 'error'; throw e; }), true);
}

/* `skip` is what makes Load More work on the keyless path.
   Without it every "page" re-requested /catalog/<kind>/top.json and the
   grid appended the SAME 50 titles again -- the "load more loads the same
   thing twice" bug. Cinemeta pages in blocks of 100 via skip=<n>. */
function cinemetaList(kind, search, skip = 0) {
  const n = Math.max(0, Math.min(9900, Math.trunc(Number(skip) || 0)));
  const base = `/catalog/${kind}/top`;
  const p = search
    ? `${base}/search=${encodeURIComponent(search)}.json`
    : (n > 0 ? `${base}/skip=${n}.json` : `${base}.json`);
  return cached('cin:' + p, 20 * 60 * 1000, () =>
    jfetch(CINEMETA + p).then((d) => {
      apiHealth.cinemeta = 'ok';
      return cinemetaToTmdbList(d.metas, kind === 'series' ? 'tv' : 'movie');
    }).catch((e) => { apiHealth.cinemeta = 'error'; throw e; }), true);
}

/* Cinemeta returns 50 items per skip-block of 100, while the UI asks for
   TMDB-style pages. Map page -> skip and report a sane total_pages so the
   Load More button hides at the end instead of paging into thin air. */
function cinemetaPaged(kind, q, search) {
  const page = Math.max(1, Number(pageOf(q)) || 1);
  return cinemetaList(kind, search, (page - 1) * 100).then((d) => ({
    ...d, page, total_pages: (d.results || []).length ? Math.max(page + 1, 2) : page,
  }));
}

/* Origin-filtered series for the Drama tab on the keyless path.
   Cinemeta cannot filter by country server-side, so we pull several
   skip-blocks in parallel and filter locally. Cached for an hour: this is
   the expensive one, and the top-series catalogue barely moves. */
const DRAMA_COUNTRIES = {
  ko: ['South Korea', 'Korea'],
  ja: ['Japan'],
  zh: ['China', 'Taiwan', 'Hong Kong'],
  th: ['Thailand'],
  hi: ['India'],
};
const DRAMA_ALL = [...new Set(Object.values(DRAMA_COUNTRIES).flat())];

/* Cinemeta's whole top-series catalogue is only ~3,000 titles, so instead of
   paging blindly we sweep it ONCE, filter it, and page the filtered result.
   That is what makes the Drama chips honest: Korea genuinely has 166 titles
   and Thailand 12, and the UI can now show exactly that instead of whatever
   happened to land in the first few blocks. The sweep is 60 small parallel
   requests behind a 6-hour cache, shared by every origin and every page. */
const DRAMA_SWEEP_BLOCKS = 60;

function cinemetaDramaSweep() {
  return cached('cin:drama:sweep', 6 * 60 * 60 * 1000, async () => {
    const blocks = Array.from({ length: DRAMA_SWEEP_BLOCKS }, (_, i) => i * 100);
    // Fetch in waves so we never open 60 sockets at once, which is what an
    // unbounded Promise.all would do to a free-tier dyno on a cold cache.
    const out = [];
    const WAVE = 12;
    for (let i = 0; i < blocks.length; i += WAVE) {
      const wave = await Promise.all(blocks.slice(i, i + WAVE).map((skip) =>
        cinemetaList('series', '', skip).then((d) => d.results || []).catch(() => [])));
      for (const list of wave) out.push(...list);
    }
    return out;
  }, true);
}

function cinemetaDrama(origin, page = 1) {
  const wanted = DRAMA_COUNTRIES[origin] || DRAMA_ALL;
  const key = `cin:drama:${origin || 'all'}:${page}`;
  return cached(key, 60 * 60 * 1000, async () => {
    const all = await cinemetaDramaSweep();
    const seen = new Set();
    const matched = [];
    for (const item of all) {
      /* Match on the PRIMARY country only. Cinemeta lists co-productions as
         "United States, South Korea", and a plain substring test let X-Men '97
         and Avatar: The Last Airbender into the K-drama row purely because
         they were animated in Korea. */
      const primary = String(item._country || '').split(',')[0].trim();
      if (!primary) continue;
      if (!wanted.some((w) => primary === w || primary.includes(w))) continue;
      // Anime has its own tab; it should not fill the drama grid. This alone
      // removes 262 Japanese titles, which is why the Japan chip is small.
      if ((item._genres || []).includes('Animation')) continue;
      if (seen.has(item.id)) continue;
      seen.add(item.id);
      matched.push(item);
    }
    const per = 40;
    const startAt = (page - 1) * per;
    const slice = matched.slice(startAt, startAt + per);
    return {
      results: slice,
      page,
      total_results: matched.length,
      total_pages: Math.max(1, Math.ceil(matched.length / per)),
    };
  }, true);
}

/* ---------------- AniList backup ---------------- */
async function anilist(query, variables = {}) {
  return cached('al:' + query + JSON.stringify(variables), 15 * 60 * 1000, async () => {
    // AniList is disabled upstream (HTTP 403) for long stretches. Without the
    // breaker every anime request spent ~12s retrying it before reaching the
    // Jikan backup, which is what made the anime tab feel "dead".
    return viaBreaker('anilist', async () => {
      const data = await anilistLimit(() => jfetch(ANILIST, {
        method: 'POST', body: JSON.stringify({ query, variables }),
        headers: { 'Content-Type': 'application/json' },
        timeout: 7000, retries: 0,
      }));
      if (data.errors && data.errors.length) throw new Error('AniList: ' + data.errors[0].message);
      apiHealth.anilist = 'ok';
      return data.data;
    });
  }, false);
}
function alMediaToJikan(m) {
  if (!m) return {};
  return {
    // Keep both identifiers. A few new AniList entries do not have a MAL id;
    // treating an AniList id as a MAL id was the main cause of anime 404s.
    mal_id: m.idMal || null,
    anilist_id: m.id || null,
    anime_source: m.idMal ? 'mal' : 'anilist',
    title: (m.title && (m.title.english || m.title.romaji)) || '',
    title_english: (m.title && (m.title.english || m.title.romaji)) || '',
    title_japanese: m.title && m.title.native,
    images: { jpg: { image_url: m.coverImage && m.coverImage.large, large_image_url: (m.coverImage && (m.coverImage.extraLarge || m.coverImage.large)) || '' } },
    score: m.averageScore ? Number(m.averageScore / 10).toFixed(1) : null,
    year: m.seasonYear || (m.startDate && m.startDate.year) || null,
    type: m.format === 'MOVIE' ? 'Movie' : 'TV',
    status: m.status === 'RELEASING' ? 'Currently Airing' : m.status === 'FINISHED' ? 'Finished Airing' : (m.status || ''),
    // Currently-airing shows report `episodes: null` on AniList. Derive a
    // usable count so the episode picker is not collapsed to a single item.
    episodes: m.episodes
      || (m.nextAiringEpisode && m.nextAiringEpisode.episode ? Math.max(1, m.nextAiringEpisode.episode - 1) : null)
      || ((m.streamingEpisodes || []).length || null),
    synopsis: m.description || '',
    genres: (m.genres || []).map((g) => ({ name: g })),
    trailer: null,
    streamingEpisodes: (m.streamingEpisodes || []).filter((e) => e && e.url).slice(0, 40).map((e) => ({
      title: e.title || 'Official episode', thumbnail: e.thumbnail || '', url: e.url, site: e.site || 'Official',
    })),
    banner_image: m.bannerImage || '',
    url: m.siteUrl || (m.idMal ? 'https://myanimelist.net/anime/' + m.idMal : ''),
    aired: { from: m.startDate && m.startDate.year ? String(m.startDate.year) : null },
  };
}
const ANIME_GENRES_FALLBACK = [
  { mal_id: 1, name: 'Action' }, { mal_id: 2, name: 'Adventure' }, { mal_id: 4, name: 'Comedy' },
  { mal_id: 8, name: 'Drama' }, { mal_id: 10, name: 'Fantasy' }, { mal_id: 14, name: 'Horror' },
  { mal_id: 7, name: 'Mystery' }, { mal_id: 22, name: 'Romance' }, { mal_id: 24, name: 'Sci-Fi' },
  { mal_id: 36, name: 'Slice of Life' }, { mal_id: 30, name: 'Sports' }, { mal_id: 37, name: 'Supernatural' },
  { mal_id: 62, name: 'Isekai' },
];
/* AniList exposes only 19 genres (GenreCollection), while the chip labels come
   from MAL/Jikan which has 45. Querying AniList with a name it does not know
   silently returns an empty list, so we check membership up front and let the
   Jikan backup handle everything else. */
/* MAL genre id -> label, so /api/anime/genre works with only ?g=N. */
const MAL_GENRE_NAME_BY_ID = {
  1: 'Action',
  2: 'Adventure',
  5: 'Avant Garde',
  46: 'Award Winning',
  28: 'Boys Love',
  4: 'Comedy',
  8: 'Drama',
  10: 'Fantasy',
  26: 'Girls Love',
  47: 'Gourmet',
  14: 'Horror',
  7: 'Mystery',
  22: 'Romance',
  24: 'Sci-Fi',
  36: 'Slice of Life',
  30: 'Sports',
  37: 'Supernatural',
  41: 'Suspense',
  9: 'Ecchi',
  49: 'Erotica',
  12: 'Hentai',
  39: 'Detective',
  35: 'Harem',
  13: 'Historical',
  62: 'Isekai',
  17: 'Martial Arts',
  18: 'Mecha',
  38: 'Military',
  19: 'Music',
  6: 'Mythology',
  20: 'Parody',
  40: 'Psychological',
  3: 'Racing',
  21: 'Samurai',
  23: 'School',
  29: 'Space',
  11: 'Strategy Game',
  31: 'Super Power',
  32: 'Vampire',
  48: 'Workplace',
  43: 'Josei',
  15: 'Kids',
  42: 'Seinen',
  25: 'Shoujo',
  27: 'Shounen',
};

const ANIME_ADULT_GENRES = new Set(['Hentai', 'Erotica', 'Ecchi']);
const AL_GENRES = new Set(['Action','Adventure','Comedy','Drama','Ecchi','Fantasy','Hentai','Horror',
  'Mahou Shoujo','Mecha','Music','Mystery','Psychological','Romance','Sci-Fi','Slice of Life',
  'Sports','Supernatural','Thriller']);
/* MAL label -> AniList label, where the same genre is simply spelled differently. */
const AL_GENRE_ALIAS = {
  'Sci Fi': 'Sci-Fi', 'Science Fiction': 'Sci-Fi',
  'Slice Of Life': 'Slice of Life',
  'Magical Girl': 'Mahou Shoujo', 'Mahou Shoujo': 'Mahou Shoujo',
  'Suspense': 'Thriller',
};
/* Jikan's own /anime?genres=N endpoint is currently answering 504 for every
   genre, and AniList has no genre for most MAL labels - which left ~10 chips
   rendering an empty grid. AniList *tags* do cover them, so they become the
   middle tier: genre -> tag -> Jikan. */
const AL_GENRE_TAG = {
  'Historical': 'Historical', 'Detective': 'Detective', 'Gourmet': 'Food',
  'Boys Love': "Boys' Love", 'Girls Love': 'Yuri',
  'Avant Garde': 'Surreal Comedy', 'Award Winning': 'Achronological Order',
  'Harem': 'Heterosexual', 'Reverse Harem': 'Reverse Harem',
  'Iyashikei': 'Iyashikei', 'Educational': 'Educational', 'Isekai': 'Isekai',
  'School': 'School', 'Military': 'Military', 'Space': 'Space',
  'Vampire': 'Vampire', 'Samurai': 'Samurai', 'Super Power': 'Super Power',
  'Martial Arts': 'Martial Arts', 'Parody': 'Parody', 'Josei': 'Josei',
  'Seinen': 'Seinen', 'Shoujo': 'Shoujo', 'Shounen': 'Shounen', 'Kids': 'Kids',
  'Racing': 'Cars', 'Team Sports': 'Team Sports', 'Strategy Game': 'Strategy Game',
  'Video Game': 'Video Games', 'Idols (Female)': 'Idol', 'Idols (Male)': 'Idol',
  'Mythology': 'Mythology', 'Workplace': 'Work', 'Adult Cast': 'Primarily Adult Cast',
  'Childcare': 'Kids', 'Combat Sports': 'Combat Sports', 'Crossdressing': 'Crossdressing',
  'Delinquents': 'Delinquents', 'Gag Humor': 'Surreal Comedy', 'Gore': 'Gore',
  'High Stakes Game': 'Death Game', 'Love Polygon': 'Love Triangle',
  'Music': 'Music', 'Otaku Culture': 'Otaku Culture', 'Performing Arts': 'Acting',
  'Pets': 'Animals', 'Psychological': 'Psychological', 'Reincarnation': 'Reincarnation',
  'Romantic Subtext': 'Female Harem', 'Showbiz': 'Show Business', 'Survival': 'Survival',
  'Time Travel': 'Time Manipulation', 'Visual Arts': 'Art', 'Anthropomorphic': 'Anthropomorphism',
  'CGDCT': 'Cute Girls Doing Cute Things', 'Mecha': 'Mecha',
};
const AL_TAG_LIST = `query ($page: Int, $tag: String, $sort: [MediaSort]) {
  Page(page: $page, perPage: 20) {
    media(type: ANIME, tag: $tag, sort: $sort, isAdult: false) {
      id idMal title { romaji english native } coverImage { extraLarge large }
      averageScore seasonYear startDate { year } episodes status format genres
      streamingEpisodes { title thumbnail url site } siteUrl
    }
  }
}`;

const AL_LIST = `query ($page: Int, $sort: [MediaSort], $status: MediaStatus, $search: String, $genre: String) {
  Page(page: $page, perPage: 20) {
    media(type: ANIME, sort: $sort, status: $status, search: $search, genre: $genre, isAdult: false) {
      id idMal title { romaji english native } coverImage { extraLarge large }
      averageScore seasonYear startDate { year } episodes status format genres
      streamingEpisodes { title thumbnail url site } siteUrl
    }
  }
}`;
const AL_DETAIL = `query ($id: Int, $idMal: Int) {
  Media(id: $id, idMal: $idMal, type: ANIME) {
    id idMal title { romaji english native } coverImage { extraLarge large } bannerImage
    description averageScore seasonYear startDate { year } episodes status format genres
    nextAiringEpisode { episode } streamingEpisodes { title thumbnail url site } siteUrl
  }
}`;
const AL_VIDEO = `query ($id: Int, $idMal: Int) {
  Media(id: $id, idMal: $idMal, type: ANIME) {
    id idMal title { romaji english native } coverImage { extraLarge large } bannerImage
    streamingEpisodes { title thumbnail url site } siteUrl
  }
}`;
const AL_RECOMMENDATIONS = `query ($id: Int, $idMal: Int) {
  Media(id: $id, idMal: $idMal, type: ANIME) {
    recommendations(page: 1, perPage: 24, sort: [RATING_DESC]) {
      nodes {
        rating
        mediaRecommendation {
          id idMal title { romaji english native } coverImage { extraLarge large }
          averageScore seasonYear startDate { year } episodes status format genres siteUrl
        }
      }
    }
  }
}`;

function animeVars(id, source) {
  const n = Number(id);
  if (!Number.isSafeInteger(n) || n <= 0) throw httpError(400, 'invalid anime id');
  return source === 'anilist' ? { id: n } : { idMal: n };
}

function animeTitle(m) {
  return (m && m.title && (m.title.english || m.title.romaji || m.title.native)) || 'Anime';
}

function secureExternalUrl(value) {
  try {
    const u = new URL(String(value));
    if (u.protocol === 'http:') u.protocol = 'https:';
    return /^https?:$/.test(u.protocol) ? u.toString() : '';
  } catch (e) { return ''; }
}

function normaliseAnimeVideos(m, id, source = 'mal', extra = {}) {
  const title = animeTitle(m);
  const episodes = (m && m.streamingEpisodes || []).filter((e) => e && e.url).slice(0, 40).map((e, i) => ({
    id: `${source}-${id}-${i + 1}`,
    title: e.title || `Official episode ${i + 1}`,
    thumbnail: e.thumbnail || '', url: secureExternalUrl(e.url), site: e.site || 'Official',
  })).filter((e) => e.url);
  const q = encodeURIComponent(title);
  const malId = (m && m.idMal) || (source === 'mal' ? Number(id) : null);
  const anilistId = (m && m.id) || (source === 'anilist' ? Number(id) : null);
  return {
    ok: Boolean(episodes.length), source: 'AniList', id: Number(id), id_type: source,
    mal_id: malId || null, anilist_id: anilistId || null, title,
    trailer: null, episodes,
    official: [
      { name: 'Crunchyroll', url: `https://www.crunchyroll.com/search?q=${q}` },
      { name: 'Netflix', url: `https://www.netflix.com/search?q=${q}` },
      ...(m && m.siteUrl ? [{ name: 'AniList', url: m.siteUrl }] : []),
      ...(malId ? [{ name: 'MyAnimeList', url: `https://myanimelist.net/anime/${malId}` }] : []),
    ],
    ...extra,
  };
}

async function animeVideosFromAniList(id, source) {
  const data = await anilist(AL_VIDEO, animeVars(id, source));
  const media = data && data.Media;
  if (!media) throw new Error('anime not found');
  return normaliseAnimeVideos(media, id, source);
}

async function animeVideosFromJikan(malId) {
  const result = await jikan(`/anime/${encodeURIComponent(malId)}/full`);
  const a = result && result.data;
  if (!a) throw new Error('anime not found');
  const title = a.title_english || a.title || 'Anime';
  return normaliseAnimeVideos({
    idMal:Number(malId),title:{romaji:title},siteUrl:a.url,streamingEpisodes:[],
  },malId,'mal',{source:'Jikan'});
}

async function animeVideos(id, source = 'mal') {
  return cached(`anime:videos:no-trailer:${source}:${id}`, 30 * 60 * 1000, async () => {
    try { return await animeVideosFromAniList(id, source); }
    catch (primaryError) {
      if (source === 'mal') {
        try { return await animeVideosFromJikan(id); } catch (backupError) { /* fall through */ }
      }
      return {
        ok:false,source:'unavailable',id:Number(id),id_type:source,
        mal_id:source==='mal'?Number(id):null,anilist_id:source==='anilist'?Number(id):null,
        title:'Anime',trailer:null,episodes:[],official:[],
      };
    }
  });
}

/* ---------------- Jikan ----------------
   Since AniList is 403 globally, Jikan is effectively the ONLY anime upstream,
   so it is treated as a precious shared resource:
     - every call goes through the process-wide rate limiter (shared egress IP)
     - 6h TTL instead of 15min (anime catalogues barely change)
     - a stale entry of ANY age beats showing "Could not load. Try again."   */
const JIKAN_TTL = 6 * 60 * 60 * 1000;
const jikanStale = new Map(); // key -> value, never expires, survives 429 storms
function jikan(p, ttl = JIKAN_TTL) {
  const url = 'https://api.jikan.moe/v4' + p;
  const key = 'jikan:' + p;
  return cached(key, ttl, async () => {
    try {
      const v = await jikanLimit(() => jfetch(url, { retries: 3 }));
      apiHealth.jikan = 'ok';
      jikanStale.set(key, v);
      while (jikanStale.size > 400) jikanStale.delete(jikanStale.keys().next().value);
      return v;
    } catch (e) {
      apiHealth.jikan = 'error';
      const stale = jikanStale.get(key);
      if (stale) {
        stats.backupsUsed.staleCache++;
        return stale && !Array.isArray(stale) && typeof stale === 'object'
          ? { ...stale, _stale: true } : stale;
      }
      throw e;
    }
  });
}

/* ---------------- Geo ---------------- */
function isPrivateIp(ip) {
  if (!ip) return true;
  let x = String(ip).replace(/^::ffff:/, '');
  if (x === '::1' || x === 'localhost') return true;
  return /^(127\.|10\.|192\.168\.|169\.254\.|0\.)/.test(x) || /^172\.(1[6-9]|2\d|3[01])\./.test(x);
}
function clientIp(req) {
  const xf = req.headers['x-forwarded-for'];
  if (xf) return String(xf).split(',')[0].trim();
  return req.socket.remoteAddress || '';
}
async function geoLookup(ip) {
  if (isPrivateIp(ip)) return { country_code: 'IN', country: 'India', flag: '🇮🇳', note: 'local default' };
  try {
    const d = await jfetch(`https://ipwho.is/${encodeURIComponent(ip)}`, { retries: 1, timeout: 8000 });
    if (d && d.success !== false && d.country_code) {
      apiHealth.geo = 'ok';
      return { country_code: d.country_code, country: d.country, flag: (d.flag && d.flag.emoji) || '', city: d.city };
    }
    throw new Error('no data');
  } catch (e) { /* backup */ }
  try {
    const d = await jfetch(`https://ipapi.co/${encodeURIComponent(ip)}/json/`, { retries: 1, timeout: 8000 });
    if (d && d.country_code) {
      stats.backupsUsed.ipapi++;
      apiHealth.geo = 'ok';
      return { country_code: d.country_code, country: d.country_name, flag: '', city: d.city, _backup: true };
    }
  } catch (e) { apiHealth.geo = 'error'; }
  return { country_code: 'IN', country: 'India', flag: '🇮🇳', fallback: true };
}

/* ---------------- TMDB countries ---------------- */
function tmdbCountries() {
  return cached('tmdb:countries', 7 * 24 * 60 * 60 * 1000, () =>
    tmdb('/configuration/countries', {}, 7 * 24 * 60 * 60 * 1000));
}

/* ---------------- anime → TMDB id mapping (for embeds) ---------------- */
async function animeToTmdb(malId) {
  return cached('a2t:' + malId, 30 * 24 * 60 * 60 * 1000, async () => {
    const j = await jikan(`/anime/${malId}/full`);
    const a = j.data || {};
    const title = a.title_english || a.title || '';
    const year = a.year ? String(a.year) : (a.aired && a.aired.from ? String(a.aired.from).slice(0, 4) : '');
    if (!title) throw new Error('no anime title');
    const r = await tmdb('/search/tv', { query: title, first_air_date_year: year, include_adult: 'false' }, 30 * 24 * 60 * 60 * 1000);
    const res = (r && r.results) || [];
    const best = res.find((x) => x.name && x.name.toLowerCase() === title.toLowerCase()) || res[0];
    if (!best) {
      // try movie search for anime films
      const rm = await tmdb('/search/movie', { query: title, year, include_adult: 'false' }, 30 * 24 * 60 * 60 * 1000);
      const m = (rm && rm.results && rm.results[0]) || null;
      if (!m) throw new Error('no tmdb match');
      return { tmdb_id: m.id, media: 'movie', title: m.title };
    }
    return { tmdb_id: best.id, media: 'tv', title: best.name };
  });
}

/* ---------------- fallback helper ---------------- */
/* Keyless deployments (the supported default) have no TMDB_KEY, so EVERY
   movie/TV route logs "primary failed" before falling to Cinemeta. On Render
   that is thousands of identical lines an hour and it buries real errors.
   The expected keyless path is logged once, then counted silently. */
let noKeyNoticeShown = false;
async function withBackup(primary, backup, backupName) {
  try { return await primary(); }
  catch (e) {
    const expectedKeyless = !TMDB_KEY && /TMDB_KEY is not configured/.test(e.message || '');
    if (expectedKeyless) {
      if (!noKeyNoticeShown) {
        noKeyNoticeShown = true;
        console.log('[keyless] no TMDB_KEY - serving movies/TV from ' + backupName + ' (this is normal; logged once)');
      }
    } else console.error('[primary failed] ' + e.message + ' → backup: ' + backupName);
    if (stats.backupsUsed[backupName] !== undefined) stats.backupsUsed[backupName]++;
    const data = await backup();
    if (data && typeof data === 'object') data._backup = true;
    return data;
  }
}
function httpError(status, msg) { const e = new Error(msg); e.status = status; return e; }

function positiveInt(value, name = 'id', max = 999999999) {
  const n = Number(value);
  if (!Number.isSafeInteger(n) || n <= 0 || n > max) throw httpError(400, `invalid ${name}`);
  return n;
}
function pageOf(q) { return String(Math.min(20, positiveInt(q.get('page') || 1, 'page', 500))); }
function mediaIdOf(value) {
  const id = String(value || '');
  if (!/^(?:\d{1,10}|tt\d{5,12})$/.test(id)) throw httpError(400, 'invalid media id');
  return id;
}
function queryOf(q, key = 'q', max = 100) {
  const value = String(q.get(key) || '').trim().replace(/[\u0000-\u001f]/g, '').slice(0, max);
  if (!value) throw httpError(400, `${key} required`);
  return value;
}
function regionOf(value) {
  const region = String(value || WATCH_REGION).toUpperCase();
  return /^[A-Z]{2}$/.test(region) ? region : 'IN';
}

/* ---------------- smart search intent parser ---------------- */
const SMART_GENRES = [
  { key: 'romantic-comedy', label: 'Romantic Comedy', aliases: ['romantic comedy', 'rom com', 'रोमांटिक कॉमेडी'], movie: '35,10749', tv: '35,10749', anime: 4 },
  { key: 'comedy', label: 'Comedy', aliases: ['comedy', 'comedies', 'funny', 'कॉमेडी', 'हास्य', 'mazedar', 'मजेदार'], movie: '35', tv: '35', anime: 4 },
  { key: 'action', label: 'Action', aliases: ['action', 'एक्शन', 'मारधाड़'], movie: '28', tv: '10759', anime: 1 },
  { key: 'romance', label: 'Romance', aliases: ['romance', 'romantic', 'love story', 'रोमांस', 'रोमांटिक', 'प्यार'], movie: '10749', tv: '10749', anime: 22 },
  { key: 'horror', label: 'Horror', aliases: ['horror', 'scary', 'ghost', 'हॉरर', 'डरावनी', 'भूत'], movie: '27', tv: '10765', tvKeywords: '6152|3358|162846', anime: 14 },
  { key: 'thriller', label: 'Thriller', aliases: ['thriller', 'suspense', 'थ्रिलर', 'सस्पेंस'], movie: '53', tv: '9648', anime: 41 },
  { key: 'animation', label: 'Animation', aliases: ['animation', 'animated', 'cartoon', 'कार्टून', 'एनिमेशन'], movie: '16', tv: '16', anime: 1 },
  { key: 'documentary', label: 'Documentary', aliases: ['documentary', 'docs', 'डॉक्यूमेंट्री'], movie: '99', tv: '99', anime: null },
  { key: 'crime', label: 'Crime', aliases: ['crime', 'gangster', 'क्राइम', 'अपराध'], movie: '80', tv: '80', anime: 7 },
  { key: 'family', label: 'Family', aliases: ['family', 'kids', 'परिवार', 'बच्चों'], movie: '10751', tv: '10751', anime: null },
  { key: 'fantasy', label: 'Fantasy', aliases: ['fantasy', 'magic', 'फैंटेसी', 'जादू'], movie: '14', tv: '10765', anime: 10 },
  { key: 'scifi', label: 'Sci-Fi', aliases: ['sci fi', 'sci-fi', 'science fiction', 'स्पेस', 'विज्ञान कथा'], movie: '878', tv: '10765', anime: 24 },
  { key: 'adventure', label: 'Adventure', aliases: ['adventure', 'एडवेंचर', 'रोमांच'], movie: '12', tv: '10759', anime: 2 },
  { key: 'mystery', label: 'Mystery', aliases: ['mystery', 'detective', 'मिस्ट्री', 'रहस्य'], movie: '9648', tv: '9648', anime: 7 },
  { key: 'drama', label: 'Drama', aliases: ['drama', 'ड्रामा', 'नाटक'], movie: '18', tv: '18', anime: 8 },
  { key: 'war', label: 'War', aliases: ['war movie', 'war', 'युद्ध'], movie: '10752', tv: '10768', anime: null },
  { key: 'music', label: 'Music', aliases: ['music', 'musical', 'संगीत', 'म्यूजिकल'], movie: '10402', tv: '10764', anime: 19 },
];
const SMART_LANGUAGES = [
  { code: 'hi', label: 'Hindi', aliases: ['hindi', 'bollywood', 'हिन्दी', 'हिंदी'] },
  { code: 'ta', label: 'Tamil', aliases: ['tamil', 'तमिल'] },
  { code: 'te', label: 'Telugu', aliases: ['telugu', 'तेलुगु'] },
  { code: 'ml', label: 'Malayalam', aliases: ['malayalam', 'मलयालम'] },
  { code: 'kn', label: 'Kannada', aliases: ['kannada', 'कन्नड़'] },
  { code: 'ko', label: 'Korean', aliases: ['korean', 'k drama', 'k-drama', 'कोरियन'] },
  { code: 'ja', label: 'Japanese', aliases: ['japanese', 'जापानी'] },
];

function normaliseIntentText(value) {
  return String(value || '').toLowerCase().normalize('NFKD')
    .replace(/[\p{M}]/gu, '')
    .replace(/[^\p{L}\p{N}]+/gu, ' ')
    .trim().replace(/\s+/g, ' ');
}
function hasAlias(text, alias) {
  const value = normaliseIntentText(alias);
  return (` ${text} `).includes(` ${value} `);
}
function parseSmartSearch(value) {
  const text = normaliseIntentText(value);
  const genre = SMART_GENRES.find((item) => item.aliases.some((alias) => hasAlias(text, alias))) || null;
  let language = SMART_LANGUAGES.find((item) => item.aliases.some((alias) => hasAlias(text, alias))) || null;
  if (!language && (hasAlias(text, 'south indian') || hasAlias(text, 'south movie') || hasAlias(text, 'साउथ'))) {
    language = { code: 'te|ta|ml|kn', label: 'South Indian' };
  }
  let media = 'all';
  if (['anime', 'ऐनिमे', 'एनीमे'].some((alias) => hasAlias(text, alias))) media = 'anime';
  else if (['movie', 'movies', 'film', 'films', 'फिल्म', 'फिल्में'].some((alias) => hasAlias(text, alias))) media = 'movie';
  else if (['tv', 'show', 'shows', 'series', 'सीरीज', 'शो'].some((alias) => hasAlias(text, alias))) media = 'tv';
  let sort = 'popularity.desc';
  if (['top rated', 'best', 'highest rated', 'टॉप', 'सबसे अच्छा'].some((alias) => hasAlias(text, alias))) sort = 'vote_average.desc';
  else if (['latest', 'new', 'recent', 'नया', 'नई', 'लेटेस्ट'].some((alias) => hasAlias(text, alias))) sort = 'date.desc';
  const yearMatch = text.match(/\b(19\d{2}|20\d{2})\b/);
  const smart = Boolean(genre || language || media !== 'all' || sort !== 'popularity.desc' || yearMatch);
  return {
    smart, genre, language, media, sort,
    year: yearMatch ? yearMatch[1] : '',
    label: [language && language.label, genre && genre.label, media === 'anime' ? 'Anime' : ''].filter(Boolean).join(' · ') || 'Smart results',
  };
}

/* ---------------- lightweight per-IP limits ---------------- */
const rateBuckets = new Map();
function rateLimit(req, kind) {
  const now = Date.now();
  const limits = kind === 'hls' ? { max: 360, ms: 60000 }
    : kind === 'ping' ? { max: 12, ms: 60000 }
      : { max: 120, ms: 60000 };
  const key = `${kind}:${clientIp(req) || 'unknown'}`;
  let bucket = rateBuckets.get(key);
  if (!bucket || now - bucket.start >= limits.ms) bucket = { start: now, count: 0 };
  bucket.count++;
  rateBuckets.set(key, bucket);
  if (bucket.count > limits.max) {
    stats.rateLimited++;
    return Math.max(1, Math.ceil((limits.ms - (now - bucket.start)) / 1000));
  }
  return 0;
}
setInterval(() => {
  const cutoff = Date.now() - 2 * 60 * 1000;
  for (const [key, value] of rateBuckets) if (value.start < cutoff) rateBuckets.delete(key);
}, 60000).unref?.();

/* MegaPlay: a second opinion when megavid has nothing for an episode.
   Its API is page-scrape shaped -- /stream/s-2/<malId>/<sub|dub> embeds a
   data-id, and /stream/getSources?id=<data-id> returns the manifest. Probed
   2026-08-24: it resolves episode 1 only, so it is a genuine last resort and
   never the primary provider. */
async function megaplayEpisode(malId, lang) {
  const base = 'https://megaplay.buzz';
  const referer = `${base}/stream/s-2/${malId}/${lang}/`;
  const headers = { 'User-Agent': UA, Accept: '*/*', Referer: referer };

  const page = await fetch(`${base}/stream/s-2/${malId}/${lang}`, {
    headers: { ...headers, Accept: 'text/html' },
    signal: AbortSignal.timeout(12000),
  });
  if (!page.ok) throw new Error(`megaplay page ${page.status}`);
  const html = await page.text();
  const m = html.match(/data-id="(\d+)"/);
  if (!m) throw new Error('megaplay: no data-id (title not carried)');

  const api = await fetch(`${base}/stream/getSources?id=${m[1]}`, {
    headers: { ...headers, 'X-Requested-With': 'XMLHttpRequest' },
    signal: AbortSignal.timeout(12000),
  });
  if (!api.ok) throw new Error(`megaplay getSources ${api.status}`);
  const body = await api.json();
  const file = body && body.sources && body.sources.file;
  if (!file) throw new Error('megaplay: no source file');

  return {
    ok: true,
    provider: 'megaplay.buzz',
    lang,
    episode: 1,
    source: '/api/hls?url=' + encodeURIComponent(String(file)),
    tracks: (Array.isArray(body.tracks) ? body.tracks : [])
      .filter((t) => t && t.file && String(t.kind || 'captions') !== 'thumbnails')
      .map((t) => ({
        file: '/api/hls?url=' + encodeURIComponent(String(t.file)),
        label: String(t.label || 'Subtitles'),
        kind: String(t.kind || 'captions'),
        default: !!t.default,
      })),
    intro: body.intro && body.intro.end ? body.intro : null,
    outro: body.outro && body.outro.end ? body.outro : null,
  };
}

/* ---------------- routes ---------------- */
/* Fallback anime source API, tried after AnimeWorld. Re-probed 2026-08-24:
   megavid.buzz answers /api/{mal|ani}/<id>/<ep>/<sub|dub> with a real 1080p
   master.m3u8 for every episode, so it stays. megaplay.buzz is kept as a
   last resort only: its working endpoint is a different shape
   (/stream/s-2/<mal>/sub -> data-id -> /stream/getSources?id=<data-id>) and
   it only ever resolves episode 1, which is why it is not the primary. */
const ANIME_STREAM_HOSTS = ['megavid.buzz'];

/* ============================================================
   AnimeWorld India (multi-audio provider)

   Why this exists: the megavid path only ever exposes sub/dub and a
   single video rendition. AnimeWorld serves one HLS master that carries
   up to 7 audio languages (Hindi, Tamil, Telugu, Bengali, Malayalam,
   English, Japanese) AND 240p-1080p renditions, so language and quality
   both become real, instant, in-place switches.

   FUTURE-PROOFING: this is a scraper, so every brittle value below is
   overridable with an env var and every extraction step falls back
   through a list of patterns. If the site moves domain or swaps player
   again (it already went .net -> .top and zephyrflick -> zephyrix), you
   change an env var on Render instead of editing code.
   ============================================================ */
const AW_SITES = String(process.env.ANIMEWORLD_HOSTS
  // .one is the live domain since Aug 2026; .top/.net 301 to it, and we
  // follow redirects, so the old names keep working as aliases.
  || 'watchanimeworld.one,watchanimeworld.top,watchanimeworld.net,watchanimeworld.in')
  .split(',').map((v) => v.trim().toLowerCase()).filter(Boolean);

// Player hosts we know how to talk to. Same PHP contract for each.
const AW_PLAYER_HOSTS = String(process.env.ANIMEWORLD_PLAYER_HOSTS
  || 'play.zephyrix.org,play.zephyrix.top,play.zephyrflick.top')
  .split(',').map((v) => v.trim().toLowerCase()).filter(Boolean);

/* SELF-HEALING PLAYER HOSTS.
   This provider has now rotated its player domain three times
   (zephyrflick.top -> zephyrix.top -> zephyrix.org). Every rotation
   silently killed Hindi anime, because the old host answers Cloudflare
   403 and the hard-coded default never learned the new one.

   Fix: treat AW_PLAYER_HOSTS as a *hint*, not the truth. Whenever an
   episode page hands us an embed on some other host, we record it here,
   promote it to the front of the try-order and trust it in the HLS proxy
   for a day. The next rotation therefore heals itself on the first play
   instead of waiting for a code change. Nothing is trusted that did not
   arrive inside a page served by an AnimeWorld site we already trust. */
const AW_LEARNED_HOSTS = new Map(); // host -> expires
const AW_LEARNED_TTL = 24 * 60 * 60 * 1000;
const AW_LEARNED_MAX = 12;

function awLearnPlayerHost(host) {
  const h = String(host || '').toLowerCase().replace(/\.$/, '');
  // Only accept things that look like a player domain, never an IP or a
  // bare TLD, and never a host that is already known.
  if (!/^[a-z0-9][a-z0-9.-]*\.[a-z]{2,}$/.test(h) || net.isIP(h)) return;
  if (AW_PLAYER_HOSTS.includes(h)) return;
  if (AW_LEARNED_HOSTS.size >= AW_LEARNED_MAX) {
    const oldest = AW_LEARNED_HOSTS.keys().next().value;
    if (oldest) AW_LEARNED_HOSTS.delete(oldest);
  }
  const fresh = !AW_LEARNED_HOSTS.has(h);
  AW_LEARNED_HOSTS.set(h, Date.now() + AW_LEARNED_TTL);
  if (fresh) console.log(`AnimeWorld: learned new player host ${h}`);
}

function awLearnedHosts() {
  const now = Date.now();
  const live = [];
  for (const [host, expires] of AW_LEARNED_HOSTS) {
    if (expires < now) AW_LEARNED_HOSTS.delete(host);
    else live.push(host);
  }
  return live;
}

// Learned hosts first: if the site has moved, the old default is dead
// weight and we should not spend a 403 round-trip on it every play.
function awPlayerHosts() {
  return [...awLearnedHosts(), ...AW_PLAYER_HOSTS];
}

const AW_LANG_NAMES = {
  hin: 'Hindi', tam: 'Tamil', tel: 'Telugu', ben: 'Bengali',
  mal: 'Malayalam', eng: 'English', jpn: 'Japanese', kan: 'Kannada',
  mar: 'Marathi', urd: 'Urdu',
};

function awHeaders(referer) {
  return {
    'User-Agent': UA,
    Accept: 'text/html,application/xhtml+xml,application/json,*/*',
    'Accept-Language': 'en-US,en;q=0.9,hi;q=0.8',
    ...(referer ? { Referer: referer } : {}),
  };
}

/* SELF-HEALING SITE DOMAIN.
   The catalogue site rotates too: watchanimeworld .net -> .top -> .one,
   each old name 301'ing to the new one. We follow redirects anyway, so
   the move is survivable -- but only if we notice where we landed and
   start going there directly. Otherwise every single request pays an
   extra redirect hop, and the day the old domain finally expires the
   whole Hindi path dies again. So: read res.url, and if the response
   came from a different watchanimeworld host, promote it. */
function awLearnSiteHost(finalUrl) {
  let host = '';
  try { host = new URL(String(finalUrl)).hostname.toLowerCase(); } catch { return; }
  if (!/^([a-z0-9-]+\.)*watchanimeworld\.[a-z]{2,6}$/.test(host)) return;
  if (AW_SITES[0] === host) return;
  const idx = AW_SITES.indexOf(host);
  if (idx > 0) AW_SITES.splice(idx, 1);
  AW_SITES.unshift(host);
  if (AW_SITES.length > 8) AW_SITES.length = 8;
  console.log(`AnimeWorld: site domain is now ${host}`);
}

async function awFetchText(url, referer, timeoutMs = 15000, init = {}) {
  const ctrl = new AbortController();
  const timer = setTimeout(() => ctrl.abort(), timeoutMs);
  try {
    const res = await fetch(url, { signal: ctrl.signal, redirect: 'follow', headers: awHeaders(referer), ...init });
    if (res.url && res.url !== url) awLearnSiteHost(res.url);
    if (!res.ok) return null;
    return await res.text();
  } catch { return null; } finally { clearTimeout(timer); }
}

/* Resolve a human title to the site's series slug. Cached for a day: slugs
   effectively never change, and this is the slowest step. */
async function awResolveSlug(title) {
  const clean = String(title || '').trim();
  if (!clean) return null;
  return cached(`aw:slug:${clean.toLowerCase()}`, 24 * 60 * 60 * 1000, async () => {
    // A direct slug guess is right most of the time and costs one request.
    const guess = clean.toLowerCase()
      .replace(/[’'`]/g, '').replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '');
    for (const site of AW_SITES) {
      const html = await awFetchText(`https://${site}/series/${guess}/`, `https://${site}/`, 12000);
      if (html && /play\.zephyr|\/episode\//i.test(html)) return { slug: guess, site };
    }
    // Otherwise fall back to the site search and take the first series hit.
    for (const site of AW_SITES) {
      const html = await awFetchText(`https://${site}/?s=${encodeURIComponent(clean)}`, `https://${site}/`, 15000);
      if (!html) continue;
      const found = [...html.matchAll(/\/series\/([a-z0-9-]+)\/?"/gi)].map((m) => m[1]);
      if (found.length) return { slug: found[0], site };
    }
    return null;
  }, true);
}

/* Pull the player embed id out of an episode page. */
function awExtractPlayer(html) {
  if (!html) return null;
  /* Prefer whatever the page ACTUALLY embeds over what we think we know.
     The old order (known hosts first) is what made the .top -> .org move
     invisible: the page already pointed at the working host, but we kept
     matching the dead one. Read the page, then learn from it. */
  const embeds = [...html.matchAll(/https?:\/\/([a-z0-9][a-z0-9.-]*\.[a-z]{2,})\/video\/([a-f0-9]{16,})/gi)]
    .map((m) => ({ host: m[1].toLowerCase(), id: m[2] }));
  if (embeds.length) {
    const known = embeds.find((e) => awPlayerHosts().includes(e.host));
    const chosen = known || embeds[0];
    if (!known) awLearnPlayerHost(chosen.host);
    return chosen;
  }
  // No absolute embed URL: fall back to a host-qualified match in case the
  // page writes the id and host separately (some themes do).
  for (const host of awPlayerHosts()) {
    const re = new RegExp(host.replace(/\./g, '\\.') + '[^"\'\\s]*?/video/([a-f0-9]{16,})', 'i');
    const hit = html.match(re);
    if (hit) return { host, id: hit[1] };
  }
  return null;
}

/* Ask the player PHP endpoint for the signed master.m3u8. */
async function awGetVideoSource(playerHost, videoId) {
  const referer = `https://${playerHost}/video/${videoId}`;
  const api = `https://${playerHost}/player/index.php?data=${encodeURIComponent(videoId)}&do=getVideo`;
  const ctrl = new AbortController();
  const timer = setTimeout(() => ctrl.abort(), 15000);
  try {
    const res = await fetch(api, {
      method: 'POST', signal: ctrl.signal,
      headers: { ...awHeaders(referer), 'X-Requested-With': 'XMLHttpRequest' },
    });
    if (!res.ok) return null;
    const body = await res.json().catch(() => null);
    const src = body && (body.videoSource || body.securedLink);
    return typeof src === 'string' && src.includes('.m3u8') ? src : null;
  } catch { return null; } finally { clearTimeout(timer); }
}

/* Read the master playlist so the UI can show the REAL languages and
   qualities instead of guessing. */
function awParseMaster(text) {
  const audio = [];
  const qualities = [];
  if (!text) return { audio, qualities };
  for (const line of text.split('\n')) {
    if (line.startsWith('#EXT-X-MEDIA:TYPE=AUDIO')) {
      const lang = (line.match(/LANGUAGE="([^"]+)"/) || [])[1] || '';
      const name = (line.match(/NAME="([^"]+)"/) || [])[1] || '';
      const code = lang.toLowerCase();
      if (!audio.some((a) => a.code === code && a.label === name)) {
        audio.push({ code, label: AW_LANG_NAMES[code] || name || code || 'Audio', name });
      }
    } else if (line.startsWith('#EXT-X-STREAM-INF')) {
      const res = (line.match(/RESOLUTION=\d+x(\d+)/) || [])[1];
      const bw = Number((line.match(/BANDWIDTH=(\d+)/) || [])[1] || 0);
      if (res) qualities.push({ height: Number(res), bandwidth: bw });
    }
  }
  qualities.sort((a, b) => b.height - a.height);
  return { audio, qualities };
}

/* Full pipeline: title + season/episode -> proxied master URL + track lists. */
// Read the season/episode pairs the series page actually links to. Guessing
// the URL works most of the time, but some shows start at 1x9 or use their own
// season numbering, so the real list is what we trust first.
function awCollectEpisodeLinks(html, slug, into) {
  const re = new RegExp('/episode/' + slug.replace(/[^a-z0-9-]/gi, '.') + '-(\\d{1,3})x(\\d{1,4})/', 'g');
  let m;
  while ((m = re.exec(html || ''))) {
    const s = Number(m[1]); const e = Number(m[2]);
    if (Number.isFinite(s) && Number.isFinite(e)) into.set(`${s}x${e}`, { season: s, episode: e });
  }
  return into;
}

async function awListEpisodes(site, slug) {
  return cached(`aw:eps:${site}:${slug}`, 6 * 60 * 60 * 1000, async () => {
    const seriesUrl = `https://${site}/series/${slug}/`;
    const html = await awFetchText(seriesUrl, `https://${site}/`, 15000);
    if (!html) return [];
    const found = awCollectEpisodeLinks(html, slug, new Map());

    // The series page only renders one season inline; the rest load over
    // admin-ajax (torofilm theme, action_select_season). Pull them so long
    // runs like One Piece resolve past episode 61.
    const postId = (html.match(/data-post="(\d+)"/) || [])[1];
    const seasons = [...new Set([...html.matchAll(/data-season="(\d{1,3})"/g)].map((m2) => Number(m2[1])))]
      .filter((n) => Number.isFinite(n) && n > 0)
      .slice(0, 40);
    if (postId && seasons.length) {
      const results = await Promise.allSettled(seasons.map((season) => awFetchText(
        `https://${site}/wp-admin/admin-ajax.php?action=action_select_season&season=${season}&post=${postId}`,
        seriesUrl, 12000,
      )));
      results.forEach((r) => {
        if (r.status === 'fulfilled' && r.value) awCollectEpisodeLinks(r.value, slug, found);
      });
    }
    return [...found.values()].sort((a, b) => (a.season - b.season) || (a.episode - b.episode));
  }, true).catch(() => []);
}

async function awResolveEpisode(title, season, ep) {
  const resolved = await awResolveSlug(title);
  if (!resolved) return { ok: false, error: 'title not found on AnimeWorld' };
  const { slug, site } = resolved;

  // Their episode URLs are slug-{season}x{episode} with no zero padding.
  // Order of attempts: the season the page really lists for this episode
  // number, then the requested season, then season 1.
  const listed = await awListEpisodes(site, slug);
  const fromList = listed.filter((item) => item.episode === Number(ep)).map((item) => item.season);
  const seasons = [...new Set([...fromList, Number(season) || 1, 1])];
  for (const s of seasons) {
    const pageUrl = `https://${site}/episode/${slug}-${s}x${ep}/`;
    const html = await awFetchText(pageUrl, `https://${site}/series/${slug}/`, 15000);
    if (!html) continue;
    const player = awExtractPlayer(html);
    if (!player) continue;
    const source = await awGetVideoSource(player.host, player.id);
    if (!source) continue;

    const master = await awFetchText(source, `https://${player.host}/`, 15000);
    const { audio, qualities } = awParseMaster(master);
    // A master with no alternate audio is no better than megavid, so let the
    // caller fall back rather than switching provider for nothing.
    if (!audio.length) continue;

    return {
      ok: true,
      provider: 'animeworld',
      site, slug, season: s, episode: ep,
      source: `/api/hls?url=${encodeURIComponent(source)}`,
      // Raw master, needed by /api/hls/remix when the user wants this
      // provider's audio grafted onto another provider's video. It is a
      // short-lived signed URL, so it is only ever used immediately.
      master: source,
      audio, qualities,
      multiAudio: audio.length > 1,
    };
  }
  return { ok: false, error: 'episode not available on AnimeWorld' };
}

const routes = {
  '/api/health': async () => ({
    ok: true, version: VERSION, uptime: Math.round(process.uptime()),
    time: new Date().toISOString(), cached_items: cache.size,
    tmdb_configured: Boolean(TMDB_KEY),
    /* Circuit breakers are the #1 cause of "everything anime is broken" while
       the upstream is actually fine, so make their state visible. */
    breakers: [...breakers.keys()].map(breakerState),
  }),

  /* Live TV catalogue. Search/filter runs on the server so the browser never
     downloads several MB of channel JSON just to render 60 cards. */
  '/api/channels': async (q) => {
    const all = channelCatalogue.channels || [];
    const search = String(q.get('q') || '').trim().toLowerCase().slice(0, 60);
    const cat = String(q.get('cat') || '').trim();
    const country = String(q.get('country') || '').trim().toUpperCase();
    const lang = String(q.get('lang') || '').trim();
    const limit = Math.min(Math.max(parseInt(q.get('limit'), 10) || 60, 1), 200);
    const offset = Math.max(parseInt(q.get('offset'), 10) || 0, 0);

    let list = all;
    if (cat && cat !== 'All') list = list.filter((c) => c.cat === cat);
    if (country) list = list.filter((c) => c.country === country);
    /* Accept either the display name ("Hindi") or the ISO 639-3 code ("hin").
       The UI sends the name, but the code is what every other API in the app
       speaks, and asking for lang=hin used to silently return zero channels. */
    if (lang) {
      const want = lang.toLowerCase();
      list = list.filter((c) => (c.langs || []).some((l) =>
        l && (String(l.name || '').toLowerCase() === want || String(l.code || '').toLowerCase() === want)));
    }
    if (search) {
      // Match the display name first, then alternate names, so "star" ranks
      // "Star Plus" above a channel that merely has it as an alias.
      const scored = [];
      for (const c of list) {
        const name = c.name.toLowerCase();
        let score = -1;
        if (name === search) score = 0;
        else if (name.startsWith(search)) score = 1;
        else if (name.includes(search)) score = 2;
        else if ((c.alt || []).some((a) => String(a).toLowerCase().includes(search))) score = 3;
        if (score >= 0) scored.push([score, c]);
      }
      scored.sort((a, b) => a[0] - b[0] || a[1].name.localeCompare(b[1].name));
      list = scored.map((x) => x[1]);
    }

    const cats = {};
    for (const c of all) cats[c.cat] = (cats[c.cat] || 0) + 1;
    const countries = {};
    for (const c of all) if (c.country) countries[c.country] = (countries[c.country] || 0) + 1;

    // Language facet follows the country selection: picking India should offer
    // Hindi/Tamil/Telugu, not all 200 languages in the catalogue.
    const langScope = country ? all.filter((c) => c.country === country) : all;
    const languages = {};
    for (const c of langScope) {
      for (const l of (c.langs || [])) {
        if (l && l.name) languages[l.name] = (languages[l.name] || 0) + 1;
      }
    }
    const languagesTrimmed = Object.fromEntries(
      Object.entries(languages).sort((a, b) => b[1] - a[1]).slice(0, 40)
    );

    return {
      ok: true,
      total: list.length,
      catalogueTotal: all.length,
      generated: channelCatalogue.generated,
      probed: Boolean(channelCatalogue.probed),
      categories: cats,
      countries,
      languages: languagesTrimmed,
      channels: list.slice(offset, offset + limit),
    };
  },

  '/api/ping': async (q) => {
    // lightweight heartbeat. client sends &t=<token>; server keeps it live.
    const supplied = String(q.get('t') || '').slice(0, 96);
    const tok = /^[a-z0-9_-]{8,96}$/i.test(supplied)
      ? supplied
      : ('a' + (++anonCounter) + '_' + crypto.randomBytes(8).toString('hex'));
    if (presence.size > 5000) sweepPresence();
    presence.set(tok, Date.now());
    return { ok: true, token: tok, online: onlineCount(), serverTime: Date.now() };
  },

  '/api/online': async () => ({ online: onlineCount(), started: stats.started }),

  '/api/stats': async () => ({
    uptime_s: Math.round((Date.now() - stats.started) / 1000),
    requests: stats.requests,
    version: VERSION,
    tmdb_configured: Boolean(TMDB_KEY),
    api_mb: +(stats.apiBytes / 1048576).toFixed(2),
    hls_mb: +(stats.hlsBytes / 1048576).toFixed(2),
    hls_inflight: hlsInFlight,
    rate_limited: stats.rateLimited,
    backups_used: stats.backupsUsed,
    api_health: apiHealth,
    cache_items: cache.size,
    top_routes: Object.entries(stats.top).sort((a, b) => b[1] - a[1]).slice(0, 8).map(([r, n]) => ({ route: r, hits: n })),
  }),

  /* ---------------- self-test ----------------
     Demand: "acche apis dalo ... test karo". This runs the real upstream
     chain (not a ping) and reports which tier answered, so a rotated domain
     shows up as a red row instead of a mystery empty grid. The client's
     automatic runner is OFF by default (Settings -> Auto API test); this
     endpoint is always available for a manual run. */
  '/api/selftest': async (q) => {
    const only = String(q.get('only') || '').trim();
    const quick = q.get('quick') === '1';
    const checks = [
      ['cinemeta-movies', async () => {
        const d = await cinemetaList('movie', 'top');
        return { count: (d.metas || d.results || []).length };
      }],
      ['cinemeta-series', async () => {
        const d = await cinemetaList('series', 'top');
        return { count: (d.metas || d.results || []).length };
      }],
      ['anilist', async () => {
        const d = await anilist(AL_LIST, { page: 1, sort: ['POPULARITY_DESC'] });
        return { count: ((d.Page && d.Page.media) || []).length };
      }],
      ['jikan', async () => {
        const d = await jikan('/top/anime?page=1');
        return { count: (d.data || []).length };
      }],
      ['live-channels', async () => {
        const all = channelCatalogue.channels || [];
        const hindi = all.filter((c) => (c.langs || []).some((l) => l && (String(l.code).toLowerCase() === 'hin' || String(l.name).toLowerCase() === 'hindi'))).length;
        if (!all.length) throw new Error('catalogue empty');
        return { count: all.length, hindi };
      }],
      ['anime-hindi-stream', async () => {
        /* The headline requirement: an anime episode that actually carries a
           Hindi audio rendition. We assert the language list, not just a 200. */
        const d = await awResolveEpisode('Frieren: Beyond Journey\'s End', 1, 1);
        if (!d || !d.ok || !d.source) throw new Error((d && d.error) || 'no stream');
        const langs = (d.audio || []).map((a) => String(a.lang || a.code || a.name || '').toLowerCase());
        const hindi = langs.some((l) => l.startsWith('hin') || l === 'hi' || l.includes('hindi'));
        if (!hindi) throw new Error('stream has no Hindi audio: ' + langs.join(','));
        return { provider: d.provider, audio: langs, qualities: (d.qualities || []).length, hindi: true };
      }],
    ].filter(([name]) => !only || name === only)
     .filter(([name]) => !quick || name !== 'anime-hindi-stream');

    const started = Date.now();
    const results = await Promise.all(checks.map(async ([name, run]) => {
      const t0 = Date.now();
      try {
        const info = await run();
        return { name, ok: true, ms: Date.now() - t0, ...info };
      } catch (e) {
        return { name, ok: false, ms: Date.now() - t0, error: String(e && e.message || e).slice(0, 200) };
      }
    }));
    return {
      ok: results.every((r) => r.ok),
      passed: results.filter((r) => r.ok).length,
      total: results.length,
      ms: Date.now() - started,
      breakers: [...breakers.keys()].map(breakerState),
      results,
    };
  },

  '/api/cache/clear': async (q, req) => {
    const tok = String(process.env.ADMIN_CACHE_TOKEN || '');
    if (!tok) throw httpError(404, 'cache administration is disabled');
    const supplied = String(req.headers['x-admin-token'] || '');
    const a = Buffer.from(tok), b = Buffer.from(supplied);
    if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) throw httpError(403, 'forbidden');
    const n = cache.size; cache.clear();
    return { ok: true, cleared: n };
  },

  '/api/geo': async (q, req) => {
    const ip = clientIp(req);
    return cached('geo:' + ip, 60 * 60 * 1000, () => geoLookup(ip));
  },

  '/api/countries': async () => {
    try {
      const list = await tmdbCountries();
      return { countries: (list || []).map((c) => ({ code: c.iso_3166_1, name: c.english_name, native: c.native_name })) };
    } catch (e) {
      return { countries: [
        { code: 'US', name: 'United States' }, { code: 'IN', name: 'India' },
        { code: 'GB', name: 'United Kingdom' }, { code: 'CA', name: 'Canada' },
        { code: 'AU', name: 'Australia' }, { code: 'DE', name: 'Germany' },
        { code: 'FR', name: 'France' }, { code: 'JP', name: 'Japan' },
      ] };
    }
  },

  '/api/anime/tmdb': async (q) => {
    const id = positiveInt(q.get('id'), 'anime id');
    const source = q.get('source') === 'anilist' ? 'anilist' : 'mal';
    return withBackup(
      async () => {
        if (source === 'mal') return animeToTmdb(id);
        const d = await anilist(AL_DETAIL, animeVars(id, source));
        if (!d.Media || !d.Media.idMal) return { tmdb_id: null, media: 'tv', error: 'no_tmdb_match' };
        return animeToTmdb(d.Media.idMal);
      },
      async () => ({ tmdb_id: null, media: 'tv', error: 'no_tmdb_match' }),
      'anilist');
  },

  // v12.13.1: ?media=tv used to be silently ignored - the route always asked
  // for /trending/all/week and always fell back to cinemetaList('movie'), so a
  // TV request came back as 50 movies with media_type:'movie'. Honour it on
  // both the TMDB path and the keyless path.
  '/api/trending': (q) => {
    const media = String(q.get('media') || '').toLowerCase();
    const scope = media === 'tv' ? 'tv' : media === 'movie' ? 'movie' : 'all';
    return withBackup(
      () => tmdb(`/trending/${scope}/week`, { page: pageOf(q), language: langOf(q) }),
      () => cinemetaPaged(scope === 'tv' ? 'series' : 'movie', q), 'cinemeta');
  },

  '/api/movie/popular': (q) => withBackup(
    () => tmdb('/movie/popular', { page: pageOf(q), language: langOf(q) }),
    () => cinemetaPaged('movie', q), 'cinemeta'),
  '/api/movie/hindi': (q) => withBackup(
    () => tmdb('/discover/movie', {
      with_original_language: 'hi', sort_by: 'popularity.desc',
      'vote_count.gte': '20', page: pageOf(q), language: langOf(q), include_adult: 'false',
    }, 30 * 60 * 1000),
    () => cinemetaPaged('movie', q), 'cinemeta'),
  '/api/movie/top_rated': (q) => withBackup(
    () => tmdb('/movie/top_rated', { page: pageOf(q), language: langOf(q) }),
    () => cinemetaPaged('movie', q), 'cinemeta'),
  '/api/movie/upcoming': (q) => withBackup(
    () => tmdb('/movie/upcoming', { page: pageOf(q), language: langOf(q) }),
    () => cinemetaPaged('movie', q), 'cinemeta'),
  '/api/movie/now_playing': (q) => withBackup(
    () => tmdb('/movie/now_playing', { page: pageOf(q), language: langOf(q) }),
    () => cinemetaPaged('movie', q), 'cinemeta'),

  '/api/tv/popular': (q) => withBackup(
    () => tmdb('/tv/popular', { page: pageOf(q), language: langOf(q) }),
    () => cinemetaPaged('series', q), 'cinemeta'),
  '/api/tv/top_rated': (q) => withBackup(
    () => tmdb('/tv/top_rated', { page: pageOf(q), language: langOf(q) }),
    () => cinemetaPaged('series', q), 'cinemeta'),

  '/api/search/smart': async (q) => {
    const search = queryOf(q);
    const page = pageOf(q);
    const intent = parseSmartSearch(search);
    if (!intent.smart) {
      return withBackup(
        () => tmdb('/search/multi', { query: search, include_adult: 'false', page, language: langOf(q) }, 10 * 60 * 1000)
          .then((data) => ({ ...data, smart: false, intent: null })),
        async () => {
          const [movies, series] = await Promise.all([cinemetaList('movie', search), cinemetaList('series', search)]);
          return { results: [...movies.results.slice(0, 12), ...series.results.slice(0, 8)], smart: false, intent: null };
        }, 'cinemeta');
    }

    const voteFloor = intent.sort === 'vote_average.desc' ? '200' : intent.sort === 'date.desc' ? '5' : '35';
    const common = {
      include_adult: 'false', page, language: langOf(q),
      'vote_count.gte': voteFloor,
      ...(intent.language ? { with_original_language: intent.language.code } : {}),
    };
    const jobs = [];
    if (intent.media !== 'tv' && intent.media !== 'anime') {
      jobs.push(Promise.resolve().then(() => tmdb('/discover/movie', {
        ...common,
        ...(intent.genre && intent.genre.movie ? { with_genres: intent.genre.movie } : {}),
        ...(intent.year ? { primary_release_year: intent.year } : {}),
        sort_by: intent.sort === 'date.desc' ? 'primary_release_date.desc' : intent.sort,
      }, 20 * 60 * 1000)).then((data) => ({ kind: 'movie', data })).catch(() => ({ kind: 'movie', data: { results: [] } })));
    }
    if (intent.media !== 'movie' && intent.media !== 'anime') {
      jobs.push(Promise.resolve().then(() => tmdb('/discover/tv', {
        ...common,
        ...(intent.genre && intent.genre.tv ? { with_genres: intent.genre.tv } : {}),
        ...(intent.genre && intent.genre.tvKeywords ? { with_keywords: intent.genre.tvKeywords } : {}),
        ...(intent.year ? { first_air_date_year: intent.year } : {}),
        sort_by: intent.sort === 'date.desc' ? 'first_air_date.desc' : intent.sort,
      }, 20 * 60 * 1000)).then((data) => ({ kind: 'tv', data })).catch(() => ({ kind: 'tv', data: { results: [] } })));
    }
    const responses = await Promise.all(jobs);
    const groups = responses.map(({ kind, data }) => (data.results || []).map((item) => ({ ...item, media_type: kind })));
    const results = [];
    const max = Math.max(0, ...groups.map((group) => group.length));
    for (let index = 0; index < max; index++) {
      for (const group of groups) if (group[index]) results.push(group[index]);
    }
    const cleanIntent = {
      genre: intent.genre ? intent.genre.key : null,
      genre_label: intent.genre ? intent.genre.label : null,
      anime_genre_id: intent.genre ? intent.genre.anime : null,
      language: intent.language ? intent.language.code : null,
      language_label: intent.language ? intent.language.label : null,
      media: intent.media,
      sort: intent.sort,
      year: intent.year || null,
      label: intent.label,
    };
    return {
      results: results.slice(0, 40),
      page: Number(page), total_pages: Math.min(20, Math.max(1, ...responses.map((item) => item.data.total_pages || 1))),
      smart: true, intent: cleanIntent,
    };
  },
  '/api/search': (q) => {
    const search = queryOf(q);
    const page = pageOf(q);
    return withBackup(
      () => tmdb('/search/multi', { query: search, include_adult: 'false', page, language: langOf(q) }, 10 * 60 * 1000),
      async () => {
        const [mv, sr] = await Promise.all([cinemetaList('movie', search), cinemetaList('series', search)]);
        return { results: [...mv.results.slice(0, 12), ...sr.results.slice(0, 8)] };
      }, 'cinemeta');
  },

  '/api/details': (q) => {
    const media = q.get('media');
    if (!['movie', 'tv'].includes(media)) throw httpError(400, 'invalid media');
    const id = mediaIdOf(q.get('id'));
    return withBackup(
      () => tmdb(`/${media}/${id}`, { append_to_response: 'credits,similar,recommendations,content_ratings,release_dates,translations', language: langOf(q) }),
      async () => {
        const kind = media === 'tv' ? 'series' : 'movie';
        try {
          const r = await jfetch(`${CINEMETA}/meta/${kind}/${encodeURIComponent(String(id))}.json`);
          const m = (r && r.meta) || {};
          // Derive the season list from meta.videos so the client can render
          // its season tabs / episode picker on a keyless deploy.
          const byS = new Map();
          for (const v of m.videos || []) {
            const n = Number(v.season);
            if (!n || n < 1) continue;
            byS.set(n, (byS.get(n) || 0) + 1);
          }
          const seasons = [...byS.entries()].sort((a, b) => a[0] - b[0]).map(([n, c]) => ({
            season_number: n, name: `Season ${n}`, episode_count: c, id: `${id}:${n}`,
            overview: '', poster_path: m.poster || '', air_date: '',
          }));
          const dateStr = m.released ? String(m.released).slice(0, 10) : (m.year ? String(m.year).slice(0, 4) : '');
          return {
            // Keep the id the client already holds (an IMDB id keyless), never
            // moviedb_id -- swapping it made every follow-up call (season,
            // recommendations, stream lookup) query an id Cinemeta can't read.
            id,
            imdb_id: m.imdb_id || (String(id).startsWith('tt') ? String(id) : ''),
            media_type: media,
            title: m.name, name: m.name, overview: m.description || '',
            poster_path: m.poster || '', backdrop_path: m.background || '',
            vote_average: parseFloat(m.imdbRating) || 0,
            runtime: parseInt(m.runtime, 10) || 0,
            release_date: media === 'movie' ? dateStr : '',
            first_air_date: media === 'tv' ? dateStr : '',
            genres: (m.genres || m.genre || []).map((g) => ({ name: g })),
            ...(media === 'tv' ? { number_of_seasons: seasons.length || 1, number_of_episodes: (m.videos || []).length, seasons } : {}),
            credits: { cast: (m.cast || []).slice(0, 12).map((n) => ({ name: n, character: '', profile_path: '' })) },
            // The modal's "More Like This" rail reads d.recommendations /
            // d.similar straight off the detail payload, so fill it here too
            // (genre-matched, same source as /api/recommendations).
            recommendations: { results: await cinemetaRecommendations(media, id).then((r) => r.results.slice(0, 12)).catch(() => []) },
            similar: { results: [] },
            _backup: true,
          };
        } catch (e) { throw e; }
      }, 'cinemeta');
  },

  '/api/recommendations': async (q) => {
    const media = q.get('media');
    if (!['movie', 'tv'].includes(media)) throw httpError(400, 'invalid media');
    const id = mediaIdOf(q.get('id'));
    const locale = langOf(q);
    return withBackup(() => cached(`recommend:v2:${locale}:${media}:${id}`, 30 * 60 * 1000, async () => {
      const detail = await tmdb(`/${media}/${id}`, {
        language: locale,
        append_to_response: 'recommendations,similar',
      }, 30 * 60 * 1000);
      const genreIds = (detail.genres || []).map((genre) => genre.id).filter(Boolean);
      const origin = detail.original_language || '';
      const discover = genreIds.length ? await tmdb(`/discover/${media}`, {
        language: locale,
        with_genres: genreIds.slice(0, 3).join('|'),
        ...(origin ? { with_original_language: origin } : {}),
        sort_by: 'popularity.desc',
        'vote_count.gte': '30', page: '1', include_adult: 'false',
      }, 30 * 60 * 1000).catch(() => ({ results: [] })) : { results: [] };

      const ranked = new Map();
      const add = (items, base, reason) => (items || []).forEach((item, index) => {
        if (!item || String(item.id) === String(id)) return;
        const overlap = (item.genre_ids || []).filter((genreId) => genreIds.includes(genreId)).length;
        const languageBoost = origin && item.original_language === origin ? (origin === 'hi' ? 88 : 22) : 0;
        const quality = Math.min(16, Number(item.vote_average || 0) * 1.4)
          + Math.min(30, Math.log10(Number(item.vote_count || 0) + 1) * 8)
          + Math.min(24, Math.log10(Number(item.popularity || 0) + 1) * 8);
        const score = base - index * 0.7 + overlap * 7 + languageBoost + quality;
        const old = ranked.get(item.id);
        if (!old || score > old.score) ranked.set(item.id, { score, item: { ...item, media_type: media, recommendation_reason: reason } });
      });
      add(detail.recommendations && detail.recommendations.results, 104, 'Recommended for this title');
      add(detail.similar && detail.similar.results, 76, 'Similar story and genres');
      add(discover.results, 72, origin === 'hi' ? 'More Hindi titles in these genres' : 'Popular in the same genres');
      const results = [...ranked.values()].sort((a, b) => b.score - a.score).map((entry) => entry.item).slice(0, 30);
      return { results, based_on: { genres: genreIds, original_language: origin } };
    }), () => cinemetaRecommendations(media, id), 'cinemeta');
  },

  '/api/tv/season': async (q) => {
    const id = mediaIdOf(q.get('id'));
    /* Accept both ?s= (what app.js sends) and the more obvious ?season=.
       Reading only 's' made any ?season=N call silently return season 1,
       which is a trap for anyone hitting the API directly. */
    const season = positiveInt(q.get('s') || q.get('season') || 1, 'season', 100);
    return withBackup(
      () => tmdb(`/tv/${id}/season/${season}`, { language: langOf(q) }, 60 * 60 * 1000),
      () => cinemetaSeason(id, season), 'cinemeta');
  },

  '/api/watch': async (q) => {
    const media = q.get('media');
    if (!['movie', 'tv'].includes(media)) throw httpError(400, 'invalid media');
    const id = mediaIdOf(q.get('id'));
    try {
      return await tmdb(`/${media}/${id}/watch/providers`, { watch_region: regionOf(q.get('region')) }, 6 * 60 * 60 * 1000);
    } catch (e) { return { results: {} }; }
  },

  '/api/genres': (q) => {
    const media = q.get('media') === 'tv' ? 'tv' : 'movie';
    return withBackup(
      () => tmdb(`/genre/${media}/list`, { language: langOf(q) }, 24 * 60 * 60 * 1000),
      async () => cinemetaGenres(media), 'cinemeta');
  },
  '/api/movie/genre': (q) => {
    // TMDB genre ids are NOT all four digits: Family=10751, War=10752,
    // TV Movie=10770, and the TV-only ids run 10759-10768. A 9999 ceiling
    // rejected all of them with 400 "invalid genre", so eleven genre rows
    // (Family, War, Kids, Reality, Sci-Fi & Fantasy, ...) were dead on arrival.
    const g = positiveInt(q.get('g'), 'genre', 99999);
    const sort = ['popularity.desc', 'vote_average.desc', 'release_date.desc'].includes(q.get('sort')) ? q.get('sort') : 'popularity.desc';
    const page = pageOf(q);
    return withBackup(
      () => tmdb('/discover/movie', {
        with_genres: String(g), sort_by: sort,
        'vote_count.gte': '50', page, language: langOf(q),
      }),
      () => cinemetaGenreList('movie', genreNameFor('movie', g), (Number(page) - 1) * 100),
      'cinemeta');
  },
  '/api/tv/genre': (q) => {
    // See /api/movie/genre: TV leans on the 10759-10768 range especially hard.
    const g = positiveInt(q.get('g'), 'genre', 99999);
    const sort = ['popularity.desc', 'vote_average.desc', 'first_air_date.desc'].includes(q.get('sort')) ? q.get('sort') : 'popularity.desc';
    const page = pageOf(q);
    return withBackup(
      () => tmdb('/discover/tv', {
        with_genres: String(g), sort_by: sort,
        'vote_count.gte': '50', page, language: langOf(q),
      }),
      () => cinemetaGenreList('series', genreNameFor('tv', g), (Number(page) - 1) * 100),
      'cinemeta');
  },

  /* anime */
  /* Adult genres are dropped: every anime list request is sent with the SFW
     filter on, so these chips could only ever render an empty grid. */
  '/api/anime/genres': () => withBackup(
    () => jikan('/genres/anime', 24 * 60 * 60 * 1000).then((d) => ({
      genres: (d.data || []).filter((g) => (g.mal_id < 50 || g.mal_id === 62) && !ANIME_ADULT_GENRES.has(g.name)),
    })),
    async () => ({ genres: ANIME_GENRES_FALLBACK.filter((g) => !ANIME_ADULT_GENRES.has(g.name)) }), 'anilist'),
  '/api/anime/genre': (q) => {
    const g = positiveInt(q.get('g'), 'genre', 9999);
    const name = String(q.get('name') || '').trim().slice(0, 50);
    const page = pageOf(q);
    return withBackup(
      async () => {
        // The chip labels come from MAL (Jikan). AniList uses a smaller, partly
        // different genre vocabulary, so names like "Avant Garde",
        // "Award Winning", "Historical", "Detective" or "Harem" match NOTHING
        // there and AniList returns an empty list. That is not an exception, so
        // withBackup never fell through and the grid rendered zero cards.
        // The client always sends `name`, but direct/API callers may pass only
        // `g`. Recover the label from the MAL id so those requests get the
        // AniList tiers too instead of dropping straight to a 504-ing Jikan.
        const label = name || MAL_GENRE_NAME_BY_ID[g] || '';
        const alName = AL_GENRE_ALIAS[label] || label;
        let data = [];
        if (alName && AL_GENRES.has(alName)) {
          const d = await anilist(AL_LIST, { page: Number(page), sort: ['POPULARITY_DESC'], genre: alName });
          data = ((d.Page && d.Page.media) || []).map(alMediaToJikan);
        }
        // Tier 2: AniList tags cover the MAL labels AniList has no genre for.
        if (!data.length) {
          const tag = AL_GENRE_TAG[label];
          if (tag) {
            const d = await anilist(AL_TAG_LIST, { page: Number(page), tag, sort: ['POPULARITY_DESC'] });
            data = ((d.Page && d.Page.media) || []).map(alMediaToJikan);
          }
        }
        if (!data.length) throw new Error('anilist returned no media for ' + (label || g));
        return { data, pagination: { current_page: Number(page), last_visible_page: 20 } };
      },
      // Tier 3: Jikan. Its genre endpoint is currently 504-ing across the
      // board, and a hard 504 turns the grid into "Could not load". A generic
      // popular list is a far better last resort than an error screen.
      async () => {
        try {
          return await jikan(`/anime?genres=${g}&order_by=members&sort=desc&sfw=true&page=${page}`);
        } catch (err) {
          const d = await anilist(AL_LIST, { page: Number(page), sort: ['POPULARITY_DESC'] });
          const data = ((d.Page && d.Page.media) || []).map(alMediaToJikan);
          if (!data.length) throw err;
          return { data, pagination: { current_page: Number(page), last_visible_page: 20 }, _degraded: true };
        }
      }, 'jikan');
  },
  '/api/anime/top': (q) => {
    const page = pageOf(q);
    return withBackup(
      async () => {
        const d = await anilist(AL_LIST, { page: Number(page), sort: ['SCORE_DESC'] });
        const data = ((d.Page && d.Page.media) || []).map(alMediaToJikan);
        if (!data.length) throw new Error('anilist returned no media');
        return { data, pagination: { last_visible_page: 20 } };
      },
      () => jikan('/top/anime?page=' + page), 'jikan');
  },
  '/api/anime/topairing': (q) => {
    const page = pageOf(q);
    return withBackup(
      async () => {
        const d = await anilist(AL_LIST, { page: Number(page), sort: ['POPULARITY_DESC'], status: 'RELEASING' });
        const data = ((d.Page && d.Page.media) || []).map(alMediaToJikan);
        if (!data.length) throw new Error('anilist returned no media');
        return { data, pagination: { last_visible_page: 20 } };
      },
      () => jikan('/top/anime?filter=airing&page=' + page), 'jikan');
  },
  '/api/anime/search': async (q) => {
    const search = queryOf(q);
    try {
      return await withBackup(
        async () => {
          const d = await anilist(AL_LIST, { page: 1, sort: ['SEARCH_MATCH'], search });
          const data = ((d.Page && d.Page.media) || []).map(alMediaToJikan);
          if (!data.length) throw new Error('anilist returned no media');
          return { data };
        },
        () => jikan('/anime?q=' + encodeURIComponent(search) + '&page=1&sfw=true'), 'jikan');
    } catch (err) {
      // A query that genuinely matches nothing ("onepiece", a typo) made
      // AniList return an empty list and Jikan answer 504, so the user got
      // "Could not load. Try again." instead of "No results". A search with no
      // hits is a valid, empty result - never an error.
      return { data: [], _empty: true };
    }
  },
  /* Native anime playback: resolve a direct HLS manifest + subtitle tracks so
     the in-house player can offer real quality / audio / subtitle switching
     instead of surrendering control to a third-party iframe. */
  '/api/anime/stream': async (q) => {
    const id = positiveInt(q.get('id'), 'anime id');
    const ep = Math.max(1, Math.min(9999, parseInt(q.get('ep'), 10) || 1));
    const kind = q.get('source') === 'anilist' ? 'ani' : 'mal';
    const lang = q.get('lang') === 'dub' ? 'dub' : 'sub';
    const title = String(q.get('title') || '').slice(0, 120);
    const season = Math.max(1, Math.min(99, parseInt(q.get('season'), 10) || 1));
    const cacheKey = `animestream:${kind}:${id}:${ep}:${lang}:${title.toLowerCase()}`;
    return cached(cacheKey, 5 * 60 * 1000, async () => {
    // Prefer AnimeWorld when we know the title: it is the only provider that
    // returns Hindi/Tamil/Telugu audio and genuine 240p-1080p renditions. If
    // anything at all goes wrong we silently fall through to megavid, so this
    // can only ever add capability, never remove it.
    if (title) {
      try {
        const aw = await awResolveEpisode(title, season, ep);
        if (aw && aw.ok) return aw;
      } catch { /* fall through to the legacy providers */ }
    }

    let lastError = 'no anime stream provider responded';
    for (const host of ANIME_STREAM_HOSTS) {
      const endpoint = `https://${host}/api/${kind}/${id}/${ep}/${lang}`;
      const ctrl = new AbortController();
      const timer = setTimeout(() => ctrl.abort(), 12000);
      try {
        const upstream = await fetch(endpoint, {
          signal: ctrl.signal,
          headers: { 'User-Agent': UA, Accept: 'application/json,*/*', Referer: `https://${host}/`, Origin: `https://${host}` },
        });
        clearTimeout(timer);
        if (!upstream.ok) { lastError = `${host} responded ${upstream.status}`; continue; }
        const body = await upstream.json();
        if (!body || body.success === false || !body.source) { lastError = `${host} returned no source`; continue; }

        // Route the manifest and every subtitle through our proxy: the CDN is
        // hotlink-protected and the browser cannot forge a Referer.
        const payload = {
          ok: true,
          provider: host,
          lang,
          episode: ep,
          source: '/api/hls?url=' + encodeURIComponent(String(body.source)),
          tracks: (Array.isArray(body.tracks) ? body.tracks : [])
            .filter((t) => t && t.file && String(t.kind || 'captions') !== 'thumbnails')
            .map((t) => ({
              file: '/api/hls?url=' + encodeURIComponent(String(t.file)),
              label: String(t.label || 'Subtitles'),
              kind: String(t.kind || 'captions'),
              default: !!t.default,
            })),
          intro: body.intro && Number.isFinite(body.intro.start) ? body.intro : null,
          outro: body.outro && Number.isFinite(body.outro.start) ? body.outro : null,
        };
        return payload;
      } catch (e) {
        clearTimeout(timer);
        lastError = e.name === 'AbortError' ? `${host} timed out` : `${host} unreachable`;
      }
    }
    /* Last resort before giving up on native playback: MegaPlay only ever
       resolves episode 1, so it is only worth asking for that. */
    if (ep === 1) {
      try {
        const mp = await megaplayEpisode(id, lang);
        if (mp && mp.ok) return mp;
      } catch (e) { lastError = e.message || lastError; }
    }
    // Not a throw: the client falls back to the iframe providers.
    return { ok: false, error: lastError, source: null, tracks: [] };
    }, false);
  },

  /* Direct (non-iframe) playback for movies and TV.
   *
   * The iframe sources still exist and are still the fallback; this route is
   * what lets a title play in our own <video> element instead, which is the
   * only way the quality picker, the audio-language picker and the speed
   * control can apply to movies the way they already do for anime.
   *
   * Never throws for "not found": a false `ok` simply means the client keeps
   * the iframe it would have used anyway. */
  '/api/movie/stream': async (q) => {
    const rawId = String(q.get('tmdb') || q.get('id') || '');
    const kind = q.get('type') === 'tv' ? 'tv' : 'movie';
    // Keyless catalogues hand out IMDB ids; resolve them to the numeric TMDB
    // id the providers expect before validating.
    let tmdbId;
    let imdbFromId = '';
    if (/^tt\d{5,10}$/.test(rawId)) {
      imdbFromId = rawId;
      tmdbId = await tmdbIdFromImdb(rawId, kind);
      if (!tmdbId) return { ok: false, error: 'no tmdb mapping for ' + rawId, streams: [] };
    } else {
      tmdbId = positiveInt(rawId, 'tmdb id');
    }
    const season = Math.max(1, Math.min(99, parseInt(q.get('season'), 10) || 1));
    const episode = Math.max(1, Math.min(9999, parseInt(q.get('ep') || q.get('episode'), 10) || 1));
    const title = String(q.get('title') || '').slice(0, 120);
    const year = String(q.get('year') || '').slice(0, 4);
    const imdbId = /^tt\d{5,10}$/.test(String(q.get('imdb') || '')) ? String(q.get('imdb')) : imdbFromId;
    const wantLang = String(q.get('lang') || '').toLowerCase().slice(0, 3).replace(/[^a-z]/g, '');

    const cacheKey = `moviestream:${kind}:${tmdbId}:${season}:${episode}:${wantLang}`;
    // Short TTL: these are signed, expiring CDN URLs. Long enough to spare the
    // upstream a burst when a viewer flips between languages, short enough
    // that nothing handed out has gone stale.
    return cached(cacheKey, 4 * 60 * 1000, async () => {
      let res;
      try {
        res = await extractMovieStreams({ kind, tmdbId, imdbId, title, year, season, episode, wantLang });
      } catch (e) {
        return { ok: false, error: String(e && e.message || e).slice(0, 200), streams: [] };
      }
      if (!res.ok) return { ok: false, error: res.error || 'no direct stream', streams: [] };

      const streams = res.streams.map((s) => ({
        // Proxied, because these CDNs are hotlink-gated and the browser cannot
        // set a cross-origin Referer.
        source: `/api/hls?url=${encodeURIComponent(s.url)}`,
        // Raw master, needed by /api/hls/remix to graft one provider's audio
        // onto another's video. Short-lived, so only used immediately.
        master: s.url,
        language: s.language || '',
        label: s.label || 'Original',
        provider: s.provider,
        height: s.height || 0,
        qualities: Array.isArray(s.qualities) ? s.qualities : [],
        multiQuality: (s.qualities || []).length > 1,
      }));

      const subtitles = (res.subtitles || []).map((t) => ({
        file: `/api/hls?url=${encodeURIComponent(t.url)}`,
        label: String(t.label || 'Subtitle'),
        language: String(t.language || ''),
        kind: 'captions',
      }));

      const languages = [...new Set(streams.map((s) => s.language).filter(Boolean))];
      const primary = streams[0];
      return {
        ok: true,
        type: kind,
        // Flattened shape matching /api/anime/stream so the player can consume
        // either without a second code path.
        source: primary.source,
        master: primary.master,
        provider: primary.provider,
        qualities: primary.qualities,
        streams,
        languages,
        multiLanguage: languages.length > 1,
        subtitles,
      };
    }, false);
  },

  '/api/anime/details': (q) => {
    const id = positiveInt(q.get('id'), 'anime id');
    const source = q.get('source') === 'anilist' ? 'anilist' : 'mal';
    const primary = async () => {
      const d = await anilist(AL_DETAIL, animeVars(id, source));
      if (!d.Media) throw new Error('anime not found');
      return { data: alMediaToJikan(d.Media) };
    };
    if (source === 'anilist') return primary();
    // AniList has been returning 403 ("temporarily disabled") for extended
    // spells and Jikan 504s per-title when MyAnimeList refuses it, so the
    // anime tab had a single point of failure. Try /full, then the lighter
    // /anime/{id}, then the search index -- each one is a separate MAL path
    // and they do not fail together.
    const jikanChain = async () => {
      const attempts = [`/anime/${id}/full`, `/anime/${id}`];
      let lastErr;
      for (const path of attempts) {
        try {
          const r = await jikan(path);
          if (r && r.data) return r;
        } catch (e) { lastErr = e; }
      }
      throw lastErr || new Error('anime details unavailable');
    };
    return withBackup(primary, jikanChain, 'jikan');
  },
  '/api/anime/recommendations': async (q) => {
    const id = positiveInt(q.get('id'), 'anime id');
    const source = q.get('source') === 'anilist' ? 'anilist' : 'mal';
    try {
      const data = await anilist(AL_RECOMMENDATIONS, animeVars(id, source));
      const nodes = data && data.Media && data.Media.recommendations && data.Media.recommendations.nodes || [];
      const results = nodes.filter((node) => node && node.mediaRecommendation).map((node) => ({
        ...alMediaToJikan(node.mediaRecommendation),
        recommendation_reason: node.rating > 0 ? 'Highly recommended by anime viewers' : 'Related anime',
        recommendation_score: node.rating || 0,
      }));
      return { data: results };
    } catch (e) {
      if (source !== 'mal') return { data: [] };
      try {
        const result = await jikan(`/anime/${id}/recommendations`, 30 * 60 * 1000);
        return { data: (result.data || []).slice(0, 24).map((item) => ({
          ...(item.entry || {}), recommendation_reason: 'Recommended by anime viewers', recommendation_score: item.votes || 0,
        })) };
      } catch (backupError) { return { data: [] }; }
    }
  },

  '/api/anime/videos': (q) => {
    const id = positiveInt(q.get('id'), 'anime id');
    const source = q.get('source') === 'anilist' ? 'anilist' : 'mal';
    return animeVideos(id, source);
  },

  /* K-Drama / Asian drama browse */
  '/api/drama/popular': (q) => {
    const origin = /^[a-z]{2}$/.test(q.get('origin') || '') ? q.get('origin') : '';
    return withBackup(
      () => tmdb('/discover/tv', {
        ...(origin ? { with_original_language: origin } : {}),
        sort_by: 'popularity.desc',
        page: pageOf(q),
        'vote_count.gte': '10',
        language: langOf(q),
      }),
      /* The old keyless fallback was cinemetaList('series') -- the plain
         top-series catalogue. That is why the Drama tab showed Reacher,
         House of the Dragon and Ted Lasso: it was not filtering by origin
         at all, so "Drama" was indistinguishable from "TV". Cinemeta has no
         country catalogue, but every catalogue item carries a `country`
         string, so scan a few skip-blocks and keep the Asian titles. */
      () => cinemetaDrama(origin, Math.max(1, Number(pageOf(q)) || 1)), 'cinemeta');
  },
};

/* ---------------- HLS proxy for Live TV ----------------
   HLS manifests contain relative URLs, so they must be rewritten back through
   this same-origin proxy. Targets are restricted to the public CDNs used by
   the built-in channel list to prevent the Render service becoming an open
   bandwidth relay. */
const HLS_ALLOWED_SUFFIXES = [
  '.getaj.net', '.france24.com', '.akamaized.net', '.bloomberg.com',
  '.springcpc.com', '.cloudfront.net', '.samsung.wurl.tv', '.skycdp.com',
  '.stackpathdns.com', '.wizdeo.io', '.luxeat.lu', '.cloudycdn.services',
  '.intoday.in', '.akamaihd.net', '.trt.com.tr', '.wiseplayout.com',
  '.shemaroo.com', '.thelegitpro.in',
  // AnimeWorld/Zephyrix manifest hosts. The player moved .top -> .org in
  // Aug 2026 (the .top host now returns a Cloudflare 403), which silently
  // killed every Hindi/Tamil/Telugu audio track. Keep both: .org is live,
  // .top costs nothing to leave allowlisted if it ever comes back.
  '.zephyrix.org', '.zephyrix.top', '.zephyrflick.top',
  ...String(process.env.HLS_ALLOWED_SUFFIXES || '').split(',').map((v) => v.trim().toLowerCase()).filter(Boolean),
];
/* The AnimeWorld/Zephyrix segment CDNs are numbered and rotate without
   warning: s11.zn-grid05.top was serving yesterday, s11.zn-grid06.top today.
   Hard-coding each number silently 403'd every video segment the moment the
   CDN rolled over (round-8 bug: the audio played but no picture). Match the
   whole family with a pattern instead. */
const HLS_ALLOWED_PATTERNS = [
  /(^|\.)zn-grid\d*\.(top|org|net)$/,
  /(^|\.)zephyrix\.(org|top)$/,
  /(^|\.)zephyrflick\.(org|top)$/,
  /* Movie/TV direct-stream CDNs (/api/movie/stream). Like the anime CDNs
     above these are numbered and rotate, so match the family. */
  /(^|\.)peakstorm\.top$/,
  /(^|\.)primecrown\.top$/,
  /(^|\.)1shows\.app$/,
  /* The vimeos CDN rotates its TLD as well as its host number: p2.vimeos.zip
     and s8.vimeos.net were both live in the same response. Allowlisting only
     .zip 403'd every s*.vimeos.net video AND every subtitle track it serves,
     so match the whole family across both TLDs. */
  /(^|\.)vimeos\.(zip|net)$/,
  /(^|\.)dolphin-d\d*\.workers\.dev$/,
  /(^|\.)slast\d*did\.com$/,
  /(^|\.)vdrk\.site$/,
  /* MegaPlay serves its manifests and subtitle tracks from watching.onl (and
     the cloudbuzz.lol mirrors it hands out); without these the fallback
     provider resolves a URL the proxy then refuses. */
  /(^|\.)watching\.onl$/,
  /(^|\.)cloudbuzz\.lol$/,
];

const HLS_ALLOWED_EXACT = new Set([
  '103.225.189.136',
  // Anime stream hosts (native player path). These serve the m3u8/vtt returned
  // by the anime source APIs below and require a matching Referer.
  'megavid.buzz', 'megaplay.buzz', 'animeplay.cfd',
  // AnimeWorld / Zephyrix multi-audio path.
  ...AW_SITES, ...AW_PLAYER_HOSTS,
  ...String(process.env.HLS_ALLOWED_HOSTS || '').split(',').map((v) => v.trim().toLowerCase()).filter(Boolean),
]);

/* Some CDNs hotlink-protect their media and return 403 unless the request
   carries the referer of the site that issued the link. The browser cannot set
   Referer cross-origin, which is exactly why these streams must be proxied. */
const HLS_REFERER_BY_HOST = [
  [/(^|\.)megavid\.buzz$/, 'https://megavid.buzz/'],
  [/(^|\.)megaplay\.buzz$/, 'https://megaplay.buzz/'],
  [/(^|\.)watching\.onl$/, 'https://megaplay.buzz/'],
  [/(^|\.)cloudbuzz\.lol$/, 'https://megaplay.buzz/'],
  [/(^|\.)animeplay\.cfd$/, 'https://animeplay.cfd/'],
  // Zephyrix serves the manifest AND the segments; both are hotlink-gated.
  // .org is the live host since Aug 2026; .top now answers Cloudflare 403.
  [/(^|\.)zephyrix\.org$/, 'https://play.zephyrix.org/'],
  [/(^|\.)zephyrix\.top$/, 'https://play.zephyrix.top/'],
  [/(^|\.)zephyrflick\.(org|top)$/, 'https://play.zephyrflick.top/'],
  /* Segment CDNs used by the above (zn-grid01.top and friends). These must
     carry the CURRENT player origin as referer, so read it from the live
     player-host list instead of freezing a domain that will rotate again. */
  [/(^|\.)zn-grid\d*\.(top|org|net)$/, () => `https://${awPlayerHosts()[0]}/`],
  [/(^|\.)watchanimeworld\.[a-z]{2,4}$/, () => `https://${AW_SITES[0]}/`],
  /* Movie/TV direct streams. Both extractors' CDNs check the referer of the
     player that issued the signed URL, not of our site. */
  [/(^|\.)peakstorm\.top$/, 'https://player.videasy.to/'],
  [/(^|\.)primecrown\.top$/, 'https://player.videasy.to/'],
  [/(^|\.)vimeos\.zip$/, 'https://player.videasy.to/'],
  [/(^|\.)1shows\.app$/, 'https://vidrock.net/'],
  [/(^|\.)dolphin-d\d*\.workers\.dev$/, 'https://vidrock.net/'],
  [/(^|\.)slast\d*did\.com$/, 'https://vidrock.net/'],
  [/(^|\.)vdrk\.site$/, 'https://vidrock.net/'],
];

function hlsRefererFor(hostname) {
  const host = String(hostname || '').toLowerCase();
  const hit = HLS_REFERER_BY_HOST.find(([re]) => re.test(host));
  /* Entries may be a literal string or a thunk. The thunk form exists so a
     rotating provider (Zephyrix moved .top -> .org and 403'd every Hindi
     segment) resolves its referer from the CURRENT host list at call time
     instead of a domain frozen into this table. */
  if (hit) return typeof hit[1] === 'function' ? (hit[1]() || '') : hit[1];
  // Segment hosts discovered from a trusted manifest inherit its referer.
  // A player host we learned from a trusted episode page refers to itself.
  if (awLearnedHosts().includes(host)) return `https://${host}/`;
  const derived = typeof derivedHlsEntry === 'function' ? derivedHlsEntry(host) : null;
  return derived && derived.referer ? derived.referer : '';
}

let hlsInFlight = 0;

function isPrivateAddress(address) {
  const ip = String(address || '').toLowerCase().replace(/^::ffff:/, '');
  if (!ip) return true;
  if (net.isIPv4(ip)) {
    const parts = ip.split('.').map(Number);
    return parts[0] === 0 || parts[0] === 10 || parts[0] === 127 ||
      (parts[0] === 169 && parts[1] === 254) ||
      (parts[0] === 172 && parts[1] >= 16 && parts[1] <= 31) ||
      (parts[0] === 192 && parts[1] === 168) ||
      (parts[0] === 100 && parts[1] >= 64 && parts[1] <= 127) ||
      parts[0] >= 224;
  }
  if (net.isIPv6(ip)) {
    return ip === '::' || ip === '::1' || ip.startsWith('fc') || ip.startsWith('fd') ||
      /^fe[89ab]/.test(ip) || ip.startsWith('2001:db8:');
  }
  return true;
}

/* These CDNs hand out a different hostname on almost every request
   (peakstorm.top -> primecrown.top -> polarcandy.top ...), so a hand-written
   allowlist goes stale within days and playback dies with a 403 from our own
   proxy. Instead we trust transitively: if a manifest we already allowed
   points at a segment host, that host is part of the same stream and is
   allowed too — for a while. The entry is short-lived and remembers which
   referer the parent needed, so hotlink gating keeps working on the segments.

   This grants no new reach: an attacker cannot get a host in here without
   first serving a playlist from a host we already trust. */
const DERIVED_HLS_HOSTS = new Map();
const DERIVED_HLS_TTL = 6 * 60 * 60 * 1000;
const DERIVED_HLS_MAX = 500;

function trustDerivedHlsHost(hostname, parentUrl) {
  const host = String(hostname || '').toLowerCase().replace(/\.$/, '');
  if (!host || allowedHlsHost(host)) return;
  let referer = '';
  try {
    const parent = new URL(String(parentUrl));
    // Inherit the parent's referer requirement; the segments of a hotlink-
    // gated manifest are gated the same way.
    referer = hlsRefererFor(parent.hostname) || `${parent.protocol}//${parent.host}/`;
  } catch (e) { /* keep the default */ }
  if (DERIVED_HLS_HOSTS.size >= DERIVED_HLS_MAX) {
    const oldest = DERIVED_HLS_HOSTS.keys().next().value;
    if (oldest) DERIVED_HLS_HOSTS.delete(oldest);
  }
  DERIVED_HLS_HOSTS.set(host, { expires: Date.now() + DERIVED_HLS_TTL, referer });
}

function derivedHlsEntry(host) {
  const hit = DERIVED_HLS_HOSTS.get(host);
  if (!hit) return null;
  if (hit.expires < Date.now()) { DERIVED_HLS_HOSTS.delete(host); return null; }
  return hit;
}

/* ============================================================
   LIVE TV CATALOGUE (channels.json, built by tools/build-channels.js)
   The proxy allowlist cannot be a hand-written list once there are
   thousands of channels, so the catalogue itself is the allowlist:
   a host is proxyable precisely because a channel in the shipped,
   probed catalogue points at it. Nothing else is granted access.
   ============================================================ */
const CHANNELS_FILE = path.join(__dirname, 'channels.json');
let channelCatalogue = { generated: null, count: 0, channels: [] };
const CHANNEL_HOSTS = new Set();

function loadChannelCatalogue() {
  try {
    // The catalogue ships gzipped (~5x smaller in git and in the deploy
    // bundle). Plain JSON is still honoured so a hand-edited file works.
    let raw;
    const gz = CHANNELS_FILE + '.gz';
    if (fs.existsSync(gz)) raw = zlib.gunzipSync(fs.readFileSync(gz)).toString('utf8');
    else raw = fs.readFileSync(CHANNELS_FILE, 'utf8');
    const parsed = JSON.parse(raw);
    const list = Array.isArray(parsed.channels) ? parsed.channels : [];
    CHANNEL_HOSTS.clear();
    for (const ch of list) {
      for (const st of ch.streams || []) {
        try { CHANNEL_HOSTS.add(new URL(st.url).hostname.toLowerCase()); }
        catch (_) { /* skip malformed */ }
      }
    }
    channelCatalogue = parsed;
    console.log(`Live TV: ${list.length} channels, ${CHANNEL_HOSTS.size} stream hosts`);
  } catch (e) {
    console.warn('Live TV catalogue unavailable:', e.message);
    channelCatalogue = { generated: null, count: 0, channels: [] };
  }
}
loadChannelCatalogue();

function allowedHlsHost(hostname) {
  const host = String(hostname || '').toLowerCase().replace(/\.$/, '');
  return HLS_ALLOWED_EXACT.has(host)
    || CHANNEL_HOSTS.has(host)
    // A player host learned from a trusted AnimeWorld episode page. This is
    // what lets a provider domain rotation heal without a redeploy.
    || awLearnedHosts().includes(host)
    || HLS_ALLOWED_SUFFIXES.some((suffix) => host.endsWith(suffix))
    || HLS_ALLOWED_PATTERNS.some((re) => re.test(host))
    || !!derivedHlsEntry(host);
}

async function validateHlsUrl(value) {
  let u;
  try { u = value instanceof URL ? value : new URL(String(value)); }
  catch (e) { throw httpError(400, 'bad stream url'); }
  if (!['http:', 'https:'].includes(u.protocol) || u.username || u.password) throw httpError(400, 'blocked stream url');
  if (!allowedHlsHost(u.hostname)) throw httpError(403, 'stream host is not allowed');
  if (u.port && !['80', '443'].includes(u.port)) throw httpError(400, 'stream port is not allowed');
  if (net.isIP(u.hostname)) {
    if (isPrivateAddress(u.hostname)) throw httpError(403, 'private stream address blocked');
  } else {
    let resolved;
    try { resolved = await dns.lookup(u.hostname, { all: true, verbatim: true }); }
    catch (e) { throw httpError(502, 'stream host lookup failed'); }
    if (!resolved.length || resolved.some((item) => isPrivateAddress(item.address))) {
      throw httpError(403, 'private stream address blocked');
    }
  }
  return u;
}

async function fetchHlsUpstream(initialUrl, req) {
  let current = await validateHlsUrl(initialUrl);
  for (let hop = 0; hop < 5; hop++) {
    const ctrl = new AbortController();
    const timer = setTimeout(() => ctrl.abort(), 15000);
    let response;
    try {
      const referer = hlsRefererFor(current.hostname);
      response = await fetch(current, {
        signal: ctrl.signal,
        redirect: 'manual',
        headers: {
          'User-Agent': UA,
          Accept: req.headers.accept || '*/*',
          ...(referer ? { Referer: referer, Origin: referer.replace(/\/$/, '') } : {}),
          ...(req.headers.range ? { Range: req.headers.range } : {}),
        },
      });
    } catch (e) {
      clearTimeout(timer);
      throw httpError(502, e.name === 'AbortError' ? 'stream timed out' : 'stream connection failed');
    }
    clearTimeout(timer);
    if (response.status >= 300 && response.status < 400 && response.headers.get('location')) {
      current = await validateHlsUrl(new URL(response.headers.get('location'), current));
      continue;
    }
    return { response, finalUrl: current };
  }
  throw httpError(502, 'too many stream redirects');
}

const downloader = createDownloadHandler({ fetchHlsUpstream, securityHeaders, httpError });

function proxyHlsUrl(value, base) {
  try {
    const absolute = new URL(value, base);
    if (!['http:', 'https:'].includes(absolute.protocol)) return value;
    trustDerivedHlsHost(absolute.hostname, base);
    return '/api/hls?url=' + encodeURIComponent(absolute.toString());
  } catch (e) { return value; }
}

function rewriteM3u8(text, base) {
  return String(text).split(/\r?\n/).map((line) => {
    if (!line) return line;
    if (!line.startsWith('#')) return proxyHlsUrl(line.trim(), base);
    // Keys, subtitles and init segments often live in URI="..." attributes.
    return line.replace(/URI=("([^"]+)"|'([^']+)')/gi, (whole, quoted, dbl, single) => {
      const value = dbl || single || '';
      const quote = quoted[0];
      return `URI=${quote}${proxyHlsUrl(value, base)}${quote}`;
    });
  }).join('\n');
}

/* ---------------------------------------------------------------------------
   CROSS-PROVIDER REMIX  (/api/hls/remix)
   ---------------------------------------------------------------------------
   The user's complaint: "the 4K source has bad quality but has Hindi, the
   other source has good quality" -> they want audio from one provider and
   video from the other.

   With sealed iframe players (Videasy, VidFast, APIPlayer...) that is
   impossible; the page is a black box and we can never reach its audio.
   But at the HLS level it IS possible, because a master playlist keeps
   video renditions and audio renditions as SEPARATE entries linked by a
   GROUP-ID. So we can:

     - fetch master A (the good-video provider) and master B (the has-Hindi one)
     - keep A's #EXT-X-STREAM-INF video renditions
     - graft B's #EXT-X-MEDIA:TYPE=AUDIO rows into A's audio group
     - hand the browser one synthetic master

   hls.js then plays A's video with B's audio track, switchable live.
   Everything is proxied through /api/hls so referer gating still works.

   Caveat we surface honestly to the UI: the two masters must be the same
   cut of the same episode or the audio drifts. We only offer the remix when
   both sides report a comparable duration.
--------------------------------------------------------------------------- */
async function fetchMasterText(url, req) {
  const { response, finalUrl } = await fetchHlsUpstream(url, req);
  if (!response.ok) throw httpError(502, 'remix upstream failed');
  const raw = Buffer.from(await response.arrayBuffer());
  if (raw.length > 2 * 1024 * 1024) throw httpError(502, 'remix manifest too large');
  return { text: raw.toString('utf8'), finalUrl };
}

/* Split a master into its audio rows, its video rows, and everything else. */
function splitMaster(text, base) {
  const lines = String(text).split(/\r?\n/);
  const audio = [];
  const video = [];   // { inf, uri }
  const other = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.startsWith('#EXT-X-MEDIA:TYPE=AUDIO')) {
      audio.push(line.replace(/URI=("([^"]+)"|'([^']+)')/i, (whole, q, dbl, sgl) => {
        const value = dbl || sgl || '';
        return 'URI="' + proxyHlsUrl(value, base) + '"';
      }));
    } else if (line.startsWith('#EXT-X-STREAM-INF')) {
      // The URI is on the following non-comment line.
      let j = i + 1;
      while (j < lines.length && (!lines[j] || lines[j].startsWith('#'))) j++;
      if (j < lines.length) {
        video.push({ inf: line, uri: proxyHlsUrl(lines[j].trim(), base) });
        i = j;
      }
    } else if (line.startsWith('#EXT-X-MEDIA:TYPE=SUBTITLES')) {
      other.push(line.replace(/URI=("([^"]+)"|'([^']+)')/i, (whole, q, dbl, sgl) => {
        const value = dbl || sgl || '';
        return 'URI="' + proxyHlsUrl(value, base) + '"';
      }));
    }
  }
  return { audio, video, other };
}

function mediaAttr(line, key) {
  const m = line.match(new RegExp(key + '="([^"]*)"', 'i'));
  return m ? m[1] : '';
}

/* Force every audio row into one group id and make exactly one DEFAULT. */
function normaliseAudioRows(rows, groupId, preferLang) {
  const want = String(preferLang || '').toLowerCase().slice(0, 3);
  let defaultIndex = -1;
  const cleaned = rows.map((row, index) => {
    let out = row
      .replace(/GROUP-ID="[^"]*"/i, 'GROUP-ID="' + groupId + '"')
      .replace(/DEFAULT=(YES|NO)/i, 'DEFAULT=NO')
      .replace(/AUTOSELECT=(YES|NO)/i, 'AUTOSELECT=YES');
    if (!/GROUP-ID=/i.test(out)) out = out.replace('#EXT-X-MEDIA:', '#EXT-X-MEDIA:GROUP-ID="' + groupId + '",');
    if (!/DEFAULT=/i.test(out)) out += ',DEFAULT=NO';
    const lang = mediaAttr(out, 'LANGUAGE').toLowerCase();
    if (want && defaultIndex < 0 && (lang === want || lang.startsWith(want.slice(0, 2)))) defaultIndex = index;
    return out;
  });
  if (defaultIndex < 0 && cleaned.length) defaultIndex = 0;
  if (defaultIndex >= 0) cleaned[defaultIndex] = cleaned[defaultIndex].replace(/DEFAULT=NO/i, 'DEFAULT=YES');
  return cleaned;
}

/* De-duplicate audio rows by LANGUAGE+NAME so a remix does not show
   "Hindi" three times when both providers carry it. */
function dedupeAudioRows(rows) {
  const seen = new Set();
  const out = [];
  for (const row of rows) {
    const key = (mediaAttr(row, 'LANGUAGE') + '|' + mediaAttr(row, 'NAME')).toLowerCase();
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(row);
  }
  return out;
}

async function hlsRemix(req, res, u) {
  const videoUrl = u.searchParams.get('video');
  const audioUrl = u.searchParams.get('audio');
  const preferLang = u.searchParams.get('lang') || '';
  if (!videoUrl || !audioUrl || videoUrl.length > 3000 || audioUrl.length > 3000) {
    return sendJson(res, 400, { error: 'video and audio master urls required' }, req.headers);
  }
  if (hlsInFlight >= 40) {
    return sendJson(res, 503, { error: 'stream proxy busy' }, req.headers, { headers: { 'Retry-After': '3' } });
  }
  hlsInFlight++;
  try {
    const [videoSide, audioSide] = await Promise.all([
      fetchMasterText(videoUrl, req),
      fetchMasterText(audioUrl, req),
    ]);
    const vParts = splitMaster(videoSide.text, videoSide.finalUrl);
    const aParts = splitMaster(audioSide.text, audioSide.finalUrl);
    if (!vParts.video.length) throw httpError(502, 'video master has no renditions');

    const GROUP = 'sv-mix';
    // Audio from the donor first (that is the whole point), then whatever the
    // video side already had, so the user never LOSES a language by remixing.
    const rows = normaliseAudioRows(
      dedupeAudioRows(aParts.audio.concat(vParts.audio)), GROUP, preferLang,
    );
    if (!rows.length) throw httpError(502, 'audio master exposes no selectable tracks');

    const out = ['#EXTM3U', '#EXT-X-VERSION:4'];
    rows.forEach((row) => out.push(row));
    vParts.other.forEach((row) => out.push(row));
    aParts.other.forEach((row) => out.push(row));
    vParts.video.forEach((entry) => {
      // Point every video rendition at our merged audio group and strip any
      // audio codec the original advertised for its own group.
      let inf = entry.inf.replace(/,?AUDIO="[^"]*"/i, '');
      inf += ',AUDIO="' + GROUP + '"';
      out.push(inf);
      out.push(entry.uri);
    });
    const body = Buffer.from(out.join('\n') + '\n');
    stats.hlsBytes += body.length;
    res.writeHead(200, securityHeaders({
      'Content-Type': 'application/vnd.apple.mpegurl; charset=utf-8',
      'Cache-Control': 'no-store',
      'Content-Length': String(body.length),
    }));
    if (req.method === 'HEAD') return res.end();
    return res.end(body);
  } catch (err) {
    const code = err && err.statusCode ? err.statusCode : 502;
    return sendJson(res, code, { error: (err && err.message) || 'remix failed' }, req.headers);
  } finally {
    hlsInFlight--;
  }
}

/* ---------------------------------------------------------------------------
   Manifest single-flight + micro-cache.

   A live HLS player re-fetches the media playlist every target-duration
   (typically 2-6 s) for as long as the channel is on screen. With N viewers on
   the same channel that is N upstream fetches per cycle, all asking for a
   manifest that is byte-identical. Measured: 100 viewers on one channel = 100
   upstream round-trips every ~4 s, which is what pushes /api/hls into its
   40-slot ceiling and returns 503 "stream proxy busy" to everyone.

   Two mechanics, both only ever applied to PLAYLISTS (never to media segments,
   which must stream through untouched):
     - single-flight: concurrent requests for the same URL share one upstream
       promise, so 100 viewers cost exactly 1 fetch.
     - micro-cache: the rewritten manifest is reused for MANIFEST_TTL_MS. This
       is shorter than any real target-duration, so players never see a stale
       segment list; it only collapses the stampede within one cycle.
   Neither changes what the client receives. */
const MANIFEST_TTL_MS = 2000;
const MANIFEST_CACHE_MAX = 256;
const manifestCache = new Map();
const manifestInflight = new Map();

function manifestCacheGet(key) {
  const hit = manifestCache.get(key);
  if (!hit) return null;
  if (Date.now() - hit.at > MANIFEST_TTL_MS) { manifestCache.delete(key); return null; }
  return hit.body;
}

function manifestCacheSet(key, body) {
  manifestCache.set(key, { body, at: Date.now() });
  while (manifestCache.size > MANIFEST_CACHE_MAX) manifestCache.delete(manifestCache.keys().next().value);
}

async function hlsProxy(req, res, u) {
  if (req.method !== 'GET' && req.method !== 'HEAD') {
    res.writeHead(405, securityHeaders({ Allow: 'GET, HEAD' }));
    return res.end();
  }
  const target = u.searchParams.get('url');
  if (!target || target.length > 3000) {
    res.writeHead(400, securityHeaders({ 'Content-Type': 'text/plain; charset=utf-8' }));
    return res.end('url required');
  }

  const sendManifest = (body) => {
    stats.hlsBytes += body.length;
    res.writeHead(200, securityHeaders({
      'Content-Type': 'application/vnd.apple.mpegurl; charset=utf-8',
      'Cache-Control': 'no-store',
      'Content-Length': String(body.length),
    }));
    if (req.method === 'HEAD') return res.end();
    return res.end(body);
  };

  // Only playlists are ever shared. Segments must stream through untouched
  // (range requests, 32 MB bodies), so they take the plain path below.
  const looksLikeManifest = /\.m3u8(?:$|\?)/i.test(target);

  if (looksLikeManifest) {
    // Cache hit costs no upstream fetch and no in-flight slot at all.
    const cached = manifestCacheGet(target);
    if (cached) return sendManifest(cached);

    // Someone is already fetching this exact manifest: ride along on their
    // result rather than opening a second connection and burning a second
    // slot. This MUST be checked before the slot ceiling, otherwise a burst of
    // viewers on one channel exhausts the 40 slots and everybody past #40 gets
    // a 503 for a manifest we are already in the middle of fetching.
    const pending = manifestInflight.get(target);
    if (pending) {
      try {
        const body = await pending;
        if (body) return sendManifest(body);
      } catch (e) { /* leader failed: fall through and try ourselves */ }
    }
  }

  if (hlsInFlight >= 40) {
    res.writeHead(503, securityHeaders({ 'Retry-After': '3', 'Content-Type': 'text/plain; charset=utf-8' }));
    return res.end('stream proxy busy');
  }
  hlsInFlight++;

  // Become the leader for this manifest BEFORE the upstream round-trip, so that
  // everyone arriving during those few hundred milliseconds waits on us instead
  // of opening their own connection. Publishing after the fetch (as an earlier
  // revision did) shares nothing, because the fetch is the entire cost.
  let settleInflight = null;
  if (looksLikeManifest && !manifestInflight.has(target)) {
    let resolveInflight; let rejectInflight;
    const share = new Promise((resolve, reject) => { resolveInflight = resolve; rejectInflight = reject; });
    share.catch(() => {});
    manifestInflight.set(target, share);
    settleInflight = { ok: resolveInflight, fail: rejectInflight };
  }

  try {
    const { response: r, finalUrl } = await fetchHlsUpstream(target, req);
    const ct = r.headers.get('content-type') || 'application/octet-stream';
    const playlist = /mpegurl|application\/vnd\.apple\.mpegurl/i.test(ct) || /\.m3u8(?:$|\?)/i.test(finalUrl.pathname + finalUrl.search);
    if (!r.ok || !r.body) {
      res.writeHead(r.status || 502, securityHeaders({ 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' }));
      return res.end('upstream stream error');
    }

    if (playlist) {
      const raw = Buffer.from(await r.arrayBuffer());
      if (raw.length > 2 * 1024 * 1024) throw httpError(502, 'stream manifest too large');
      const body = Buffer.from(rewriteM3u8(raw.toString('utf8'), finalUrl));
      manifestCacheSet(target, body);
      if (settleInflight) {
        manifestInflight.delete(target);
        settleInflight.ok(body);
        settleInflight = null;
      }
      return sendManifest(body);
    }

    const headers = securityHeaders({
      'Content-Type': ct,
      'Cache-Control': 'public, max-age=20',
      ...(r.headers.get('content-range') ? { 'Content-Range': r.headers.get('content-range') } : {}),
      ...(r.headers.get('accept-ranges') ? { 'Accept-Ranges': r.headers.get('accept-ranges') } : {}),
    });
    res.writeHead(r.status, headers);
    if (req.method === 'HEAD') return res.end();
    const reader = r.body.getReader();
    let total = 0;
    const maxBytes = 32 * 1024 * 1024;
    while (true) {
      // Live TV viewers change channels constantly, which aborts the socket
      // mid-segment. Stop pulling from upstream the moment that happens.
      if (res.destroyed || res.writableEnded || !res.writable) {
        await reader.cancel('client disconnected').catch(() => {});
        break;
      }
      const { done, value } = await reader.read();
      if (done) break;
      total += value.byteLength;
      if (total > maxBytes) {
        await reader.cancel('segment too large').catch(() => {});
        throw httpError(502, 'stream segment too large');
      }
      if (!res.write(Buffer.from(value))) {
        // Never await 'drain' alone: on a closed socket that event never fires,
        // so the request would hang forever and leak its in-flight slot until
        // the proxy wedged at 503 and Live TV stopped loading for everyone.
        const drained = await new Promise((resolve) => {
          let settled = false;
          const finish = (ok) => { if (!settled) { settled = true; cleanup(); resolve(ok); } };
          const onDrain = () => finish(true);
          const onStop = () => finish(false);
          const timer = setTimeout(() => finish(false), 20000);
          function cleanup() {
            clearTimeout(timer);
            res.off('drain', onDrain);
            res.off('close', onStop);
            res.off('error', onStop);
          }
          res.once('drain', onDrain);
          res.once('close', onStop);
          res.once('error', onStop);
        });
        if (!drained) {
          await reader.cancel('client gone').catch(() => {});
          break;
        }
      }
    }
    stats.hlsBytes += total;
    if (!res.writableEnded) res.end();
  } catch (e) {
    if (!res.headersSent) {
      res.writeHead(e.status || 502, securityHeaders({ 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' }));
      res.end(e.message || 'upstream stream error');
    } else if (!res.writableEnded) {
      res.destroy();
    }
  } finally {
    // If a manifest fetch was published as in-flight but then threw, the riders
    // waiting on it must be released or they hang until their socket times out.
    if (settleInflight) {
      manifestInflight.delete(target);
      settleInflight.fail(new Error('manifest fetch failed'));
    }
    hlsInFlight--;
  }
}

/* ---------------- static + compression + headers ---------------- */
const MIME = {
  '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.json': 'application/json; charset=utf-8',
  '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
  '.svg': 'image/svg+xml', '.html': 'text/html; charset=utf-8',
  '.webmanifest': 'application/manifest+json; charset=utf-8', '.ico': 'image/x-icon',
  '.webp': 'image/webp', '.woff2': 'font/woff2', '.txt': 'text/plain; charset=utf-8',
  '.xml': 'application/xml; charset=utf-8',
};
const COMPRESSIBLE = /^text\/|application\/(?:json|javascript|manifest|xml)/i;
const CSP = [
  "default-src 'self'",
  "base-uri 'self'",
  "object-src 'none'",
  "script-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net https://unpkg.com",
  "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com",
  "font-src 'self' data: https://fonts.gstatic.com",
  "img-src 'self' data: blob: https:",
  "media-src 'self' blob: https:",
  // blob: is required because player SDKs (Vidstack et al.) fetch subtitle
  // tracks through blob URLs; https: covers HLS manifests from live channels.
  "connect-src 'self' blob: data: https: https://api.themoviedb.org https://api.jikan.moe https://graphql.anilist.co",
  // 'self' is required by the download button: it navigates a hidden
  // same-origin iframe at /api/download so the browser handles the save
  // without tearing down the player. Without it the download is blocked
  // outright whenever the app is served over plain http (local, LAN).
  "frame-src 'self' https:",
  "worker-src 'self' blob:",
  "form-action 'self'",
].join('; ');

function securityHeaders(extra = {}) {
  return {
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'strict-origin-when-cross-origin',
    'Permissions-Policy': 'camera=(), microphone=(), geolocation=(), payment=()',
    'Cross-Origin-Opener-Policy': 'same-origin-allow-popups',
    'Content-Security-Policy': CSP,
    ...extra,
  };
}

function sendJson(res, code, data, reqHeaders, options = {}) {
  const body = Buffer.from(JSON.stringify(data));
  stats.apiBytes += body.length;
  const headers = securityHeaders({
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': options.cacheControl || 'no-store',
    Vary: 'Accept-Encoding',
    ...(options.headers || {}),
  });
  negotiateCompression(reqHeaders, headers, body, code, res, options.head);
}

// ---------------------------------------------------------------------------
// Compression back-pressure.
//
// Every zlib async call allocates a native compressor context off-heap and
// queues work on libuv's 4-thread pool. Under a burst (thousands of concurrent
// API requests) Node happily allocates thousands of those contexts before the
// pool drains any of them; measured peak RSS hit 1052 MB for 12k concurrent API
// requests, which OOM-kills a 512 MB Render instance (exit 137).
//
// Two defences, both measured:
//   1. compCache — identical response bodies compress to identical bytes, and a
//      burst is overwhelmingly the SAME hot endpoints. Hash the body once and
//      reuse the result, so N concurrent /api/trending cost one compression.
//   2. compGate — a hard ceiling on compressions in flight. Past the ceiling we
//      send the response uncompressed rather than queueing unbounded native
//      contexts. Slightly more egress for a few requests beats a dead process.
const COMP_CACHE_MAX = 96;
const COMP_MAX_INFLIGHT = 24;
const COMP_CACHE_MAX_BYTES = 512 * 1024;
const compCache = new Map();
let compInflight = 0;

function compCacheGet(key) {
  const hit = compCache.get(key);
  if (!hit) return null;
  // refresh LRU position
  compCache.delete(key);
  compCache.set(key, hit);
  return hit;
}

function compCacheSet(key, value) {
  compCache.set(key, value);
  while (compCache.size > COMP_CACHE_MAX) compCache.delete(compCache.keys().next().value);
}

function negotiateCompression(reqHeaders, headers, body, code, res, head = false, prepared = null) {
  const ae = (reqHeaders['accept-encoding'] || '').toLowerCase();
  const finish = (payload, encoding) => {
    if (encoding) headers['Content-Encoding'] = encoding;
    headers['Content-Length'] = String(payload.length);
    res.writeHead(code, headers);
    return head ? res.end() : res.end(payload);
  };
  if (body.length < 1024 || !COMPRESSIBLE.test(headers['Content-Type'] || '')) return finish(body);

  const wantBr = ae.includes('br');
  const wantGzip = !wantBr && ae.includes('gzip');
  if (!wantBr && !wantGzip) return finish(body);

  const enc = wantBr ? 'br' : 'gzip';
  if (prepared && prepared[enc]) return finish(prepared[enc], enc);

  // 1. identical-body cache
  const cacheable = body.length <= COMP_CACHE_MAX_BYTES;
  let key = null;
  if (cacheable) {
    key = enc + ':' + crypto.createHash('sha1').update(body).digest('base64');
    const hit = compCacheGet(key);
    if (hit) return finish(hit, enc);
  }

  // 2. in-flight ceiling — shed to identity instead of queueing native contexts
  if (compInflight >= COMP_MAX_INFLIGHT) return finish(body);

  compInflight++;
  const done = (err, cmp) => {
    compInflight--;
    if (err || !cmp) return finish(body);
    if (key) compCacheSet(key, cmp);
    return finish(cmp, enc);
  };
  if (wantBr) {
    zlib.brotliCompress(body, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 4 } }, done);
  } else {
    zlib.gzip(body, { level: 6 }, done);
  }
}

const staticCache = new Map();
const ROOT_PUBLIC_ALLOW = new Set([
  'index.html', 'app.js', 'style.css', 'manifest.webmanifest', 'sw.js',
  'robots.txt', 'sitemap.xml', 'favicon.svg', 'icon-192.png', 'icon-512.png',
  'hls.min.js',
]);
function cachedStatic(file, stat) {
  const stamp = `${stat.size}:${stat.mtimeMs}`;
  const old = staticCache.get(file);
  if (old && old.stamp === stamp) return old;
  const raw = fs.readFileSync(file);
  const value = {
    stamp, raw,
    br: raw.length >= 1024 ? zlib.brotliCompressSync(raw, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 4 } }) : null,
    gzip: raw.length >= 1024 ? zlib.gzipSync(raw, { level: 6 }) : null,
  };
  staticCache.set(file, value);
  return value;
}

function serveStatic(res, req, pathname) {
  let clean;
  try { clean = decodeURIComponent(pathname).replace(/^\/+/, '') || 'index.html'; }
  catch (e) { return false; }
  if (clean.includes('\0')) return false;
  const root = path.resolve(PUBLIC_DIR);
  const file = path.resolve(root, clean);
  if (file !== root && !file.startsWith(root + path.sep)) {
    sendJson(res, 403, { error: 'forbidden' }, req.headers, { head: req.method === 'HEAD' });
    return true;
  }
  if (PUBLIC_DIR === __dirname && !ROOT_PUBLIC_ALLOW.has(clean.replace(/\\/g, '/'))) return false;
  const ext = path.extname(file).toLowerCase();
  if (!MIME[ext]) return false;
  try {
    const stat = fs.statSync(file);
    if (!stat.isFile()) return false;
    const entry = cachedStatic(file, stat);
    const etag = `W/\"${entry.stamp}\"`;
    const cacheControl = ext === '.html'
      ? 'no-cache'
      : /^(?:app\.js|style\.css|sw\.js)$/.test(path.basename(file))
        ? 'public, max-age=3600, must-revalidate'
        : 'public, max-age=86400';
    const headers = securityHeaders({
      'Content-Type': MIME[ext],
      'Cache-Control': cacheControl,
      ETag: etag,
      Vary: 'Accept-Encoding',
    });
    if (req.headers['if-none-match'] === etag) {
      res.writeHead(304, headers);
      res.end();
      return true;
    }
    negotiateCompression(req.headers, headers, entry.raw, 200, res, req.method === 'HEAD', entry);
    return true;
  } catch (e) { return false; }
}

function cachePolicyFor(pathname) {
  if (['/api/health', '/api/ping', '/api/online', '/api/stats', '/api/geo', '/api/cache/clear', '/api/selftest'].includes(pathname)) return 'no-store';
  if (pathname.startsWith('/api/search') || pathname.startsWith('/api/anime/search')) return 'private, max-age=30, stale-while-revalidate=120';
  return 'private, max-age=60, stale-while-revalidate=300';
}

/* ---------------- server ---------------- */
const server = http.createServer(async (req, res) => {
  let u;
  try { u = new URL(req.url, 'http://localhost'); }
  catch (e) { return sendJson(res, 400, { error: 'bad url' }, req.headers); }
  const pathname = u.pathname.replace(/\/+$/, '') || '/';

  try {
    if (req.method === 'OPTIONS') {
      res.writeHead(204, securityHeaders({ Allow: 'GET, HEAD, OPTIONS', 'Cache-Control': 'no-store' }));
      return res.end();
    }

    if (pathname === '/api/hls/remix') {
      const retryAfter = rateLimit(req, 'hls');
      if (retryAfter) return sendJson(res, 429, { error: 'stream request limit reached' }, req.headers, { headers: { 'Retry-After': String(retryAfter) } });
      return hlsRemix(req, res, u);
    }

    if (pathname === '/api/hls') {
      const retryAfter = rateLimit(req, 'hls');
      if (retryAfter) return sendJson(res, 429, { error: 'stream request limit reached' }, req.headers, { headers: { 'Retry-After': String(retryAfter) } });
      return hlsProxy(req, res, u);
    }

    // Downloads are long-lived responses that stitch a whole episode, so they
    // bypass the JSON route table and the short API rate bucket entirely.
    if (pathname === '/api/download/info') {
      const retryAfter = rateLimit(req, 'api');
      if (retryAfter) return sendJson(res, 429, { error: 'request limit reached' }, req.headers, { headers: { 'Retry-After': String(retryAfter) } });
      return downloader.info(req, res, u);
    }
    if (pathname === '/api/download') {
      if (req.method !== 'GET' && req.method !== 'HEAD') {
        res.writeHead(405, securityHeaders({ Allow: 'GET, HEAD' }));
        return res.end();
      }
      const retryAfter = rateLimit(req, 'hls');
      if (retryAfter) return sendJson(res, 429, { error: 'download limit reached' }, req.headers, { headers: { 'Retry-After': String(retryAfter) } });
      stats.downloads = (stats.downloads || 0) + 1;
      return downloader.download(req, res, u);
    }

    const handler = routes[pathname];
    if (handler) {
      if (req.method !== 'GET' && req.method !== 'HEAD') {
        return sendJson(res, 405, { error: 'method not allowed' }, req.headers, { headers: { Allow: 'GET, HEAD' } });
      }
      const retryAfter = rateLimit(req, pathname === '/api/ping' ? 'ping' : 'api');
      if (retryAfter) return sendJson(res, 429, { error: 'request limit reached' }, req.headers, { headers: { 'Retry-After': String(retryAfter) } });
      stats.requests++;
      stats.top[pathname] = (stats.top[pathname] || 0) + 1;
      const data = await handler(u.searchParams, req);
      return sendJson(res, 200, data, req.headers, { cacheControl: cachePolicyFor(pathname), head: req.method === 'HEAD' });
    }

    if (pathname === '/favicon.ico') {
      const body = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><rect width="64" height="64" rx="14" fill="#e50914"/><path d="M26 20l18 12-18 12z" fill="white"/></svg>';
      const headers = securityHeaders({ 'Content-Type': 'image/svg+xml', 'Cache-Control': 'public, max-age=86400', 'Content-Length': String(Buffer.byteLength(body)) });
      res.writeHead(200, headers);
      return req.method === 'HEAD' ? res.end() : res.end(body);
    }

    if ((req.method === 'GET' || req.method === 'HEAD') && serveStatic(res, req, pathname)) return;
    return sendJson(res, 404, { error: 'not found' }, req.headers, { head: req.method === 'HEAD' });
  } catch (err) {
    const status = err && err.status ? err.status : 502;
    if (status >= 500) console.error(`[error] ${pathname} → ${status}: ${err.message}`);
    return sendJson(res, status, { error: err.message || 'server error' }, req.headers, { head: req.method === 'HEAD' });
  }
});

server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;
server.requestTimeout = 30000;
server.listen(PORT, HOST, () => {
  console.log(`StreamVerse v${VERSION} → http://${HOST}:${PORT}`);
  console.log(`Static: ${PUBLIC_DIR}`);
  console.log(`TMDB: ${TMDB_KEY ? 'configured' : 'missing (set TMDB_KEY)'}`);
  startKeepAlive();
  startBreakerHealer();
  prewarmAnime();
});

/* ---------------- breaker self-healing prober ----------------
   A tripped breaker used to stay tripped: `fails` was never reset, so the
   first request after the 5-minute cool-off re-opened it for another 5.
   Half-open handling fixes the stuck state, but users still paid a full
   cool-off after the upstream recovered. This prober checks any OPEN breaker
   in the background with one cheap request and closes it the moment the
   upstream answers, so a domain/API outage heals itself without a redeploy. */
const BREAKER_PROBES = {
  anilist: async () => {
    const d = await jfetch(ANILIST, {
      method: 'POST',
      body: JSON.stringify({ query: '{Page(page:1,perPage:1){media(type:ANIME){id}}}' }),
      headers: { 'Content-Type': 'application/json' },
      timeout: 6000, retries: 0,
    });
    if (!d || !d.data || !d.data.Page) throw new Error('anilist probe: unexpected payload');
    return true;
  },
};
function startBreakerHealer() {
  if (process.env.BREAKER_HEAL === 'off') return;
  const everyMs = Math.max(Number(process.env.BREAKER_HEAL_SECONDS) || 60, 20) * 1000;
  const timer = setInterval(async () => {
    for (const [name, probe] of Object.entries(BREAKER_PROBES)) {
      const b = breakers.get(name);
      if (!b || b.openUntil <= Date.now()) continue;
      try {
        await probe();
        breakerOk(name);
        apiHealth[name] = 'ok';
        console.log('[breaker] ' + name + ' recovered early - circuit closed');
      } catch (e) { /* still down; the cool-off keeps protecting us */ }
    }
  }, everyMs);
  if (timer.unref) timer.unref();
}

/* A cold instance has an empty cache, so the very first anime visitor pays the
   full Jikan round-trip - and if Jikan 429s (shared egress IP on Render) there
   is no stale entry to fall back on and the grid shows
   "Could not load. Try again.". Warming the few keys the anime tab opens with
   means there is always something to serve. Spaced out so we never burst. */
function prewarmAnime() {
  if (process.env.PREWARM === '0') return;
  // These MUST be byte-identical to the paths the routes build, otherwise the
  // warmed entry lands under a different cache key and does nothing.
  const jobs = [
    () => jikan('/top/anime?page=1'),
    () => jikan('/genres/anime', 24 * 60 * 60 * 1000),
    () => jikan('/top/anime?filter=airing&page=1'),
    () => jikan('/top/anime?page=2'),
    () => jikan('/anime?genres=1&order_by=members&sort=desc&sfw=true&page=1'),
  ];
  jobs.forEach((job, i) => {
    const t = setTimeout(() => {
      Promise.resolve().then(job)
        .then(() => console.log('[prewarm] anime key ' + (i + 1) + '/' + jobs.length + ' ok'))
        .catch((e) => console.warn('[prewarm] anime key ' + (i + 1) + ' failed: ' + e.message));
    }, 1500 + i * 1200);
    if (t.unref) t.unref();
  });
}

/* Free hosting tiers (Render free, Koyeb, Back4app) suspend a service after
   ~15 minutes with no inbound traffic, and the next visitor then waits 30-60s
   for a cold start. Pinging our own public URL keeps the instance warm.
   Opt-in: set KEEPALIVE_URL to the app's public https URL. Render and Koyeb
   both expose that automatically, so it usually needs no configuration.
   A ping is only worth doing when the host actually sleeps, hence the
   explicit env rather than always-on. */
function startKeepAlive() {
  const url =
    process.env.KEEPALIVE_URL ||
    process.env.RENDER_EXTERNAL_URL ||
    (process.env.KOYEB_PUBLIC_DOMAIN ? `https://${process.env.KOYEB_PUBLIC_DOMAIN}` : '');
  if (!url || process.env.KEEPALIVE === 'off') return;

  const target = url.replace(/\/+$/, '') + '/api/health';
  const everyMs = Math.max(Number(process.env.KEEPALIVE_MINUTES) || 12, 5) * 60 * 1000;
  console.log(`Keep-alive: pinging ${target} every ${Math.round(everyMs / 60000)} min`);

  const timer = setInterval(() => {
    const ctrl = new AbortController();
    const bail = setTimeout(() => ctrl.abort(), 10000);
    fetch(target, { signal: ctrl.signal, headers: { 'User-Agent': 'streamverse-keepalive' } })
      .catch(() => { /* a failed ping is not worth logging every 12 min */ })
      .finally(() => clearTimeout(bail));
  }, everyMs);
  timer.unref?.();
}

function shutdown(signal) {
  console.log(`${signal}: closing server`);
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(1), 8000).unref();
}
process.once('SIGTERM', () => shutdown('SIGTERM'));
process.once('SIGINT', () => shutdown('SIGINT'));

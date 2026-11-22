// PLASMA.io — server multigiocatore autoritativo
// Avvio: node server.js  (porta da process.env.PORT, default 3000)
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const CLIENT = path.join(__dirname, 'index.html');

// ---------- dati condivisi letti dal client (una sola fonte di verità) ----------
const SRC = fs.readFileSync(CLIENT, 'utf8');
function grab(name) {
  const i = SRC.indexOf('const ' + name + '=');
  if (i < 0) throw new Error('manca ' + name);
  let depth = 0, j = SRC.indexOf('=', i) + 1, started = false;
  for (; j < SRC.length; j++) {
    const c = SRC[j];
    if (c === '[' || c === '{') { depth++; started = true; }
    else if (c === ']' || c === '}') { depth--; if (started && depth === 0) { j++; break; } }
  }
  return new Function('return ' + SRC.slice(SRC.indexOf('=', i) + 1, j))();
}
const SHOP = grab('SHOP'), MODELS = grab('MODELS'), NAMES = grab('NAMES'), PERS = grab('PERS'), COLORS = grab('COLORS');
const MODEL_BY_ID = Object.fromEntries(MODELS.map(m => [m.id, m]));
const SHOP_IDS = new Set(SHOP.map(s => s.id));
const rarityOf = it => it.price >= 5.5 ? 'M' : it.price >= 3.4 ? 'L' : it.price >= 2.4 ? 'E' : it.price > 0 ? 'R' : '';
const PERK_TIER = { skin: { R: 3, E: 5, L: 6, M: 8 }, hilt: { R: 3, E: 5, L: 6, M: 8 }, trail: { R: 2, E: 3, L: 4, M: 5 }, kill: { R: 5, E: 8, L: 10, M: 12 } };
const PCT = {}; for (const it of SHOP) { const r = rarityOf(it); PCT[it.id] = r ? PERK_TIER[it.cat][r] : 0; }

// ---------- costanti di gioco (identiche al client) ----------
const WORLD = 4200, PELLETS = 750, TAU = Math.PI * 2, MAX_HUMANS = 24, MIN_ENTITIES = 18, MIN_BOTS = 4;
const rnd = (a, b) => a + Math.random() * (b - a), clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const angDiff = (a, b) => { let d = (a - b) % TAU; if (d > Math.PI) d -= TAU; if (d < -Math.PI) d += TAU; return d; };
const radius = m => 12 + Math.sqrt(m) * 2.4;
const bladeLen = p => (radius(p.m) * 1.5 + 40) * p.model.len * (1 + (PCT[p.hiltS] || 0) / 100);
const bladeW = p => (4 + radius(p.m) * .08) * p.model.w;
const r1 = v => Math.round(v * 10) / 10, r3 = v => Math.round(v * 1000) / 1000;

function segPointD2(ax, ay, bx, by, px, py) { const dx = bx - ax, dy = by - ay, l2 = dx * dx + dy * dy; let t = l2 ? ((px - ax) * dx + (py - ay) * dy) / l2 : 0; t = clamp(t, 0, 1); const qx = ax + dx * t - px, qy = ay + dy * t - py; return [qx * qx + qy * qy, ax + dx * t, ay + dy * t]; }
function segSegD2(a, b) {
  const ccw = (ax, ay, bx, by, cx, cy) => (cy - ay) * (bx - ax) - (by - ay) * (cx - ax);
  const d1 = ccw(b[0], b[1], b[2], b[3], a[0], a[1]), d2 = ccw(b[0], b[1], b[2], b[3], a[2], a[3]), d3 = ccw(a[0], a[1], a[2], a[3], b[0], b[1]), d4 = ccw(a[0], a[1], a[2], a[3], b[2], b[3]);
  if (((d1 > 0) !== (d2 > 0)) && ((d3 > 0) !== (d4 > 0))) { const t = d1 / (d1 - d2); return [0, a[0] + (a[2] - a[0]) * t, a[1] + (a[3] - a[1]) * t]; }
  let best = [1e18, 0, 0]; for (const [s, px, py] of [[b, a[0], a[1]], [b, a[2], a[3]], [a, b[0], b[1]], [a, b[2], b[3]]]) { const q = segPointD2(s[0], s[1], s[2], s[3], px, py); if (q[0] < best[0]) best = q; } return best;
}
const segsOf = bl => { const s = []; for (const pts of bl) for (let i = 0; i < pts.length - 1; i++) s.push([pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1]]); return s; };


// ================= ACCOUNT, ECONOMIA E PAGAMENTI (tutto lato server) =================
const QDEF = grab('QDEF'), PACKS = grab('PACKS');
const cyrb53 = (str, seed = 7) => { let h1 = 0xdeadbeef ^ seed, h2 = 0x41c6ce57 ^ seed; for (let i = 0, ch; i < str.length; i++) { ch = str.charCodeAt(i); h1 = Math.imul(h1 ^ ch, 2654435761); h2 = Math.imul(h2 ^ ch, 1597334677); } h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507); h1 ^= Math.imul(h2 ^ (h2 >>> 13), 3266489909); h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507); h2 ^= Math.imul(h1 ^ (h1 >>> 13), 3266489909); return 4294967296 * (2097151 & h2) + (h1 >>> 0); };
const OWNER_H = 2121273334490870; // hash del codice owner (il codice vero non e' nel repository)
const usdOf = it => Math.round(it.price * 500 / 50) * 50;
const levelOf = x => Math.floor(Math.sqrt((x || 0) / 120)) + 1;
const dayKey = () => { const d = new Date(new Date().toLocaleString('en-US', { timeZone: 'Europe/Rome' })); return d.getFullYear() + '-' + (d.getMonth() + 1) + '-' + d.getDate(); };
function seeded(s) { let x = (cyrb53(s) % 2147483646) + 1; return () => { x = x * 16807 % 2147483647; return x / 2147483647; }; }
function freshQuests() { const R = seeded('q' + dayKey()), pool = [...QDEF], pick = []; while (pick.length < 3) pick.push(pool.splice((R() * pool.length) | 0, 1)[0]); return { day: dayKey(), list: pick.map((d, i) => ({ t: d.t, n: d.ns[i], r: d.r[i], p: 0, c: false, ok: false })) }; }
const isUnlocked = (m, st) => !m.unlock || (m.unlock.kills && st.kills >= m.unlock.kills) || (m.unlock.mass && st.best >= m.unlock.mass);
const SHOP_BY_ID = Object.fromEntries(SHOP.map(s => [s.id, s]));

// ---- archivio: Postgres se c'e' DATABASE_URL, altrimenti file locale (solo per prove) ----
const store = (() => {
  const cache = new Map(), dirty = new Set();
  if (process.env.DATABASE_URL) {
    const { Pool } = require('pg');
    const pool = new Pool({ connectionString: process.env.DATABASE_URL.trim().replace(/([?&])channel_binding=[^&]*&?/, '$1').replace(/[?&]$/, ''), ssl: /localhost|127\.0\.0\.1/.test(process.env.DATABASE_URL) ? false : { rejectUnauthorized: false }, max: 4 });
    const ready = pool.query('CREATE TABLE IF NOT EXISTS plasma_accounts (id TEXT PRIMARY KEY, data JSONB NOT NULL, updated_at TIMESTAMPTZ NOT NULL DEFAULT now())').then(() => console.log('Database pronto'), e => console.error('Errore database:', e.message));
    return {
      kind: 'postgres', cache,
      async get(id) { if (cache.has(id)) return cache.get(id); await ready; const r = await pool.query('SELECT data FROM plasma_accounts WHERE id=$1', [id]); const a = r.rows[0] ? r.rows[0].data : null; if (a) cache.set(id, a); return a; },
      async put(a, now) { cache.set(a.id, a); if (!now) { dirty.add(a.id); return; } await ready; await pool.query('INSERT INTO plasma_accounts (id,data,updated_at) VALUES ($1,$2,now()) ON CONFLICT (id) DO UPDATE SET data=$2, updated_at=now()', [a.id, a]); dirty.delete(a.id); },
      async flush() { for (const id of [...dirty]) { const a = cache.get(id); if (a) await this.put(a, true).catch(e => console.error('salvataggio fallito', e.message)); } },
    };
  }
  const FILE = path.join(__dirname, 'accounts.json');
  let data = {}; try { data = JSON.parse(fs.readFileSync(FILE, 'utf8')); } catch (e) {}
  console.warn('ATTENZIONE: nessun DATABASE_URL, gli account vengono salvati in accounts.json (si perdono a ogni riavvio di Render)');
  return {
    kind: 'file', cache,
    async get(id) { return data[id] || null; },
    async put(a, now) { data[a.id] = a; dirty.add(a.id); if (now) await this.flush(); },
    async flush() { if (!dirty.size) return; dirty.clear(); fs.writeFile(FILE, JSON.stringify(data), () => {}); },
  };
})();
setInterval(() => store.flush(), 4000);

const newToken = () => 'PLA-' + crypto.randomBytes(15).toString('base64').replace(/[^A-Za-z0-9]/g, '').slice(0, 20).toUpperCase();
const idOf = token => crypto.createHash('sha256').update(String(token)).digest('hex').slice(0, 32);
function blankAccount(id) { return { id, created: Date.now(), usd: 0, owned: [], eq: { skin: 's_default', hilt: 'h_default', trail: 't_default', kill: 'k_default' }, stats: { kills: 0, best: 0, xp: 0 }, daily: '', quests: freshQuests(), owner: false, paid: [], pending: [] }; }
const ownsItem = (a, id) => { const it = SHOP_BY_ID[id]; return !!it && (a.owner || it.price === 0 || a.owned.includes(id)); };
function publicAcct(a) { if (a.quests.day !== dayKey()) a.quests = freshQuests(); return { usd: a.owner ? 0 : a.usd, owned: a.owned, eq: a.eq, stats: a.stats, quests: a.quests, owner: a.owner }; }
function pushAcct(ws) { if (ws && ws.acct) send(ws, { t: 'acct', d: publicAcct(ws.acct) }); }
function touch(ws) { if (ws && ws.acct) { store.put(ws.acct); pushAcct(ws); } }
function giveUsd(a, n) { if (!a.owner) a.usd = Math.max(0, Math.round(a.usd + n)); }
function questProg(ws, t, v, mode) {
  const a = ws && ws.acct; if (!a) return; if (a.quests.day !== dayKey()) a.quests = freshQuests();
  let changed = false;
  for (const q of a.quests.list) { if (q.t !== t || q.c) continue; const np = mode === 'max' ? Math.max(q.p, v) : q.p + v; if (np === q.p) continue; q.p = np; changed = true;
    if (!q.ok && q.p >= q.n) { q.ok = true; send(ws, { t: 'qdone', q: q.t, n: q.n }); pushAcct(ws); } }
  if (changed) store.put(a);
}

// ---- Stripe (solo lato server: la chiave segreta non arriva mai al browser) ----
const STRIPE_KEY = process.env.STRIPE_SECRET_KEY || '';
const STRIPE_TEST = /^(sk|rk)_test_/.test(STRIPE_KEY);
const PRICE_IDS = STRIPE_TEST
  ? { d500: 'price_1UeEeEHAmft5IIW8PY4sGPrp', d1100: 'price_1UeEeZHAmft5IIW86QuxCpWD', d3000: 'price_1UeEeaHAmft5IIW8bTCGf8p4', d6500: 'price_1UeEebHAmft5IIW83YBat9Sq', d14000: 'price_1UeEebHAmft5IIW8ADk31HOd' }
  : { d500: 'price_1UeJvNHVgMTUNb13KUYeADnS', d1100: 'price_1UeJvcHVgMTUNb13JtnTbJr7', d3000: 'price_1UeJvdHVgMTUNb13ZexhlQvV', d6500: 'price_1UeJvdHVgMTUNb13kWIaFLfr', d14000: 'price_1UeJveHVgMTUNb13JzPqtwSh' };
function formEncode(obj, prefix, out = []) { for (const [k, v] of Object.entries(obj)) { const key = prefix ? `${prefix}[${k}]` : k; if (v && typeof v === 'object') formEncode(v, key, out); else out.push(encodeURIComponent(key) + '=' + encodeURIComponent(v)); } return out.join('&'); }
async function stripe(method, pathname, params) {
  const res = await fetch((process.env.STRIPE_API || 'https://api.stripe.com') + '/v1/' + pathname + (method === 'GET' && params ? '?' + formEncode(params) : ''), {
    method, headers: { Authorization: 'Bearer ' + STRIPE_KEY, 'Content-Type': 'application/x-www-form-urlencoded' }, body: method === 'GET' ? undefined : formEncode(params || {}) });
  const j = await res.json(); if (!res.ok) throw new Error((j.error && j.error.message) || ('Stripe ' + res.status)); return j;
}
const creditLocks = new Set();
async function verifySession(a, sid, ws) {
  if (!STRIPE_KEY || !/^cs_(test|live)_[A-Za-z0-9]+$/.test(sid) || a.paid.includes(sid) || creditLocks.has(sid)) return 0;
  creditLocks.add(sid);
  try {
    const s = await stripe('GET', 'checkout/sessions/' + sid);
    if (s.payment_status !== 'paid' || s.client_reference_id !== a.id) return 0;
    if (a.paid.includes(sid)) return 0;
    const pk = PACKS.find(p => p.id === (s.metadata && s.metadata.pack)); if (!pk) return 0;
    a.paid.push(sid); a.pending = a.pending.filter(x => x !== sid); a.usd += pk.usd;
    await store.put(a, true);
    console.log('Pagamento accreditato', a.id.slice(0, 8), pk.id, sid.slice(0, 18));
    if (ws) { send(ws, { t: 'credited', n: pk.usd }); pushAcct(ws); }
    return pk.usd;
  } catch (e) { console.error('verifica pagamento', e.message); return 0; } finally { creditLocks.delete(sid); }
}
async function checkPending(a, ws) {
  for (const sid of [...a.pending]) await verifySession(a, sid, ws);
  // le sessioni scadono dopo 24 ore: tieni solo le ultime
  if (a.pending.length > 20) a.pending = a.pending.slice(-20);
}

// ---------- arena ----------
let NEXT_ID = 1;
class Arena {
  constructor(id) {
    this.id = id; this.tick = 0; this.players = []; this.orbs = new Map(); this.orbId = 1; this.grid = new Map(); this.moving = new Set(); this.timed = new Set(); this.pellets = 0;
    this.clients = new Set(); this.events = []; this.orbAdds = []; this.orbRems = [];
    this.storm = { on: false, x: 0, y: 0, R: 360, t: 0, next: 2400 };
    for (let i = 0; i < PELLETS; i++) this.pellet(true);
    this.balanceBots(true);
  }
  humans() { return this.players.filter(p => !p.bot); }
  // ---- orbs ----
  addOrb(x, y, v, col, vx = 0, vy = 0, life = 0, silent) {
    const o = { id: this.orbId++, x, y, v, col, vx, vy, life, r: 3 + Math.sqrt(v) * 1.6, cell: -1 };
    this.orbs.set(o.id, o); if (!silent) this.orbAdds.push(o);
    if (vx || vy) this.moving.add(o); else this.gridAdd(o);
    if (life) this.timed.add(o); if (v === 1 && !life) this.pellets++;
    return o;
  }
  // griglia spaziale persistente delle particelle (aggiornata solo quando cambiano)
  gridAdd(o) { const k = ((o.x / 160) | 0) * 64 + ((o.y / 160) | 0); o.cell = k; let c = this.grid.get(k); if (!c) this.grid.set(k, c = []); c.push(o); }
  gridDel(o) { if (o.cell < 0) return; const c = this.grid.get(o.cell); if (c) { const i = c.indexOf(o); if (i >= 0) { c[i] = c[c.length - 1]; c.pop(); } } o.cell = -1; }
  removeOrb(o, by) { if (o.dead) return; o.dead = true; this.orbs.delete(o.id); this.gridDel(o); this.moving.delete(o); this.timed.delete(o); if (o.v === 1 && !o.life) this.pellets--; this.orbRems.push([o.id, by]); }
  pellet(silent) { this.addOrb(rnd(20, WORLD - 20), rnd(20, WORLD - 20), 1, (Math.random() * 7) | 0, 0, 0, 0, silent); }
  dropMass(x, y, amount, col) { let left = amount; const piece = Math.max(4, amount / 22); while (left > .5) { const v = Math.min(left, piece * rnd(.7, 1.3)); left -= v; const a = rnd(0, TAU), s = rnd(1.5, 6); this.addOrb(x + rnd(-6, 6), y + rnd(-6, 6), v, col, Math.cos(a) * s, Math.sin(a) * s, 1800); } }
  // ---- giocatori ----
  newPlayer(name, bot) {
    return { id: NEXT_ID++, name, bot, x: 0, y: 0, vx: 0, vy: 0, m: 20, a: 0, aPrev: 0, aim: 0, aimT: 0, av: 0, omega: 0, model: MODELS[0], col: COLORS[0], alive: false, kills: 0, best: 20, born: 0, dashT: 0, dashCd: 0, stun: 0, hitCd: new Map(), mx: 0, my: 0, respawn: 0, counter: 0, steady: 0,
      react: 10, iq: .5, hand: .12, pat: 80, reactT: 0, mode: 'guard', modeT: 0, circ: 1, target: null, th: null, block: null, wx: 0, wy: 0, aimNoise: 0, skin: 's_default', hiltS: 'h_default', trailS: 't_default', kfx: 'k_default', lv: 1 };
  }
  botCosmetics(b) { const pick = (cat, pr) => { if (Math.random() > pr) return SHOP.find(s => s.cat === cat && s.price === 0).id; const L2 = SHOP.filter(s => s.cat === cat && s.price > 0); return L2[(Math.random() * L2.length) | 0].id; }; b.skin = pick('skin', .3); b.hiltS = pick('hilt', .25); b.trailS = pick('trail', .2); b.kfx = pick('kill', .2); }
  setPersonality(b) { let r = Math.random(), P = PERS[0]; for (const q of PERS) { if (r < q.p) { P = q; break; } r -= q.p; } b.react = rnd(...P.react) | 0; b.iq = rnd(...P.iq); b.hand = rnd(...P.hand); b.pat = rnd(...P.pat) | 0; b.circ = Math.random() < .5 ? 1 : -1;
    b.react0 = b.react;
    // carattere: coraggio (sfida chi e' piu' grande), pentimento (a meta' attacco ci ripensa), arroganza (ignora i piccolissimi)
    const c = Math.random(); b.courage = c < .3 ? rnd(.7, 1) : c < .8 ? rnd(.35, .7) : rnd(0, .35);
    b.regret = Math.random() < .4 ? rnd(.3, .8) : rnd(0, .2); b.arrog = rnd(0, 1); b.scared = 0; b.scaredOf = null; }
  botModel() { const w = [40, 15, 12, 14, 8, 7, 4]; let r = Math.random() * 100; for (let i = 0; i < w.length; i++) { if (r < w[i]) return MODELS[i]; r -= w[i]; } return MODELS[0]; }
  rollBot(b) { b.name = NAMES[(Math.random() * NAMES.length) | 0]; b.col = COLORS[(Math.random() * 7) | 0]; b.model = this.botModel(); this.setPersonality(b); this.botCosmetics(b); b.lv = 1 + ((Math.random() ** 1.6) * 40 | 0); }
  spawn(p, m = 20) {
    let best = [WORLD / 2, WORLD / 2], bs = -1e9;
    for (let t = 0; t < 40; t++) { const x = rnd(220, WORLD - 220), y = rnd(220, WORLD - 220); let md = 1e9;
      for (const o of this.players) { if (!o.alive || o === p) continue; let d = Math.hypot(o.x - x, o.y - y) - bladeLen(o) - radius(o.m); if (!o.bot) d -= 600; if (d < md) md = d; }
      if (md > bs) { bs = md; best = [x, y]; } if (bs > 700) break; }
    Object.assign(p, { x: best[0], y: best[1], vx: 0, vy: 0, m, alive: true, kills: 0, best: m, born: this.tick, dashT: 0, dashCd: 0, stun: 0, streak: 0, a: rnd(0, TAU), av: 0, counter: 0, mode: 'guard', modeT: 0, target: null, th: null, block: null, steady: 0 });
    p.aPrev = p.a; p.aim = p.a; p.aimT = p.a; p.hitCd.clear(); p.ph = []; p.viewR = NaN;
    this.events.push(['sp', this.info(p)]);
  }
  info(p) { return { id: p.id, n: p.name, b: p.bot ? 1 : 0, c: p.col, md: p.model.id, s: p.skin, h: p.hiltS, t: p.trailS, k: p.kfx, lv: p.lv, x: r1(p.x), y: r1(p.y), a: r3(p.a), m: r1(p.m), born: p.born }; }
  balanceBots(initial) {
    const hum = this.humans().length, want = Math.max(MIN_BOTS, MIN_ENTITIES - hum);
    let bots = this.players.filter(p => p.bot);
    while (bots.length < want) { const b = this.newPlayer('', true); this.rollBot(b); this.players.push(b); this.spawn(b, Math.random() < .5 ? rnd(20, 60) : rnd(60, 200)); if (initial) b.born = -999; bots.push(b); }
    // rimuove bot in eccesso (prima quelli morti)
    while (bots.length > want) { const b = bots.find(x => !x.alive) || bots[bots.length - 1]; this.removePlayer(b); bots = bots.filter(x => x !== b); }
  }
  removePlayer(p) { const i = this.players.indexOf(p); if (i >= 0) this.players.splice(i, 1); if (p.alive) { p.alive = false; this.dropMass(p.x, p.y, p.m * .6, p.col); } this.events.push(['rm', p.id]); for (const o of this.players) { if (o.target === p) o.target = null; if (o.th === p) o.th = null; if (o.block === p) o.block = null; } }
  // ---- logica ----
  steer(p, mx, my) { const ml = Math.hypot(mx, my); if (ml > 1) { mx /= ml; my /= ml; } const sp = 4.3 * Math.pow(20 / p.m, .2) * (p.dashT > 0 ? 3 : 1) * (1 + (PCT[p.trailS] || 0) / 100); p.vx += (mx * sp - p.vx) * (p.dashT > 0 ? .35 : .16); p.vy += (my * sp - p.vy) * (p.dashT > 0 ? .35 : .16); }
  turnBlade(p) { p.aPrev = p.a; const tf = p.model.turn * Math.pow(20 / p.m, .16) * (p.stun > 0 ? .35 : 1); const d = angDiff(p.aim, p.a), maxW = .5 * tf; p.av = p.av * .5 + d * .27 * Math.min(1.25, tf); p.av = clamp(p.av, -maxW, maxW); p.a += p.av; p.omega = p.a - p.aPrev; }
  dash(p) { if (p.dashCd > 0 || p.m < 14 || !p.alive) return; p.m *= .97; p.dashT = 10; p.dashCd = 55; let dx = p.vx, dy = p.vy; const l = Math.hypot(dx, dy); if (l < .3) { dx = Math.cos(p.a); dy = Math.sin(p.a); } else { dx /= l; dy /= l; } p.vx = dx * 12; p.vy = dy * 12; this.events.push(['ds', p.id]); }
  bladesAt(p, x, y, a) {
    const ign = Math.min(1, Math.max(.05, (this.tick - p.born) / 22)), r = radius(p.m), Ln = bladeLen(p) * ign, h1 = r * 1.05, M = p.model, out = [];
    for (const d of M.dbl ? [a, a + Math.PI] : [a]) {
      const c = Math.cos(d), s = Math.sin(d), bx = x + c * h1, by = y + s * h1;
      if (M.shape === 'curve') { const pts = [[bx, by]]; let hx = bx, hy = by, hd = d; for (let i = 0; i < 3; i++) { hd += .16; hx += Math.cos(hd) * Ln / 3; hy += Math.sin(hd) * Ln / 3; pts.push([hx, hy]); } out.push(pts); }
      else if (M.shape === 'scythe') { const tx = bx + c * Ln * .82, ty = by + s * Ln * .82, hd = d + 2.25; out.push([[bx, by], [tx, ty], [tx + Math.cos(hd) * Ln * .42, ty + Math.sin(hd) * Ln * .42]]); }
      else out.push([[bx, by], [bx + c * Ln, by + s * Ln]]);
    }
    return out;
  }
  kill(p, att) {
    if (!p.alive) return;
    const king = this.king, wasKing = p === king, bountyPct = p.kills >= 3 ? Math.min(100, (p.kills - 2) * 25) : 0;
    const revenge = !!(att && !att.bot && att.nemId === p.id);
    p.alive = false;
    this.dropMass(p.x, p.y, p.m * .8 + 6 + (wasKing ? p.m * .4 : 0) + p.m * bountyPct / 100 + (revenge ? p.m * .5 : 0), p.col);
    if (att && att !== p && att.alive) { if (PCT[att.kfx]) att.m += p.m * PCT[att.kfx] / 100; att.kills++; if (revenge) att.nemId = null;
      if (att.ws && att.ws.acct) { const A = att.ws.acct; giveUsd(A, 5 + (revenge ? 5 : 0) + (bountyPct ? 5 : 0)); A.stats.kills++; A.stats.xp += 40 + (revenge ? 60 : 0) + (bountyPct ? 30 : 0); questProg(att.ws, 'kill', 1); touch(att.ws); } }
    if (!p.bot && p.ws && p.ws.acct) { const A = p.ws.acct, secs = (this.tick - p.born) / 60, mass = Math.floor(p.best / 50), time = Math.floor(secs / 30); giveUsd(A, mass + time); A.stats.xp += Math.round(p.best * .5); A.stats.best = Math.max(A.stats.best, Math.round(p.best)); p.earn = { mass, time }; touch(p.ws); }
    if (!p.bot && att && att !== p) p.nemId = att.id;
    this.events.push(['k', p.id, att ? att.id : 0, r1(p.x), r1(p.y), r1(p.m), r3(att ? att.a : rnd(0, TAU)), p.kills]);
    if (p.bot) p.respawn = 150 + (Math.random() * 150 | 0);
    else if (p.ws) send(p.ws, { t: 'dead', by: att ? att.id : 0, earn: p.earn || null });
  }
  clash(p, q, x, y) {
    if ((p.hitCd.get('c' + q.id) || 0) > this.tick) return; p.hitCd.set('c' + q.id, this.tick + 16); q.hitCd.set('c' + p.id, this.tick + 16);
    // lama molto piu' grande: travolge quella piccola, niente rimbalzo ne' blocco per il grande
    if (p.m >= q.m * 3 || q.m >= p.m * 3) { const big = p.m > q.m ? p : q, sm = big === p ? q : p; sm.a = sm.aPrev - sm.omega * 1.2; sm.av = -sm.av * .8; sm.stun = 14; const dx = sm.x - big.x, dy = sm.y - big.y, d = Math.hypot(dx, dy) || 1; sm.vx += dx / d * 4; sm.vy += dy / d * 4; this.events.push(['c', p.id, q.id, r1(x), r1(y), 0, 0]); return; }
    const vp = Math.abs(p.omega) * bladeLen(p), vq = Math.abs(q.omega) * bladeLen(q);
    p.a = p.aPrev - p.omega * .8; q.a = q.aPrev - q.omega * .8; p.av = -p.av * .6; q.av = -q.av * .6;
    const def = vp <= vq ? p : q, att = def === p ? q : p, vd = Math.min(vp, vq), va = Math.max(vp, vq);
    const perfect = (def.steady || 0) >= 8 && vd < 3 && va > 8;
    if (perfect) { att.stun = 26; def.stun = 0; def.counter = this.tick + 50; if (def.ws) questProg(def.ws, 'parry', 1); } else { p.stun = 3; q.stun = 3; }
    const dx = q.x - p.x, dy = q.y - p.y, d = Math.hypot(dx, dy) || 1; p.vx -= dx / d * 3; p.vy -= dy / d * 3; q.vx += dx / d * 3; q.vy += dy / d * 3;
    this.events.push(['c', p.id, q.id, r1(x), r1(y), perfect ? def.id : 0, perfect ? att.id : 0]);
  }
  combat() {
    const alive = this.players.filter(p => p.alive), segs = new Map(); for (const p of alive) segs.set(p, segsOf(this.bladesAt(p, p.x, p.y, p.a)));
    for (let i = 0; i < alive.length; i++) { const p = alive[i];
      for (let j = 0; j < alive.length; j++) { if (i === j) continue; const q = alive[j]; if (!p.alive) break;
        const reach = bladeLen(p) + radius(p.m) * 1.1 + radius(q.m) + 80;
        if (!q.alive || Math.abs(p.x - q.x) > reach || Math.abs(p.y - q.y) > reach) continue;
        if (i < j) { const w = (bladeW(p) + bladeW(q)) * .5 + 3; outer: for (const a of segs.get(p)) for (const b of segs.get(q)) { const [d2, x, y] = segSegD2(a, b); if (d2 < w * w) { this.clash(p, q, x, y); break outer; } } }
        if (p.stun > 0 || this.tick - q.born < 120) continue;
        const human = !p.bot, rq = radius(q.m) + bladeW(p) * .75 + (human ? 6 : 2);
        // compensazione del ritardo: per i giocatori umani controlla il nemico dove lo vedevano sul loro schermo
        let qx = q.x, qy = q.y;
        if (human && Number.isFinite(p.viewR) && q.ph) { const back = clamp(this.tick - p.viewR, 0, 14); if (back > 0) { const want = this.tick - back; for (let k = q.ph.length - 1; k >= 0; k--) if (q.ph[k][0] <= want) { qx = q.ph[k][1]; qy = q.ph[k][2]; break; } } }
        const hitAt = (sg, x, y) => { for (const a of sg) { const [d2] = segPointD2(a[0], a[1], a[2], a[3], x, y); if (d2 < rq * rq) return true; } return false; };
        let hit = hitAt(segs.get(p), q.x, q.y) || (qx !== q.x && hitAt(segs.get(p), qx, qy));
        // lama veloce: controlla anche le posizioni intermedie del colpo (niente "salti" sopra i nemici piccoli)
        if (!hit && Math.abs(p.omega) > .02) { const steps = Math.min(8, Math.ceil(Math.abs(p.omega) * (bladeLen(p) + radius(p.m)) / Math.max(8, rq))); for (let k = 1; k < steps && !hit; k++) { const sg = segsOf(this.bladesAt(p, p.x, p.y, p.a - p.omega * k / steps)); hit = hitAt(sg, q.x, q.y) || (qx !== q.x && hitAt(sg, qx, qy)); } }
        if (hit) this.kill(q, p);
      }
    }
    for (let i = 0; i < alive.length; i++) for (let j = i + 1; j < alive.length; j++) { const p = alive[i], q = alive[j]; if (!p.alive || !q.alive) continue; const dx = q.x - p.x, dy = q.y - p.y, rr = radius(p.m) + radius(q.m), d2 = dx * dx + dy * dy; if (d2 < rr * rr && d2 > 0) { const d = Math.sqrt(d2), o = (rr - d) / 2, nx = dx / d, ny = dy / d; p.x -= nx * o; p.y -= ny * o; q.x += nx * o; q.y += ny * o; } }
  }
  orbsNear(x, y, R, fn) { const g = this.grid; if (!g) return; const C = 160, x0 = Math.max(0, ((x - R) / C) | 0), x1 = ((x + R) / C) | 0, y0 = Math.max(0, ((y - R) / C) | 0), y1 = ((y + R) / C) | 0;
    for (let cx = x0; cx <= x1; cx++) for (let cy = y0; cy <= y1; cy++) { const c = g.get(cx * 64 + cy); if (c) for (const o of c) if (!o.dead) fn(o); }
    for (const o of this.moving) if (Math.abs(o.x - x) < R && Math.abs(o.y - y) < R) fn(o); }
  // il bottino (energia lasciata da un ucciso) e' sicuro se nessuno piu' grande puo' colpire il bot li'
  lootSafe(b, x, y) { const r = radius(b.m); for (const o of this.players) { if (!o.alive || o === b || o.m < b.m * .9) continue; if (Math.hypot(o.x - x, o.y - y) < bladeLen(o) + radius(o.m) + r + 90) return false; } return true; }
  botThink(b) {
    const r = radius(b.m), Ln = bladeLen(b), dumb = b.iq < .35, tick = this.tick, players = this.players;
    if (--b.reactT <= 0) {
      // tempo di reazione variabile per tutti: a volte pronti, a volte distratti
      if (Math.random() < .05) b.react = clamp(Math.round(b.react0 * rnd(.7, 1.5)), 3, 40);
      b.reactT = Math.max(2, Math.round(b.react * rnd(.5, 1.8) * (Math.random() < .07 ? 2.5 : 1)));
      const courage = b.courage ?? .5, fleeRatio = 1.4 + courage * 2.6, huntRatio = 1.25 + courage * 2.2, ignoreRatio = 3 + (1 - (b.arrog ?? .5)) * 4;
      let th = null, td = 1e9, pr = null, pd = 1e9;
      for (const o of players) { if (!o.alive || o === b) continue; const d = Math.hypot(o.x - b.x, o.y - b.y), reach = bladeLen(o) + radius(o.m);
        // paura: solo chi e' MOLTO piu' grande (dipende dal coraggio), oppure chi ci ha appena fatto pentire
        if ((!dumb || Math.random() < .4) && ((o.m > b.m * fleeRatio) || (b.scared > tick && b.scaredOf === o)) && d < reach + r + 200 && d < td) { th = o; td = d; }
        // preda: anche piu' grande di noi se siamo coraggiosi; i giganti ignorano i piccolissimi finche' non si avvicinano troppo
        const tiny = b.m > o.m * ignoreRatio && d > r + Ln * .6;
        if (o.m < b.m * huntRatio && !tiny && d < 450 + 350 * b.iq && d < pd && tick - o.born > 150) { pr = o; pd = d; } }
      b.th = th; if (pr !== b.target) { b.target = pr; b.mode = 'guard'; b.modeT = 0; }
      b.block = null;
      if (!dumb) for (const o of players) { if (!o.alive || o === b) continue; const d = Math.hypot(o.x - b.x, o.y - b.y); if (d > bladeLen(o) + r + 30) continue;
        if (Math.abs(o.omega || 0) * bladeLen(o) > 7 && Math.random() < b.iq * .6) { b.block = o; break; } }
      b.aimNoise = rnd(-1, 1) * (1 - b.iq) * .5;
      // bottino: energia dei nemici uccisi nelle vicinanze, se andarci e' sicuro
      b.loot = null;
      if (!th) { let bx = 0, by = 0, bv = 0, best = -1; this.orbsNear(b.x, b.y, 950, o => { if (!o.life || o.v < 2) return; const d = Math.hypot(o.x - b.x, o.y - b.y); if (d > 950) return; const sc = o.v / (d + 150); if (sc > best) { best = sc; bx = o.x; by = o.y; } bv += o.v; });
        if (bv >= 8 && best > 0 && this.lootSafe(b, bx, by)) b.loot = { x: bx, y: by }; }
      if (!pr && !th) { let best = null, bd = 1e12; this.orbsNear(b.x, b.y, 520, o => { const dx = o.x - b.x, dy = o.y - b.y; if (dx > 520 || dx < -520 || dy > 520 || dy < -520) return; const d = (dx * dx + dy * dy) / (o.v + 1); if (d < bd) { bd = d; best = o; } });
        const st = this.storm;
        if (st.on && Math.hypot(st.x - b.x, st.y - b.y) < 1600 && Math.random() < .6) { b.wx = st.x + rnd(-150, 150); b.wy = st.y + rnd(-150, 150); } else if (best) { b.wx = best.x; b.wy = best.y; } else if (!b.wx || Math.hypot(b.wx - b.x, b.wy - b.y) < 80) { b.wx = rnd(300, WORLD - 300); b.wy = rnd(300, WORLD - 300); } }
    }
    let mx = 0, my = 0; const th = b.th, pr = b.target;
    if (th && th.alive) { const dx = b.x - th.x, dy = b.y - th.y, d = Math.hypot(dx, dy) || 1; mx = dx / d; my = dy / d; b.aimT = Math.atan2(-dy, -dx);
      if (d < bladeLen(th) + radius(th.m) + r + 20 && b.iq > .5 && Math.random() < .02) this.dash(b); }
    else if (b.loot && (!pr || !pr.alive || Math.hypot(pr.x - b.x, pr.y - b.y) > Math.hypot(b.loot.x - b.x, b.loot.y - b.y) * .6)) {
      mx = b.loot.x - b.x; my = b.loot.y - b.y; const l = Math.hypot(mx, my); if (l < 25) b.loot = null; else { mx /= l; my /= l; b.aimT = Math.atan2(my, mx) + b.aimNoise * .5; } }
    else if (pr && pr.alive) {
      const dx = pr.x - b.x, dy = pr.y - b.y, d = Math.hypot(dx, dy) || 1, ang = Math.atan2(dy, dx), rq = radius(pr.m);
      const guardD = Ln + r + rq + 22 + (1 - b.iq) * 20;
      b.modeT++;
      if (dumb) { const pointed = Math.abs(angDiff(pr.a, Math.atan2(-dy, -dx))) < .55 && d < bladeLen(pr) + r + rq + 90;
        if (pointed) { mx = -dx / d * .7 + (-dy / d) * .5 * b.circ; my = -dy / d * .7 + (dx / d) * .5 * b.circ; } else { mx = dx / d; my = dy / d; }
        b.aimT = ang + b.aimNoise; }
      else if (b.mode === 'guard') {
        if (d > guardD + 15) { mx = dx / d; my = dy / d; } else if (d < guardD - 15) { mx = -dx / d; my = -dy / d; }
        mx += -dy / d * .45 * b.circ; my += dx / d * .45 * b.circ;
        b.aimT = ang + b.aimNoise * .5;
        const theirFacing = Math.abs(angDiff(pr.a, Math.atan2(-dy, -dx)));
        const opening = pr.stun > 0 || (theirFacing > 1.1 && !pr.model.dbl) || b.counter > tick;
        if ((opening && b.modeT > 12) || b.modeT > b.pat * (1.3 - (b.courage || 0) * .8)) { b.mode = 'strike'; b.modeT = 0; if (b.iq > .6 && b.m > 30 && d < guardD + 60 && Math.random() < .4) this.dash(b); }
        if (Math.random() < .004) b.circ *= -1;
      } else if (b.mode === 'strike') { mx = dx / d; my = dy / d; b.aimT = ang + Math.sin(b.modeT * .25) * .35 * b.circ;
        // pentimento: attaccando qualcuno piu' grande, alcuni ci ripensano e scappano
        if (pr.m > b.m * 1.1 && Math.random() < (b.regret || 0) * .035) { b.mode = 'back'; b.modeT = 0; b.scared = tick + 90 + ((Math.random() * 120) | 0); b.scaredOf = pr; b.target = null; if (Math.random() < .5) this.dash(b); }
        else if (b.modeT > 28 + b.react + (b.courage || 0) * 30) { b.mode = 'back'; b.modeT = 0; } }
      else { mx = -dx / d; my = -dy / d; b.aimT = ang; if (b.modeT > 20 + b.react || d > guardD + 30) { b.mode = 'guard'; b.modeT = 0; } }
    } else { mx = b.wx - b.x; my = b.wy - b.y; const l = Math.hypot(mx, my); if (l > 1) b.aimT = Math.atan2(my, mx); }
    if (b.block && b.block.alive) { const s = segsOf(this.bladesAt(b.block, b.block.x, b.block.y, b.block.a))[0]; b.aimT = Math.atan2((s[1] + s[3]) / 2 - b.y, (s[0] + s[2]) / 2 - b.x) + Math.sign(b.block.omega || 1) * .2; }
    b.aim += clamp(angDiff(b.aimT, b.aim), -b.hand, b.hand);
    if (b.x < 150) mx += 1; if (b.x > WORLD - 150) mx -= 1; if (b.y < 150) my += 1; if (b.y > WORLD - 150) my -= 1;
    b.mx = mx; b.my = my;
  }
  update() {
    this.tick++;
    for (const p of this.players) {
      if (!p.alive) { if (p.bot && --p.respawn <= 0) { this.rollBot(p); this.spawn(p, rnd(20, 45)); } continue; }
      if (p.bot) this.botThink(p);
      else { if (p.wantDash) { p.wantDash = false; this.dash(p); }
        if (p.ws && this.tick % 30 === 0) { questProg(p.ws, 'mass', p.m, 'max'); questProg(p.ws, 'time', (this.tick - p.born) / 3600, 'max'); if (p.eat) { questProg(p.ws, 'energy', p.eat); p.eat = 0; } } }
      this.steer(p, p.mx, p.my); p.x += p.vx; p.y += p.vy; const r = radius(p.m); p.x = clamp(p.x, r, WORLD - r); p.y = clamp(p.y, r, WORLD - r);
      if (p.bot || !Number.isFinite(p.ba)) this.turnBlade(p);
      else { // la lama dei giocatori umani segue quella che vedono sul loro schermo, con un limite di velocita' anti-imbroglio
        p.aPrev = p.a; const tf = p.model.turn * Math.pow(20 / p.m, .16) * (p.stun > 0 ? .35 : 1), maxW = .5 * tf * 1.25;
        const d = angDiff(p.ba, p.a); p.a += clamp(d, -maxW, maxW); p.omega = p.a - p.aPrev; p.av = p.omega; }
      p.steady = Math.abs(p.omega) * bladeLen(p) < 3 ? (p.steady || 0) + 1 : 0;
      if (p.dashT > 0) p.dashT--; if (p.dashCd > 0) p.dashCd--; if (p.stun > 0) p.stun--;
      if (p.m > 300) p.m -= (p.m - 300) * .00004;
      if (p.m > p.best) p.best = p.m;
      (p.ph || (p.ph = [])).push([this.tick, p.x, p.y]); if (p.ph.length > 20) p.ph.shift();
    }
    this.combat();
    const st = this.storm;
    if (!st.on && --st.next <= 0) { st.on = true; st.t = 900; st.x = rnd(500, WORLD - 500); st.y = rnd(500, WORLD - 500); this.events.push(['st', st.x | 0, st.y | 0]); }
    if (st.on) { if (--st.t <= 0) { st.on = false; st.next = (5400 + rnd(0, 1800)) | 0; this.events.push(['st0']); } else if (this.tick % 3 === 0) { const a = rnd(0, TAU), d = Math.sqrt(Math.random()) * st.R; this.addOrb(st.x + Math.cos(a) * d, st.y + Math.sin(a) * d, 3, 4, 0, 0, 1200); } }
    { let k = null; for (const p of this.players) if (p.alive && (!k || p.m > k.m)) k = p; this.king = k; }
    // energia: griglia spaziale persistente, ogni giocatore controlla solo le particelle vicine
    for (const o of this.moving) { o.x = clamp(o.x + o.vx, 4, WORLD - 4); o.y = clamp(o.y + o.vy, 4, WORLD - 4); o.vx *= .9; o.vy *= .9; if (Math.abs(o.vx) < .05 && Math.abs(o.vy) < .05) { o.vx = o.vy = 0; this.moving.delete(o); this.gridAdd(o); } }
    for (const o of this.timed) if (--o.life <= 0) { o.life = 1; this.removeOrb(o, 0); }
    const grid = this.grid;
    const eatCheck = (p, pr, o) => { const r = pr + o.r + 8, dx = p.x - o.x, dy = p.y - o.y; if (dx > r + 40 || dx < -r - 40 || dy > r + 40 || dy < -r - 40) return; const d2 = dx * dx + dy * dy;
      if (d2 < r * r) { p.m += o.v * (1 + (PCT[p.skin] || 0) / 100); if (p.ws) p.eat = (p.eat || 0) + o.v; this.removeOrb(o, p.id); }
      else if (d2 < (r + 40) * (r + 40)) { const d = Math.sqrt(d2); o.x += dx / d * 2.5; o.y += dy / d * 2.5; if (o.cell >= 0 && (((o.x / 160) | 0) * 64 + ((o.y / 160) | 0)) !== o.cell) { this.gridDel(o); this.gridAdd(o); } } };
    for (const p of this.players) {
      if (!p.alive) continue; const pr = radius(p.m), reach = pr + 60;
      const x0 = Math.max(0, ((p.x - reach) / 160) | 0), x1 = ((p.x + reach) / 160) | 0, y0 = Math.max(0, ((p.y - reach) / 160) | 0), y1 = ((p.y + reach) / 160) | 0;
      for (let cx = x0; cx <= x1; cx++) for (let cy = y0; cy <= y1; cy++) { const c = grid.get(cx * 64 + cy); if (!c) continue; for (let i = c.length - 1; i >= 0; i--) { const o = c[i]; if (o) eatCheck(p, pr, o); } }
      for (const o of this.moving) if (!o.dead) eatCheck(p, pr, o);
    }
    const pc = this.pellets;
    for (let k = pc; k < PELLETS && k < pc + 6; k++) this.pellet();
    if (this.tick % 2 === 0) this.broadcast();
  }
  broadcast() {
    const P = [];
    for (const p of this.players) if (p.alive) P.push([p.id, r1(p.x), r1(p.y), r3(p.a), r1(p.m), p.kills, (p.dashT > 0 ? 1 : 0) | (p.stun > 0 ? 2 : 0), r1(p.vx), r1(p.vy)]);
    const msg = { t: 's', k: this.tick, p: P };
    if (this.events.length) msg.e = this.events;
    if (this.orbAdds.length) msg.oa = this.orbAdds.map(o => [o.id, r1(o.x), r1(o.y), r1(o.v), o.col, r1(o.vx), r1(o.vy), o.life]);
    if (this.orbRems.length) msg.or = this.orbRems;
    if (this.tick % 60 === 0) msg.n = this.clients.size;
    if (this.storm.on) msg.st = [this.storm.x | 0, this.storm.y | 0, this.storm.t];
    const s = JSON.stringify(msg);
    for (const c of this.clients) if (c.readyState === 1 && c.bufferedAmount < 2e6) c.send(s);
    this.events = []; this.orbAdds = []; this.orbRems = [];
  }
  welcome(ws) {
    send(ws, { t: 'w', arena: this.id, tick: this.tick, world: WORLD, n: this.clients.size,
      players: this.players.filter(p => p.alive).map(p => this.info(p)),
      orbs: [...this.orbs.values()].map(o => [o.id, r1(o.x), r1(o.y), r1(o.v), o.col, r1(o.vx), r1(o.vy), o.life]),
      storm: this.storm.on ? [this.storm.x | 0, this.storm.y | 0, this.storm.t] : null });
  }
}

function send(ws, obj) { if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj)); }
const arenas = [];
function pickArena() { let a = arenas.find(x => x.humans().length < MAX_HUMANS); if (!a) { a = new Arena(arenas.length + 1); arenas.push(a); } return a; }

// ---------- HTTP (serve il gioco) ----------
const MIME = { '.html': 'text/html; charset=utf-8' };
let CLIENT_HTML = SRC.replace('<head>', '<head><script>window.PLASMA_ONLINE=true;</script><link rel="icon" href="/brand/icon.png">');
const ICON_PNG = Buffer.from('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', 'base64');
const rateLimit = new Map(); setInterval(() => rateLimit.clear(), 600000);
const server = http.createServer((req, res) => {
  const url = decodeURIComponent((req.url || '/').split('?')[0]);
  if (url === '/' || url === '/index.html') { res.writeHead(200, { 'Content-Type': MIME['.html'], 'Cache-Control': 'no-cache' }); return res.end(CLIENT_HTML); }
  if (url === '/api/checkout' && req.method === 'POST') {
    let body = ''; req.on('data', c => { body += c; if (body.length > 2000) req.destroy(); });
    req.on('end', async () => {
      const out = (code, obj) => { res.writeHead(code, { 'Content-Type': 'application/json' }); res.end(JSON.stringify(obj)); };
      try {
        if (!STRIPE_KEY) return out(503, { error: 'payments_off' });
        const ip = req.headers['x-forwarded-for'] || req.socket.remoteAddress || ''; const now = Date.now();
        const rl = rateLimit.get(ip) || []; const recent = rl.filter(t => now - t < 60000); if (recent.length >= 8) return out(429, { error: 'slow_down' }); recent.push(now); rateLimit.set(ip, recent);
        const { token, pack } = JSON.parse(body || '{}');
        const a = /^PLA-[A-Z0-9]{20}$/.test(String(token || '')) ? await store.get(idOf(token)) : null; if (!a) return out(401, { error: 'no_account' });
        const pk = PACKS.find(p => p.id === pack); if (!pk || !PRICE_IDS[pk.id]) return out(400, { error: 'bad_pack' });
        const base = process.env.BASE_URL || ('https://' + req.headers.host);
        const s = await stripe('POST', 'checkout/sessions', { mode: 'payment', line_items: { 0: { price: PRICE_IDS[pk.id], quantity: 1 } }, managed_payments: { enabled: 'true' },
          client_reference_id: a.id, metadata: { acct: a.id, pack: pk.id }, locale: 'auto',
          branding_settings: { display_name: 'DOOM GAMES', background_color: '#0b0d14', button_color: '#1fb6ff', border_style: 'rounded', icon: { type: 'url', url: base + '/brand/icon.png' } }, success_url: base + '/?paid={CHECKOUT_SESSION_ID}', cancel_url: base + '/' });
        a.pending.push(s.id); if (a.pending.length > 20) a.pending = a.pending.slice(-20); await store.put(a, true);
        out(200, { url: s.url });
      } catch (e) { console.error('checkout', e.message); out(500, { error: 'stripe', msg: e.message }); }
    });
    return;
  }
  if (url === '/brand/icon.png' || url === '/favicon.ico') { res.writeHead(200, { 'Content-Type': 'image/png', 'Cache-Control': 'public, max-age=86400' }); return res.end(ICON_PNG); }
  if (url === '/health') { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, tickMs: +PERF.tickMs.toFixed(3), cpuLoad: +(PERF.tickMs * 60 / 10).toFixed(1) + '%', arenas: arenas.map(a => ({ id: a.id, humans: a.humans().length, bots: a.players.length - a.humans().length })) })); }
  res.writeHead(404); res.end('Not found');
});

// ---------- account dei giocatori ----------
async function handleAuth(ws, token, switching) {
  try {
    let tok = /^PLA-[A-Z0-9]{20}$/.test(String(token || '')) ? String(token) : null, a = tok ? await store.get(idOf(tok)) : null;
    if (!a) { if (switching) return send(ws, { t: 'err', k: 'badCode' }); tok = newToken(); a = blankAccount(idOf(tok)); await store.put(a, true); }
    if (ws.player && ws.player.alive) return;
    ws.acct = a; ws.token = tok;
    let daily = 0; if (a.daily !== dayKey()) { a.daily = dayKey(); daily = 25; giveUsd(a, 25); store.put(a, true); }
    send(ws, { t: 'acct', token: tok, d: publicAcct(a), daily, pay: !!STRIPE_KEY });
    if (switching) send(ws, { t: 'switched' });
    checkPending(a, ws);
  } catch (e) { console.error('auth', e.message); send(ws, { t: 'err', k: 'server' }); }
}

// ---------- WebSocket ----------
const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 4096 });
wss.on('connection', (ws) => {
  const arena = pickArena(); arena.clients.add(ws); ws.arena = arena; ws.player = null; ws.isAlive = true;
  arena.welcome(ws);
  ws.on('pong', () => { ws.isAlive = true; });
  let msgCount = 0, msgWindow = Date.now();
  ws.on('message', (raw) => {
    const now = Date.now(); if (now - msgWindow > 1000) { msgWindow = now; msgCount = 0; } if (++msgCount > 90) return; // anti-flood
    let m; try { m = JSON.parse(raw); } catch (e) { return; }
    if (m.t === 'join') {
      let p = ws.player;
      if (!p) { p = arena.newPlayer('', false); p.ws = ws; ws.player = p; arena.players.push(p); }
      if (p.alive) return;
      p.name = String(m.name || 'Player').replace(/[<>&"]/g, '').slice(0, 14) || 'Player';
      p.col = COLORS.includes(m.col) ? m.col : COLORS[(Math.random() * 7) | 0];
      const A = ws.acct; if (!A) return;
      const md = MODEL_BY_ID[m.model] || MODELS[0]; p.model = isUnlocked(md, A.stats) ? md : MODELS[0];
      const ok = (id, cat) => SHOP_BY_ID[id] && SHOP_BY_ID[id].cat === cat && ownsItem(A, id);
      p.skin = ok(A.eq.skin, 'skin') ? A.eq.skin : 's_default'; p.hiltS = ok(A.eq.hilt, 'hilt') ? A.eq.hilt : 'h_default';
      p.trailS = ok(A.eq.trail, 'trail') ? A.eq.trail : 't_default'; p.kfx = ok(A.eq.kill, 'kill') ? A.eq.kill : 'k_default';
      p.lv = levelOf(A.stats.xp); p.ba = NaN; p.earn = null;
      p.mx = p.my = 0; arena.spawn(p); arena.balanceBots();
      send(ws, { t: 'you', id: p.id });
    } else if (m.t === 'in' && ws.player && ws.player.alive) {
      const p = ws.player;
      const mx = +m.mx || 0, my = +m.my || 0; p.mx = clamp(mx, -1, 1); p.my = clamp(my, -1, 1);
      if (Number.isFinite(+m.a)) p.aim = +m.a;
      if (Number.isFinite(+m.b)) p.ba = p.a + angDiff(+m.b, p.a);
      if (Number.isFinite(+m.r)) p.viewR = Math.min(+m.r, arena.tick);
      if (m.d) p.wantDash = true;
    } else if (m.t === 'ping') send(ws, { t: 'pong', c: m.c });
    else if (m.t === 'auth') handleAuth(ws, m.token);
    else if (!ws.acct) return;
    else if (m.t === 'buy') {
      const A = ws.acct, it = SHOP_BY_ID[m.id]; if (!it || it.price <= 0 || ownsItem(A, it.id)) return;
      const cost = usdOf(it); if (A.usd < cost) return send(ws, { t: 'err', k: 'notEnough' });
      A.usd -= cost; A.owned.push(it.id); A.eq[it.cat] = it.id; store.put(A, true); send(ws, { t: 'bought', id: it.id }); pushAcct(ws);
    } else if (m.t === 'eq') {
      const A = ws.acct, it = SHOP_BY_ID[m.id]; if (!it || !ownsItem(A, it.id)) return; A.eq[it.cat] = it.id; touch(ws);
    } else if (m.t === 'qclaim') {
      const A = ws.acct; if (A.quests.day !== dayKey()) A.quests = freshQuests(); const q = A.quests.list[m.i | 0];
      if (!q || !q.ok || q.c) return; q.c = true; giveUsd(A, q.r); store.put(A, true); pushAcct(ws);
    } else if (m.t === 'claim') { verifySession(ws.acct, String(m.sid || ''), ws); }
    else if (m.t === 'code') {
      const raw = String(m.code || '').trim().toUpperCase().slice(0, 64);
      if ((process.env.OWNER_CODE && raw === process.env.OWNER_CODE.toUpperCase()) || cyrb53(raw) === OWNER_H) { ws.acct.owner = true; touch(ws); send(ws, { t: 'owner' }); }
      else if (/^PLA-[A-Z0-9]{20}$/.test(raw)) handleAuth(ws, raw, true);
      else send(ws, { t: 'err', k: 'badCode' });
    }
  });
  ws.on('close', () => { arena.clients.delete(ws); if (ws.acct) store.put(ws.acct); if (ws.player) arena.removePlayer(ws.player); arena.balanceBots(); });
});
setInterval(() => { for (const ws of wss.clients) { if (!ws.isAlive) { ws.terminate(); continue; } ws.isAlive = false; try { ws.ping(); } catch (e) {} } }, 15000);

// ---------- loop a 60 Hz ----------
const PERF = { tickMs: 0 };
const STEP = 1000 / 60; let last = performance.now(), acc = 0;
function loop() {
  const now = performance.now(); acc += now - last; last = now; if (acc > 250) acc = 250;
  const t0 = performance.now(); let n = 0;
  while (acc >= STEP) { for (const a of arenas) a.update(); acc -= STEP; n++; }
  if (n) PERF.tickMs = PERF.tickMs * .98 + ((performance.now() - t0) / n) * .02;
  // libera arene vuote oltre la prima
  for (let i = arenas.length - 1; i > 0; i--) if (!arenas[i].clients.size) arenas.splice(i, 1);
  setTimeout(loop, Math.max(1, Math.floor(STEP - acc)));
}
pickArena(); loop();
console.log('Archivio account: ' + store.kind + ' · pagamenti: ' + (STRIPE_KEY ? (STRIPE_TEST ? 'TEST' : 'LIVE') : 'disattivati (manca STRIPE_SECRET_KEY)'));
for (const sig of ['SIGTERM', 'SIGINT']) process.on(sig, async () => { await store.flush(); process.exit(0); });
server.listen(PORT, () => console.log('PLASMA.io server su porta ' + PORT));

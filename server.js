// PLASMA.io — server multigiocatore autoritativo
// Avvio: node server.js  (porta da process.env.PORT, default 3000)
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

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

// ---------- arena ----------
let NEXT_ID = 1;
class Arena {
  constructor(id) {
    this.id = id; this.tick = 0; this.players = []; this.orbs = new Map(); this.orbId = 1;
    this.clients = new Set(); this.events = []; this.orbAdds = []; this.orbRems = [];
    this.storm = { on: false, x: 0, y: 0, R: 360, t: 0, next: 2400 };
    for (let i = 0; i < PELLETS; i++) this.pellet(true);
    this.balanceBots(true);
  }
  humans() { return this.players.filter(p => !p.bot); }
  // ---- orbs ----
  addOrb(x, y, v, col, vx = 0, vy = 0, life = 0, silent) {
    const o = { id: this.orbId++, x, y, v, col, vx, vy, life, r: 3 + Math.sqrt(v) * 1.6 };
    this.orbs.set(o.id, o); if (!silent) this.orbAdds.push(o); return o;
  }
  pellet(silent) { this.addOrb(rnd(20, WORLD - 20), rnd(20, WORLD - 20), 1, (Math.random() * 7) | 0, 0, 0, 0, silent); }
  dropMass(x, y, amount, col) { let left = amount; const piece = Math.max(4, amount / 22); while (left > .5) { const v = Math.min(left, piece * rnd(.7, 1.3)); left -= v; const a = rnd(0, TAU), s = rnd(1.5, 6); this.addOrb(x + rnd(-6, 6), y + rnd(-6, 6), v, col, Math.cos(a) * s, Math.sin(a) * s, 1800); } }
  // ---- giocatori ----
  newPlayer(name, bot) {
    return { id: NEXT_ID++, name, bot, x: 0, y: 0, vx: 0, vy: 0, m: 20, a: 0, aPrev: 0, aim: 0, aimT: 0, av: 0, omega: 0, model: MODELS[0], col: COLORS[0], alive: false, kills: 0, best: 20, born: 0, dashT: 0, dashCd: 0, stun: 0, hitCd: new Map(), mx: 0, my: 0, respawn: 0, counter: 0, steady: 0,
      react: 10, iq: .5, hand: .12, pat: 80, reactT: 0, mode: 'guard', modeT: 0, circ: 1, target: null, th: null, block: null, wx: 0, wy: 0, aimNoise: 0, skin: 's_default', hiltS: 'h_default', trailS: 't_default', kfx: 'k_default', lv: 1 };
  }
  botCosmetics(b) { const pick = (cat, pr) => { if (Math.random() > pr) return SHOP.find(s => s.cat === cat && s.price === 0).id; const L2 = SHOP.filter(s => s.cat === cat && s.price > 0); return L2[(Math.random() * L2.length) | 0].id; }; b.skin = pick('skin', .3); b.hiltS = pick('hilt', .25); b.trailS = pick('trail', .2); b.kfx = pick('kill', .2); }
  setPersonality(b) { let r = Math.random(), P = PERS[0]; for (const q of PERS) { if (r < q.p) { P = q; break; } r -= q.p; } b.react = rnd(...P.react) | 0; b.iq = rnd(...P.iq); b.hand = rnd(...P.hand); b.pat = rnd(...P.pat) | 0; b.circ = Math.random() < .5 ? 1 : -1; }
  botModel() { const w = [40, 15, 12, 14, 8, 7, 4]; let r = Math.random() * 100; for (let i = 0; i < w.length; i++) { if (r < w[i]) return MODELS[i]; r -= w[i]; } return MODELS[0]; }
  rollBot(b) { b.name = NAMES[(Math.random() * NAMES.length) | 0]; b.col = COLORS[(Math.random() * 7) | 0]; b.model = this.botModel(); this.setPersonality(b); this.botCosmetics(b); b.lv = 1 + ((Math.random() ** 1.6) * 40 | 0); }
  spawn(p, m = 20) {
    let best = [WORLD / 2, WORLD / 2], bs = -1e9;
    for (let t = 0; t < 40; t++) { const x = rnd(220, WORLD - 220), y = rnd(220, WORLD - 220); let md = 1e9;
      for (const o of this.players) { if (!o.alive || o === p) continue; let d = Math.hypot(o.x - x, o.y - y) - bladeLen(o) - radius(o.m); if (!o.bot) d -= 600; if (d < md) md = d; }
      if (md > bs) { bs = md; best = [x, y]; } if (bs > 700) break; }
    Object.assign(p, { x: best[0], y: best[1], vx: 0, vy: 0, m, alive: true, kills: 0, best: m, born: this.tick, dashT: 0, dashCd: 0, stun: 0, streak: 0, a: rnd(0, TAU), av: 0, counter: 0, mode: 'guard', modeT: 0, target: null, th: null, block: null, steady: 0 });
    p.aPrev = p.a; p.aim = p.a; p.aimT = p.a; p.hitCd.clear();
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
    if (att && att !== p && att.alive) { if (PCT[att.kfx]) att.m += p.m * PCT[att.kfx] / 100; att.kills++; if (revenge) att.nemId = null; }
    if (!p.bot && att && att !== p) p.nemId = att.id;
    this.events.push(['k', p.id, att ? att.id : 0, r1(p.x), r1(p.y), r1(p.m), r3(att ? att.a : rnd(0, TAU)), p.kills]);
    if (p.bot) p.respawn = 150 + (Math.random() * 150 | 0);
    else if (p.ws) send(p.ws, { t: 'dead', by: att ? att.id : 0 });
  }
  clash(p, q, x, y) {
    if ((p.hitCd.get('c' + q.id) || 0) > this.tick) return; p.hitCd.set('c' + q.id, this.tick + 16); q.hitCd.set('c' + p.id, this.tick + 16);
    const vp = Math.abs(p.omega) * bladeLen(p), vq = Math.abs(q.omega) * bladeLen(q);
    p.a = p.aPrev - p.omega * .8; q.a = q.aPrev - q.omega * .8; p.av = -p.av * .6; q.av = -q.av * .6;
    const def = vp <= vq ? p : q, att = def === p ? q : p, vd = Math.min(vp, vq), va = Math.max(vp, vq);
    const perfect = (def.steady || 0) >= 8 && vd < 3 && va > 8;
    if (perfect) { att.stun = 26; def.stun = 0; def.counter = this.tick + 50; } else { p.stun = 3; q.stun = 3; }
    const dx = q.x - p.x, dy = q.y - p.y, d = Math.hypot(dx, dy) || 1; p.vx -= dx / d * 3; p.vy -= dy / d * 3; q.vx += dx / d * 3; q.vy += dy / d * 3;
    this.events.push(['c', p.id, q.id, r1(x), r1(y), perfect ? def.id : 0, perfect ? att.id : 0]);
  }
  combat() {
    const alive = this.players.filter(p => p.alive), segs = new Map(); for (const p of alive) segs.set(p, segsOf(this.bladesAt(p, p.x, p.y, p.a)));
    for (let i = 0; i < alive.length; i++) { const p = alive[i];
      for (let j = 0; j < alive.length; j++) { if (i === j) continue; const q = alive[j]; if (!p.alive) break;
        if (!q.alive || Math.abs(p.x - q.x) > 700 || Math.abs(p.y - q.y) > 700) continue;
        if (i < j) { const w = (bladeW(p) + bladeW(q)) * .5 + 3; outer: for (const a of segs.get(p)) for (const b of segs.get(q)) { const [d2, x, y] = segSegD2(a, b); if (d2 < w * w) { this.clash(p, q, x, y); break outer; } } }
        if (p.stun > 0 || this.tick - q.born < 120) continue;
        const rq = radius(q.m) + bladeW(p) * .75 + 2;
        for (const a of segs.get(p)) { const [d2] = segPointD2(a[0], a[1], a[2], a[3], q.x, q.y); if (d2 < rq * rq) { this.kill(q, p); break; } }
      }
    }
    for (let i = 0; i < alive.length; i++) for (let j = i + 1; j < alive.length; j++) { const p = alive[i], q = alive[j]; if (!p.alive || !q.alive) continue; const dx = q.x - p.x, dy = q.y - p.y, rr = radius(p.m) + radius(q.m), d2 = dx * dx + dy * dy; if (d2 < rr * rr && d2 > 0) { const d = Math.sqrt(d2), o = (rr - d) / 2, nx = dx / d, ny = dy / d; p.x -= nx * o; p.y -= ny * o; q.x += nx * o; q.y += ny * o; } }
  }
  botThink(b) {
    const r = radius(b.m), Ln = bladeLen(b), dumb = b.iq < .35, tick = this.tick, players = this.players;
    if (--b.reactT <= 0) {
      b.reactT = b.react + ((Math.random() * b.react * .5) | 0);
      let th = null, td = 1e9, pr = null, pd = 1e9;
      for (const o of players) { if (!o.alive || o === b) continue; const d = Math.hypot(o.x - b.x, o.y - b.y), reach = bladeLen(o) + radius(o.m);
        if (!dumb || Math.random() < .4) { if (o.m > b.m * 1.8 && d < reach + r + 200 && d < td) { th = o; td = d; } }
        if (o.m < b.m * 1.6 && d < 450 + 350 * b.iq && d < pd && tick - o.born > 150) { pr = o; pd = d; } }
      b.th = th; if (pr !== b.target) { b.target = pr; b.mode = 'guard'; b.modeT = 0; }
      b.block = null;
      if (!dumb) for (const o of players) { if (!o.alive || o === b) continue; const d = Math.hypot(o.x - b.x, o.y - b.y); if (d > bladeLen(o) + r + 30) continue;
        if (Math.abs(o.omega || 0) * bladeLen(o) > 7 && Math.random() < b.iq * .6) { b.block = o; break; } }
      b.aimNoise = rnd(-1, 1) * (1 - b.iq) * .5;
      if (!pr && !th) { let best = null, bd = 1e12; for (const o of this.orbs.values()) { const dx = o.x - b.x, dy = o.y - b.y; if (dx > 520 || dx < -520 || dy > 520 || dy < -520) continue; const d = (dx * dx + dy * dy) / (o.v + 1); if (d < bd) { bd = d; best = o; } }
        const st = this.storm;
        if (st.on && Math.hypot(st.x - b.x, st.y - b.y) < 1600 && Math.random() < .6) { b.wx = st.x + rnd(-150, 150); b.wy = st.y + rnd(-150, 150); } else if (best) { b.wx = best.x; b.wy = best.y; } else if (!b.wx || Math.hypot(b.wx - b.x, b.wy - b.y) < 80) { b.wx = rnd(300, WORLD - 300); b.wy = rnd(300, WORLD - 300); } }
    }
    let mx = 0, my = 0; const th = b.th, pr = b.target;
    if (th && th.alive) { const dx = b.x - th.x, dy = b.y - th.y, d = Math.hypot(dx, dy) || 1; mx = dx / d; my = dy / d; b.aimT = Math.atan2(-dy, -dx);
      if (d < bladeLen(th) + radius(th.m) + r + 20 && b.iq > .5 && Math.random() < .02) this.dash(b); }
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
        if ((opening && b.modeT > 12) || b.modeT > b.pat) { b.mode = 'strike'; b.modeT = 0; if (b.iq > .6 && b.m > 30 && d < guardD + 60 && Math.random() < .4) this.dash(b); }
        if (Math.random() < .004) b.circ *= -1;
      } else if (b.mode === 'strike') { mx = dx / d; my = dy / d; b.aimT = ang + Math.sin(b.modeT * .25) * .35 * b.circ; if (b.modeT > 28 + b.react) { b.mode = 'back'; b.modeT = 0; } }
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
      else if (p.wantDash) { p.wantDash = false; this.dash(p); }
      this.steer(p, p.mx, p.my); p.x += p.vx; p.y += p.vy; const r = radius(p.m); p.x = clamp(p.x, r, WORLD - r); p.y = clamp(p.y, r, WORLD - r);
      this.turnBlade(p);
      p.steady = Math.abs(p.omega) * bladeLen(p) < 3 ? (p.steady || 0) + 1 : 0;
      if (p.dashT > 0) p.dashT--; if (p.dashCd > 0) p.dashCd--; if (p.stun > 0) p.stun--;
      if (p.m > 300) p.m -= (p.m - 300) * .00004;
      if (p.m > p.best) p.best = p.m;
    }
    this.combat();
    const st = this.storm;
    if (!st.on && --st.next <= 0) { st.on = true; st.t = 900; st.x = rnd(500, WORLD - 500); st.y = rnd(500, WORLD - 500); this.events.push(['st', st.x | 0, st.y | 0]); }
    if (st.on) { if (--st.t <= 0) { st.on = false; st.next = (5400 + rnd(0, 1800)) | 0; this.events.push(['st0']); } else if (this.tick % 3 === 0) { const a = rnd(0, TAU), d = Math.sqrt(Math.random()) * st.R; this.addOrb(st.x + Math.cos(a) * d, st.y + Math.sin(a) * d, 3, 4, 0, 0, 1200); } }
    { let k = null; for (const p of this.players) if (p.alive && (!k || p.m > k.m)) k = p; this.king = k; }
    let pc = 0;
    for (const o of this.orbs.values()) {
      if (o.vx || o.vy) { o.x += o.vx; o.y += o.vy; o.vx *= .9; o.vy *= .9; if (Math.abs(o.vx) < .05 && Math.abs(o.vy) < .05) o.vx = o.vy = 0; }
      if (o.life && --o.life <= 0) { this.orbs.delete(o.id); this.orbRems.push([o.id, 0]); continue; }
      let eaten = false;
      for (const p of this.players) { if (!p.alive) continue; const r = radius(p.m) + o.r + 8, dx = p.x - o.x, dy = p.y - o.y; if (dx > r + 40 || dx < -r - 40 || dy > r + 40 || dy < -r - 40) continue; const d2 = dx * dx + dy * dy;
        if (d2 < r * r) { p.m += o.v * (1 + (PCT[p.skin] || 0) / 100); this.orbs.delete(o.id); this.orbRems.push([o.id, p.id]); eaten = true; break; }
        else if (d2 < (r + 40) * (r + 40)) { const d = Math.sqrt(d2); o.x += dx / d * 2.5; o.y += dy / d * 2.5; } }
      if (!eaten && o.v === 1 && !o.life) pc++;
    }
    for (let k = pc; k < PELLETS && k < pc + 6; k++) this.pellet();
    if (this.tick % 3 === 0) this.broadcast();
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
let CLIENT_HTML = SRC.replace('<head>', '<head><script>window.PLASMA_ONLINE=true;</script>');
const server = http.createServer((req, res) => {
  const url = decodeURIComponent((req.url || '/').split('?')[0]);
  if (url === '/' || url === '/index.html') { res.writeHead(200, { 'Content-Type': MIME['.html'], 'Cache-Control': 'no-cache' }); return res.end(CLIENT_HTML); }
  if (url === '/health') { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, arenas: arenas.map(a => ({ id: a.id, humans: a.humans().length, bots: a.players.length - a.humans().length })) })); }
  res.writeHead(404); res.end('Not found');
});

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
      p.model = MODEL_BY_ID[m.model] || MODELS[0];
      const ok = (id, cat) => SHOP_IDS.has(id) && SHOP.find(s => s.id === id).cat === cat;
      p.skin = ok(m.skin, 'skin') ? m.skin : 's_default'; p.hiltS = ok(m.hilt, 'hilt') ? m.hilt : 'h_default';
      p.trailS = ok(m.trail, 'trail') ? m.trail : 't_default'; p.kfx = ok(m.kfx, 'kill') ? m.kfx : 'k_default';
      p.lv = clamp(m.lv | 0, 1, 999);
      p.mx = p.my = 0; arena.spawn(p); arena.balanceBots();
      send(ws, { t: 'you', id: p.id });
    } else if (m.t === 'in' && ws.player && ws.player.alive) {
      const p = ws.player;
      const mx = +m.mx || 0, my = +m.my || 0; p.mx = clamp(mx, -1, 1); p.my = clamp(my, -1, 1);
      if (Number.isFinite(+m.a)) p.aim = +m.a;
      if (m.d) p.wantDash = true;
    } else if (m.t === 'ping') send(ws, { t: 'pong', c: m.c });
  });
  ws.on('close', () => { arena.clients.delete(ws); if (ws.player) arena.removePlayer(ws.player); arena.balanceBots(); });
});
setInterval(() => { for (const ws of wss.clients) { if (!ws.isAlive) { ws.terminate(); continue; } ws.isAlive = false; try { ws.ping(); } catch (e) {} } }, 15000);

// ---------- loop a 60 Hz ----------
const STEP = 1000 / 60; let last = performance.now(), acc = 0;
function loop() {
  const now = performance.now(); acc += now - last; last = now; if (acc > 250) acc = 250;
  while (acc >= STEP) { for (const a of arenas) a.update(); acc -= STEP; }
  // libera arene vuote oltre la prima
  for (let i = arenas.length - 1; i > 0; i--) if (!arenas[i].clients.size) arenas.splice(i, 1);
  setTimeout(loop, 4);
}
pickArena(); loop();
server.listen(PORT, () => console.log('PLASMA.io server su porta ' + PORT));

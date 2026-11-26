// ================================================================
//  BACKGAMMON — PewPlay
//  @bg #1d140e
//  @accent #d9a441
//  Regole complete: barra, colpi, uscita, doppi, obbligo di usare il
//  massimo dei dadi. Contro il computer (euristica) o in due.
//  board[1..24]: >0 pedine bianche (giocatore 1, va da 24 a 1),
//               <0 pedine nere (giocatore 2, va da 1 a 24).
// ================================================================
(function () {
  'use strict';
  const { clamp, rand, sfx, store } = PP;

  const GAME_ID = 'backgammon';
  const MODES = ['vs Computer', '2 Players'];
  const LEVELS = ['Easy', 'Medium', 'Hard'];
  const BW = 1000, BH = 760;          // tavola in coordinate locali
  const M = 20, TRAY = 80, BAR = 60;
  const PW = (BW - 2 * M - TRAY - BAR) / 12, PH = 300, CR = Math.min(PW / 2 - 2, 30);

  let mode = 0, level = 1;
  let st;                 // { b: [25], bar: [0,w,b], off: [0,w,b] }
  let turn, dice, diceUsed, moves, turnStart, phase, selected, aiTimer, aiQueue, winner, rollAnim, noMoveT;
  let view = { s: 1, x: 0, y: 0, rot: false };
  let anims = [];

  // ── REGOLE ──────────────────────────────────────
  const sign = p => (p === 1 ? 1 : -1);
  function fresh() {
    const b = Array(25).fill(0);
    b[24] = 2; b[13] = 5; b[8] = 3; b[6] = 5;
    b[1] = -2; b[12] = -5; b[17] = -3; b[19] = -5;
    return { b, bar: [0, 0, 0], off: [0, 0, 0] };
  }
  const clone = s => ({ b: s.b.slice(), bar: s.bar.slice(), off: s.off.slice() });
  function allHome(s, p) {
    if (s.bar[p]) return false;
    for (let i = 1; i <= 24; i++) { const v = s.b[i]; if (p === 1 && v > 0 && i > 6) return false; if (p === 2 && v < 0 && i < 19) return false; }
    return true;
  }
  // mosse singole con un dado: { from, to, die } — from 0 = barra, to 0/25 = fuori
  function singleMoves(s, p, die) {
    const out = [], sg = sign(p);
    const dest = from => (p === 1 ? from - die : from + die);
    const open = to => sg * s.b[to] >= -1;
    if (s.bar[p]) {
      const to = p === 1 ? 25 - die : die;
      if (open(to)) out.push({ from: 0, to, die });
      return out;
    }
    const home = allHome(s, p);
    for (let i = 1; i <= 24; i++) {
      if (sg * s.b[i] <= 0) continue;
      const to = dest(i);
      if (to >= 1 && to <= 24) { if (open(to)) out.push({ from: i, to, die }); }
      else if (home) {
        const dist = p === 1 ? i : 25 - i;
        if (dist === die) out.push({ from: i, to: p === 1 ? 0 : 25, die });
        else if (dist < die) {
          // si può uscire con un dado più alto solo dalla pedina più lontana
          let farther = false;
          for (let j = 1; j <= 24; j++) { const d = p === 1 ? j : 25 - j; if (sg * s.b[j] > 0 && d > dist && d <= 6) farther = true; }
          if (!farther) out.push({ from: i, to: p === 1 ? 0 : 25, die });
        }
      }
    }
    return out;
  }
  function applyMove(s, p, m) {
    const sg = sign(p);
    if (m.from === 0) s.bar[p]--; else s.b[m.from] -= sg;
    let hit = false;
    if (m.to === 0 || m.to === 25) s.off[p]++;
    else {
      if (s.b[m.to] === -sg) { s.b[m.to] = 0; s.bar[3 - p]++; hit = true; }
      s.b[m.to] += sg;
    }
    return hit;
  }
  // tutte le sequenze legali (rispettando l'obbligo di usare il massimo dei dadi)
  function sequences(s, p, ds) {
    const results = [];
    const seen = new Set();
    function rec(cur, remaining, path) {
      let any = false;
      const tried = new Set();
      for (let k = 0; k < remaining.length; k++) {
        const die = remaining[k];
        if (tried.has(die)) continue;
        tried.add(die);
        for (const m of singleMoves(cur, p, die)) {
          any = true;
          const n = clone(cur); applyMove(n, p, m);
          rec(n, remaining.slice(0, k).concat(remaining.slice(k + 1)), path.concat([m]));
        }
      }
      if (!any) {
        const key = cur.b.join() + '|' + cur.bar.join() + '|' + cur.off.join() + '|' + path.length;
        if (!seen.has(key)) { seen.add(key); results.push({ path, s: cur }); }
      }
    }
    rec(s, ds, []);
    const max = Math.max(0, ...results.map(r => r.path.length));
    let best = results.filter(r => r.path.length === max);
    if (max === 1 && ds.length === 2 && ds[0] !== ds[1]) {
      const hi = Math.max(...ds);
      if (best.some(r => r.path[0].die === hi)) best = best.filter(r => r.path[0].die === hi);
    }
    return best;
  }

  // ── IA ──────────────────────────────────────────
  function pips(s, p) {
    let n = s.bar[p] * 25;
    for (let i = 1; i <= 24; i++) { const v = s.b[i] * sign(p); if (v > 0) n += v * (p === 1 ? i : 25 - i); }
    return n;
  }
  function evalFor(s, p) {
    const o = 3 - p, sg = sign(p);
    let v = (pips(s, o) - pips(s, p)) * 1.0;
    v += s.off[p] * 12 - s.off[o] * 12;
    v += s.bar[o] * 18 - s.bar[p] * 18;
    const contact = !raceOnly(s);
    for (let i = 1; i <= 24; i++) {
      const c = s.b[i] * sg;
      const d = p === 1 ? i : 25 - i; // distanza dalla propria uscita
      if (c >= 2) { v += 5 + (d <= 6 ? 6 : d <= 9 ? 3 : 0); }
      if (c === 1 && contact) {
        // pedina scoperta: quanti avversari la possono colpire (entro 12)
        let threat = 0;
        for (let j = 1; j <= 24; j++) { const oc = s.b[j] * sign(o); if (oc <= 0) continue; const dist = p === 1 ? i - j : j - i; if (dist < 0 && -dist <= 12) threat++; }
        if (s.bar[o]) threat += 2;
        v -= (level === 2 ? 4 : 3) * Math.min(threat, 4) * (d <= 6 ? 1.5 : 1);
      }
    }
    // prime: punti consecutivi
    let run = 0, bestRun = 0;
    for (let i = 1; i <= 24; i++) { if (s.b[i] * sg >= 2) { run++; bestRun = Math.max(bestRun, run); } else run = 0; }
    v += bestRun * bestRun * (level === 2 ? 2 : 1);
    return v;
  }
  function raceOnly(s) {
    let lastW = 0, firstB = 25;
    for (let i = 1; i <= 24; i++) { if (s.b[i] > 0) lastW = Math.max(lastW, i); if (s.b[i] < 0) firstB = Math.min(firstB, i); }
    if (s.bar[1] || s.bar[2]) return false;
    return lastW < firstB;
  }
  function aiChoose() {
    const seqs = sequences(st, turn, dice.length === 4 ? dice.slice() : dice.slice());
    if (!seqs.length || !seqs[0].path.length) return [];
    if (level === 0) return PP.pick(seqs).path;
    let best = seqs[0], bv = -Infinity;
    for (const q of seqs) { const v = evalFor(q.s, turn) + Math.random() * (level === 1 ? 3 : 0.5); if (v > bv) { bv = v; best = q; } }
    return best.path;
  }

  // ── FLUSSO ──────────────────────────────────────
  function start() {
    st = fresh(); winner = 0; anims = []; selected = null;
    // il primo turno: ognuno tira un dado, chi fa di più comincia con quei due numeri
    let a, b; do { a = PP.randInt(1, 6); b = PP.randInt(1, 6); } while (a === b);
    turn = a > b ? 1 : 2;
    beginTurn([Math.max(a, b), Math.min(a, b)]);
  }
  function beginTurn(forced) {
    const d = forced || [PP.randInt(1, 6), PP.randInt(1, 6)];
    dice = d[0] === d[1] ? [d[0], d[0], d[0], d[0]] : d;
    diceUsed = []; legalCache = null;
    rollAnim = 0.5;
    turnStart = clone(st); moves = [];
    sfx.noise(0.18, 0.18, 2500); sfx.tone(300, 0.05, 'square', 0.05, null, 0.08);
    selected = null;
    const legal = sequences(st, turn, dice);
    phase = 'move';
    if (!legal.length || !legal[0].path.length) { noMoveT = 1.6; phase = 'nomove'; return; }
    if (mode === 0 && turn === 2) { aiQueue = aiChoose(); aiTimer = 0.8; }
  }
  // dadi rimasti
  const remaining = () => { const r = dice.slice(); for (const u of diceUsed) r.splice(r.indexOf(u), 1); return r; };
  // mosse singole ammesse ora (che restano dentro una sequenza legale massima)
  let legalCache = null;
  function legalNow() {
    if (legalCache) return legalCache;
    const rem = remaining();
    const seqs = sequences(st, turn, rem);
    const out = [];
    const k = new Set();
    for (const q of seqs) if (q.path.length) { const m = q.path[0]; const key = `${m.from}-${m.to}-${m.die}`; if (!k.has(key)) { k.add(key); out.push(m); } }
    legalCache = out;
    return out;
  }

  function doMove(m) {
    const before = clone(st);
    const hit = applyMove(st, turn, m);
    diceUsed.push(m.die); legalCache = null;
    moves.push(m);
    anims.push({ from: m.from, to: m.to, p: turn, t: 0, fromState: before });
    sfx.tone(hit ? 260 : 520, 0.06, 'triangle', 0.12);
    if (hit) { sfx.noise(0.15, 0.2, 1800); PP.shake = 5; }
    if (st.off[turn] === 15) return finish(turn);
    selected = null;
    // il giocatore conferma con "Done" (così può ancora annullare); il computer passa da solo
    if (!remaining().length || !legalNow().length) { phase = 'done'; aiTimer = mode === 0 && turn === 2 ? 0.5 : Infinity; }
  }

  function endTurn() { turn = 3 - turn; beginTurn(); }

  function undo() {
    if (!moves.length || (mode === 0 && turn === 2)) return;
    st = clone(turnStart); diceUsed = []; moves = []; phase = 'move'; selected = null; legalCache = null;
    sfx.tone(420, 0.08, 'sine', 0.1, 300);
  }

  function finish(p) {
    winner = p;
    const o = 3 - p;
    let kind = 1;
    if (st.off[o] === 0) {
      kind = 2;
      if (st.bar[o]) kind = 3;
      for (let i = 1; i <= 24; i++) { const v = st.b[i] * sign(o); if (v > 0 && (p === 1 ? i <= 6 : i >= 19)) kind = 3; }
    }
    const name = ['', 'win', 'gammon', 'backgammon'][kind];
    const key = `stats-${level}`, s = store.get(key, { w: 0, l: 0 });
    if (mode === 0) { if (p === 1) s.w++; else s.l++; store.set(key, s); }
    if (p === 1 || mode === 1) sfx.win(); else sfx.lose();
    PP.burst(PP.W / 2, PP.H / 2, ['#d9a441', '#fff', '#c0392b'], 50, 380, 5, 1.3, 300);
    const who = mode === 1 ? (p === 1 ? 'White' : 'Black') : p === 1 ? 'You' : 'Computer';
    PP.game.overDelay = 1200;
    PP.over(`${who} win${who === 'You' ? '' : 's'}!`, `${kind > 1 ? `A ${name}! ` : ''}${mode === 0 ? `${LEVELS[level]}: ${s.w} wins · ${s.l} losses` : ''}`);
  }

  function update(dt) {
    rollAnim = Math.max(0, rollAnim - dt);
    for (const a of anims) a.t += dt * 4;
    anims = anims.filter(a => a.t < 1);
    if (winner) return;
    if (phase === 'nomove') {
      noMoveT -= dt;
      if (noMoveT <= 0) endTurn();
      return;
    }
    if (phase === 'done') { aiTimer -= dt; if (aiTimer <= 0 && !anims.length) endTurn(); return; }
    if (mode === 0 && turn === 2 && phase === 'move' && !anims.length) {
      aiTimer -= dt;
      if (aiTimer <= 0 && rollAnim <= 0) {
        const m = aiQueue.shift();
        if (m) { doMove(m); aiTimer = 0.45; } else phase = 'done';
      }
    }
  }

  // ── GEOMETRIA ───────────────────────────────────
  function layout() {
    const top = 58, bottom = 70;
    const rot = PP.H > PP.W * 1.1;
    const w = rot ? BH : BW, h = rot ? BW : BH;
    const s = Math.min((PP.W - 16) / w, (PP.H - top - bottom) / h);
    view = { s, rot, x: (PP.W - w * s) / 2, y: top + (PP.H - top - bottom - h * s) / 2, w: w * s, h: h * s };
  }
  // coordinate locali → schermo
  function toScreen(x, y) {
    if (view.rot) return { x: view.x + (BH - y) * view.s, y: view.y + x * view.s };
    return { x: view.x + x * view.s, y: view.y + y * view.s };
  }
  function toLocal(px, py) {
    if (view.rot) return { x: (py - view.y) / view.s, y: BH - (px - view.x) / view.s };
    return { x: (px - view.x) / view.s, y: (py - view.y) / view.s };
  }
  // x centrale di un punto (1..24)
  function pointX(i) {
    const col = i <= 12 ? 12 - i : i - 13;      // 0..11 da sinistra
    return M + col * PW + (col >= 6 ? BAR : 0) + PW / 2;
  }
  const isTop = i => i >= 13;
  function checkerPos(i, k, n) {
    const step = n > 5 ? (PH - CR * 2) / (n - 1) : CR * 2;
    const x = pointX(i);
    const y = isTop(i) ? M + CR + k * step : BH - M - CR - k * step;
    return { x, y };
  }
  const barX = () => M + 6 * PW + BAR / 2;
  function barPos(p, k) { return { x: barX(), y: p === 1 ? BH / 2 + 50 + k * CR * 1.6 : BH / 2 - 50 - k * CR * 1.6 }; }
  function offPos(p, k) { return { x: BW - TRAY / 2 - 6, y: p === 1 ? BH - M - 8 - k * 15 : M + 8 + k * 15 }; }

  // ── DISEGNO ─────────────────────────────────────
  function drawBoard(ctx) {
    const wood = ctx.createLinearGradient(0, 0, BW, BH);
    wood.addColorStop(0, '#6b3f1f'); wood.addColorStop(1, '#4a2a13');
    PP.rr(0, 0, BW, BH, 24); ctx.fillStyle = wood; ctx.fill();
    const felt = '#1f5b46';
    ctx.fillStyle = felt;
    ctx.fillRect(M, M, PW * 6, BH - 2 * M);
    ctx.fillRect(M + PW * 6 + BAR, M, PW * 6, BH - 2 * M);
    ctx.fillStyle = '#3a2210'; ctx.fillRect(M + PW * 6, M, BAR, BH - 2 * M);
    ctx.fillStyle = '#2a170a'; ctx.fillRect(BW - TRAY - 4, M, TRAY - 12, BH - 2 * M);
    for (let i = 1; i <= 24; i++) {
      const x = pointX(i), top = isTop(i);
      ctx.fillStyle = i % 2 ? '#c9b48a' : '#8f2d22';
      ctx.beginPath();
      if (top) { ctx.moveTo(x - PW / 2 + 2, M); ctx.lineTo(x + PW / 2 - 2, M); ctx.lineTo(x, M + PH); }
      else { ctx.moveTo(x - PW / 2 + 2, BH - M); ctx.lineTo(x + PW / 2 - 2, BH - M); ctx.lineTo(x, BH - M - PH); }
      ctx.closePath(); ctx.fill();
    }
  }
  function checker(ctx, x, y, p, hl) {
    ctx.save();
    ctx.shadowColor = 'rgba(0,0,0,.45)'; ctx.shadowBlur = 6; ctx.shadowOffsetY = 3;
    const g = ctx.createRadialGradient(x - CR * 0.3, y - CR * 0.35, CR * 0.1, x, y, CR);
    if (p === 1) { g.addColorStop(0, '#ffffff'); g.addColorStop(1, '#d9d2c2'); } else { g.addColorStop(0, '#4a4a4a'); g.addColorStop(1, '#111'); }
    ctx.fillStyle = g; ctx.beginPath(); ctx.arc(x, y, CR, 0, 7); ctx.fill();
    ctx.restore();
    ctx.strokeStyle = p === 1 ? 'rgba(0,0,0,.15)' : 'rgba(255,255,255,.12)'; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.arc(x, y, CR * 0.62, 0, 7); ctx.stroke();
    if (hl) { ctx.strokeStyle = '#ffd54a'; ctx.lineWidth = 5; ctx.beginPath(); ctx.arc(x, y, CR + 2, 0, 7); ctx.stroke(); }
  }
  function die(ctx, x, y, n, size, used, rollT) {
    ctx.save(); ctx.translate(x, y);
    if (rollT > 0) ctx.rotate(rollT * 8);
    ctx.globalAlpha = used ? 0.35 : 1;
    ctx.shadowColor = 'rgba(0,0,0,.4)'; ctx.shadowBlur = 8; ctx.shadowOffsetY = 3;
    PP.rr(-size / 2, -size / 2, size, size, size * 0.18); ctx.fillStyle = '#fbf6ea'; ctx.fill();
    ctx.shadowColor = 'transparent';
    const show = rollT > 0 ? PP.randInt(1, 6) : n;
    const P = { 1: [[0, 0]], 2: [[-1, -1], [1, 1]], 3: [[-1, -1], [0, 0], [1, 1]], 4: [[-1, -1], [1, -1], [-1, 1], [1, 1]], 5: [[-1, -1], [1, -1], [0, 0], [-1, 1], [1, 1]], 6: [[-1, -1], [1, -1], [-1, 0], [1, 0], [-1, 1], [1, 1]] }[show];
    for (const [a, b] of P) { ctx.beginPath(); ctx.arc(a * size * 0.26, b * size * 0.26, size * 0.09, 0, 7); ctx.fillStyle = '#2a1a0e'; ctx.fill(); }
    ctx.restore();
  }

  function draw(ctx, W, H) {
    layout();
    const bg = ctx.createRadialGradient(W / 2, H / 2, 10, W / 2, H / 2, Math.max(W, H) * 0.75);
    bg.addColorStop(0, '#3a2818'); bg.addColorStop(1, '#120c07');
    ctx.fillStyle = bg; ctx.fillRect(0, 0, W, H);
    if (!st) st = fresh();
    ctx.save();
    if (view.rot) { ctx.translate(view.x + BH * view.s, view.y); ctx.rotate(Math.PI / 2); ctx.scale(view.s, view.s); }
    else { ctx.translate(view.x, view.y); ctx.scale(view.s, view.s); }
    ctx.shadowColor = 'rgba(0,0,0,.5)'; ctx.shadowBlur = 30;
    drawBoard(ctx);
    ctx.shadowBlur = 0;

    const human = PP.state === 'playing' && !winner && phase === 'move' && (mode === 1 || turn === 1);
    const legal = human ? legalNow() : [];
    const animTo = new Set(anims.map(a => a.to));
    // pedine sui punti
    for (let i = 1; i <= 24; i++) {
      const v = st.b[i]; if (!v) continue;
      const p = v > 0 ? 1 : 2, n = Math.abs(v);
      for (let k = 0; k < n; k++) {
        if (animTo.has(i) && k === n - 1 && anims.some(a => a.to === i && a.t < 1)) continue;
        const pos = checkerPos(i, k, n);
        const isSel = selected === i && k === n - 1;
        const can = human && k === n - 1 && legal.some(m => m.from === i);
        checker(ctx, pos.x, pos.y, p, isSel);
        if (can && !isSel) { ctx.strokeStyle = 'rgba(255,213,74,.55)'; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(pos.x, pos.y, CR + 1, 0, 7); ctx.stroke(); }
      }
    }
    // barra e uscite
    for (const p of [1, 2]) {
      for (let k = 0; k < st.bar[p]; k++) { const pos = barPos(p, k); checker(ctx, pos.x, pos.y, p, selected === 0 && turn === p && k === st.bar[p] - 1); }
      for (let k = 0; k < st.off[p]; k++) {
        const pos = offPos(p, k);
        ctx.fillStyle = p === 1 ? '#efe8d8' : '#1a1a1a'; PP.rr(pos.x - 28, pos.y - 6, 56, 12, 4); ctx.fill();
        ctx.strokeStyle = 'rgba(0,0,0,.3)'; ctx.lineWidth = 1; ctx.stroke();
      }
    }
    // pedine in movimento
    for (const a of anims) {
      const t = PP.easeInOut(Math.min(1, a.t));
      const fs = a.fromState;
      const fromPos = a.from === 0 ? barPos(a.p, fs.bar[a.p] - 1) : checkerPos(a.from, Math.abs(fs.b[a.from]) - 1, Math.abs(fs.b[a.from]));
      const toPos = a.to === 0 || a.to === 25 ? offPos(a.p, st.off[a.p] - 1) : checkerPos(a.to, Math.abs(st.b[a.to]) - 1, Math.abs(st.b[a.to]));
      checker(ctx, PP.lerp(fromPos.x, toPos.x, t), PP.lerp(fromPos.y, toPos.y, t) - Math.sin(t * Math.PI) * 40, a.p, false);
    }
    // destinazioni
    if (human && selected !== null) {
      for (const m of legal.filter(m => m.from === selected)) {
        if (m.to === 0 || m.to === 25) { ctx.fillStyle = 'rgba(255,213,74,.35)'; ctx.fillRect(BW - TRAY - 4, turn === 1 ? BH / 2 : M, TRAY - 12, BH / 2 - M); continue; }
        const n = Math.abs(st.b[m.to]);
        const pos = checkerPos(m.to, n === 1 && Math.sign(st.b[m.to]) !== sign(turn) ? 0 : n, n + 1);
        ctx.fillStyle = 'rgba(255,213,74,.5)'; ctx.beginPath(); ctx.arc(pos.x, pos.y, CR * 0.55, 0, 7); ctx.fill();
      }
    }
    // dadi sulla metà destra (o sinistra) del tavolo
    if (dice && PP.state !== 'menu') {
      const used = diceUsed.slice();
      const half = turn === 1 ? M + PW * 6 + BAR + PW * 3 : M + PW * 3;
      const ds = dice.length === 4 ? dice : dice;
      ds.forEach((d, i) => {
        const ui = used.indexOf(d); const isUsed = ui >= 0; if (isUsed) used.splice(ui, 1);
        const n = ds.length;
        die(ctx, half + (i - (n - 1) / 2) * 76, BH / 2, d, 60, isUsed, rollAnim);
      });
    }
    ctx.restore();
    PP.drawFx();

    if (PP.state === 'menu') return;
    // HUD fuori dalla tavola
    const name = p => (mode === 0 ? (p === 1 ? 'You' : 'Computer') : p === 1 ? 'White' : 'Black');
    PP.circle(22, 30, 9, turn === 1 ? '#f4efe2' : '#222'); ctx.strokeStyle = '#999'; ctx.lineWidth = 1; ctx.beginPath(); ctx.arc(22, 30, 9, 0, 7); ctx.stroke();
    const status = winner ? 'Game over' : phase === 'nomove' ? `${name(turn)}: no legal moves` : mode === 0 && turn === 2 ? 'Computer is playing…' : `${mode === 0 ? 'Your' : `${name(turn)}'s`} move`;
    PP.text(status, 38, 31, 16, '#fff', 'left', 800);
    PP.text(`Pips — ${name(1)} ${pips(st, 1)} · ${name(2)} ${pips(st, 2)}`, 16, 50, 11, 'rgba(255,255,255,.6)', 'left', 600);
    // pulsanti
    btns = [];
    if (human || (phase === 'done' && (mode === 1 || turn === 1))) {
      const bw = 120, bh = 46, y = H - bh - 12;
      btns.push({ n: 'Undo', x: W / 2 - bw - 6, y, w: bw, h: bh, on: moves.length > 0 });
      btns.push({ n: 'Done', x: W / 2 + 6, y, w: bw, h: bh, on: phase === 'done' });
      for (const b of btns) { PP.rr(b.x, b.y, b.w, b.h, 12); ctx.fillStyle = b.n === 'Done' && b.on ? '#d9a441' : 'rgba(255,255,255,.12)'; ctx.fill(); PP.text(b.n, b.x + b.w / 2, b.y + b.h / 2 + 1, 15, b.on ? (b.n === 'Done' ? '#1d140e' : '#fff') : 'rgba(255,255,255,.35)', 'center', 800); }
    }
  }
  let btns = [];

  // ── INPUT ───────────────────────────────────────
  function pointerDown(p) {
    for (const b of btns) if (b.on && p.x >= b.x && p.x <= b.x + b.w && p.y >= b.y && p.y <= b.y + b.h) {
      if (b.n === 'Undo') undo(); else if (b.n === 'Done') { aiTimer = 0; phase = 'done'; }
      return;
    }
    if (winner || phase !== 'move' || (mode === 0 && turn === 2)) return;
    const l = toLocal(p.x, p.y);
    const legal = legalNow();
    // tocco su una destinazione?
    if (selected !== null) {
      const targets = legal.filter(m => m.from === selected);
      let hit = null;
      for (const m of targets) {
        if (m.to === 0 || m.to === 25) { if (l.x > BW - TRAY - 10) hit = m; continue; }
        if (Math.abs(l.x - pointX(m.to)) < PW / 2 && (isTop(m.to) ? l.y < BH / 2 : l.y > BH / 2)) hit = hit || m;
      }
      if (hit) {
        // se lo stesso arrivo si raggiunge con due dadi diversi preferisci quello più grande
        const same = targets.filter(m => m.to === hit.to);
        doMove(same.sort((a, b) => b.die - a.die)[0]);
        return;
      }
    }
    // selezione di una pedina
    if (st.bar[turn]) { if (legal.some(m => m.from === 0)) { selected = 0; sfx.click(); } return; }
    for (let i = 1; i <= 24; i++) {
      if (Math.abs(l.x - pointX(i)) < PW / 2 && (isTop(i) ? l.y < BH / 2 : l.y > BH / 2)) {
        if (legal.some(m => m.from === i)) { selected = i; sfx.click(); }
        else { selected = null; if (st.b[i] * sign(turn) > 0) sfx.tone(170, 0.08, 'square', 0.06); }
        return;
      }
    }
    selected = null;
  }
  function keyDown(code) { if (code === 'KeyZ' || code === 'Backspace') undo(); if ((code === 'Enter' || code === 'Space') && phase === 'done') aiTimer = 0; }

  function demo(n) {
    st = fresh(); winner = 0; anims = []; turn = 1; rollAnim = 0; phase = 'move';
    if (n === 2) { st.b = Array(25).fill(0); Object.assign(st.b, { 1: 3, 2: 3, 3: 2, 4: 2, 5: 1, 6: 2, 20: -3, 21: -4, 22: -2, 24: -2, 19: -2 }); st.off = [0, 2, 2]; }
    if (n === 3) { Object.assign(st.b, { 24: 1, 13: 4, 8: 2, 6: 4, 5: 2, 7: 1, 1: -2, 12: -4, 17: -3, 19: -4, 20: -2 }); st.bar = [0, 1, 0]; }
    dice = n === 3 ? [5, 5, 5, 5] : n === 2 ? [6, 4] : [3, 1]; diceUsed = n === 3 ? [5] : []; moves = []; turnStart = clone(st); legalCache = null;
    if (n === 1) selected = 8; else if (n === 2) selected = 6; else selected = 0;
    PP.game.update = () => {};
  }

  function icon(c, S) {
    c.fillStyle = '#4a2a13'; c.fillRect(0, 0, S, S);
    c.fillStyle = '#1f5b46'; c.fillRect(S * 0.18, S * 0.18, S * 0.64, S * 0.64);
    const tri = (x, up, col) => { c.fillStyle = col; c.beginPath(); if (up) { c.moveTo(x - S * 0.05, S * 0.82); c.lineTo(x + S * 0.05, S * 0.82); c.lineTo(x, S * 0.5); } else { c.moveTo(x - S * 0.05, S * 0.18); c.lineTo(x + S * 0.05, S * 0.18); c.lineTo(x, S * 0.5); } c.fill(); };
    for (let i = 0; i < 6; i++) { const x = S * (0.23 + i * 0.108); tri(x, true, i % 2 ? '#c9b48a' : '#8f2d22'); tri(x, false, i % 2 ? '#8f2d22' : '#c9b48a'); }
    const ck = (x, y, p) => { const g = c.createRadialGradient(x - 8, y - 8, 2, x, y, S * 0.06); if (p === 1) { g.addColorStop(0, '#fff'); g.addColorStop(1, '#d9d2c2'); } else { g.addColorStop(0, '#555'); g.addColorStop(1, '#111'); } c.fillStyle = g; c.beginPath(); c.arc(x, y, S * 0.05, 0, 7); c.fill(); };
    ck(S * 0.23, S * 0.77, 1); ck(S * 0.23, S * 0.67, 1); ck(S * 0.77, S * 0.23, 2); ck(S * 0.77, S * 0.33, 2);
    const dd = (x, y, n) => { c.save(); c.translate(x, y); c.rotate(n === 5 ? 0.2 : -0.15); c.fillStyle = '#fbf6ea'; c.beginPath(); c.roundRect(-S * 0.07, -S * 0.07, S * 0.14, S * 0.14, S * 0.025); c.fill(); c.fillStyle = '#2a1a0e'; const P = n === 5 ? [[-1, -1], [1, -1], [0, 0], [-1, 1], [1, 1]] : [[-1, -1], [0, 0], [1, 1]]; for (const [a, b] of P) { c.beginPath(); c.arc(a * S * 0.035, b * S * 0.035, S * 0.012, 0, 7); c.fill(); } c.restore(); };
    dd(S * 0.44, S * 0.5, 5); dd(S * 0.6, S * 0.52, 3);
  }

  const realUpdate = update;
  PP.run({
    id: GAME_ID,
    title: 'Backgammon',
    intro: 'Move all your checkers home and bear them off first.\nRoll, hit lone checkers, and avoid being hit.',
    choices: () => [
      { label: 'Opponent', options: MODES, value: mode, onChange: i => { mode = i; store.set('mode', i); PP.showMain(); } },
      ...(mode === 0 ? [{ label: 'Difficulty', options: LEVELS, value: level, onChange: i => { level = i; store.set('level', i); PP.showMain(); } }] : []),
    ],
    bestText: () => { if (mode) return ''; const s = store.get(`stats-${level}`, { w: 0, l: 0 }); return `${LEVELS[level]}: ${s.w} wins · ${s.l} losses`; },
    pauseText: () => `Pips: ${pips(st, 1)} – ${pips(st, 2)}`,
    init() { mode = store.get('mode', 0); level = store.get('level', 1); st = fresh(); },
    start() { PP.game.update = realUpdate; PP.game.overDelay = 650; start(); },
    update, draw, pointerDown, keyDown, demo, icon,
  });
})();

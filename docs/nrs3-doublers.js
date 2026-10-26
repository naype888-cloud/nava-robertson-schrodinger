// The eight corners of the open box: position and the standing waves, driven by the page itself
// (window.NRS3Shared, written by nrs3-box.js on every frame): the same box dx × dy × dz, the same
// Ψ(t) of the transport, the same turn.
// Position: the corners {0, d−1}³ are NOT neighbours (no seam); each has three links. The colour is
// the staggered sign ε = (−1)^(x+y+z), which anticommutes with the path transport.
// Waves: the standing waves of the path, speed λ_k = cos((k+1)π/(d+1))/cos(π/(d+1)); ε sends the wave
// k to d−1−k (opposite speed). The 8 extreme waves k ∈ {0, d−1} are the ones ε exchanges.
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const CORNERS = [];
  for (const a of [0, 1]) for (const b of [0, 1]) for (const c of [0, 1]) CORNERS.push([a, b, c]);
  const ST = () => window.NRS3Shared;
  function rot([x, y, z]) {
    const { yaw, pitch } = ST(), cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x1 = cy * x + sy * z, z1 = -sy * x + cy * z;
    return [x1, cp * y - sp * z1, sp * y + cp * z1];
  }
  const proj = (v, cx, cy, S) => { const [x, y, z] = rot(v), f = 3.6 / (3.6 + z); return [cx + x * S * f, cy - y * S * f, z, f]; };
  const W = ([x, y, z]) => [x, z, y];
  function setup(c) {
    const r = c.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, r.width, r.height);
    return [g, r.width, r.height];
  }
  const dark = () => css("--bg").startsWith("#0") || css("--bg").startsWith("#1");
  const sgnCol = (s) => css(s > 0 ? "--blue" : "--orange");
  const hue = (ph, a = 1) => `hsla(${((ph * 180 / Math.PI) % 360 + 360) % 360}, ${dark() ? 70 : 80}%, ${dark() ? 62 : 45}%, ${a})`;
  function cube(g, cx, cy, S, h, col, dash) {
    const C = [];
    for (const a of [-h, h]) for (const b of [-h, h]) for (const c of [-h, h]) C.push([a, b, c]);
    g.strokeStyle = col; g.lineWidth = 1; if (dash) g.setLineDash(dash);
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(([i, j]) => {
      const p = proj(W(C[i]), cx, cy, S), q = proj(W(C[j]), cx, cy, S);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    });
    g.setLineDash([]);
  }
  const ball = (g, P, r, fill, ring, lw = 1.5) => {
    g.fillStyle = fill; g.beginPath(); g.arc(P[0], P[1], Math.max(1.2, r * P[3]), 0, 2 * Math.PI); g.fill();
    if (ring) { g.strokeStyle = ring; g.lineWidth = lw; g.stroke(); }
  };
  const label = (g, txt, x, y, col, size = 12) => { g.font = `${size}px system-ui, sans-serif`; g.fillStyle = col; g.fillText(txt, x, y); };
  function legend(g, items, tail) {
    let x = 10; g.font = "12px system-ui, sans-serif";
    for (const [col, txt] of items) {
      g.fillStyle = col; g.beginPath(); g.arc(x + 4, 14, 4, 0, 7); g.fill();
      g.fillStyle = css("--ink2"); g.fillText(txt, x + 12, 18); x += 12 + g.measureText(txt).width + 14;
    }
    if (tail) { g.fillStyle = css("--ink2"); g.fillText(tail, x, 18); }
  }
  const par = (j) => (j % 2 ? -1 : 1);
  const eps = (p) => par(p[0] + p[1] + p[2]);
  const site = (c) => c.map((v, i) => (v ? ST().box[i] - 1 : 0));          // corner bit 1 → d − 1, 0 → 0 (no seam)
  const wave = (c) => c.map((v, i) => (v ? ST().box[i] - 1 : 0));          // extreme wave: bit 1 → slowest (k = d−1)
  const pair = (k) => k.map((v, i) => ST().box[i] - 1 - v);                // ε: k → d − 1 − k
  let PROB, PHASE, MODE, mass = 0, fiber = false, time = 0, phi4 = 0;
  const effMass = () => (fiber ? 0.5 : mass);
  function four([x, y, z, w]) {
    const c = Math.cos(phi4), s = Math.sin(phi4), x1 = c * x - s * w, w1 = s * x + c * w, f = 2.4 / (2.4 + w1);
    return [x1 * f, y * f, z * f];
  }
  const wAxis = (i, k) => MODE[i][k];

  function drawPos() {
    const { box } = ST(), [g, w, h] = setup($("dpos")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22;
    const m = Math.max(...box), s = 2 / (m - 1 || 1), hx = box.map((d) => (d - 1) * s / 2);
    cube(g, cx, cy, S, 1, css("--grid"));
    const pmax = PROB.map((p) => Math.max(...p)).reduce((a, b) => a * b, 1);
    const idx = box.map((d) => { const n = Math.min(d, 14); return Array.from({ length: n }, (_, k) => Math.round(k * (d - 1) / (n - 1 || 1))); });
    const pts = [];
    for (const i of idx[0]) for (const j of idx[1]) for (const k of idx[2]) {
      const corner = [i, j, k].every((v, a) => v === 0 || v === box[a] - 1);
      pts.push([proj(W([i * s - hx[0], j * s - hx[1], k * s - hx[2]]), cx, cy, S), corner, [i, j, k], PROB[0][i] * PROB[1][j] * PROB[2][k] / pmax]);
    }
    pts.sort((a, b) => b[0][2] - a[0][2]);
    for (const [P, corner, p, pr] of pts) {
      const ph = PHASE[0][p[0]] + PHASE[1][p[1]] + PHASE[2][p[2]];
      if (!corner) { if (pr > 0.01) ball(g, P, S * 0.05 * Math.sqrt(pr), hue(ph, 0.35)); else { g.fillStyle = css("--grid"); g.fillRect(P[0] - 1, P[1] - 1, 2, 2); } continue; }
      ball(g, P, S * (0.03 + 0.09 * Math.sqrt(pr)), hue(ph), sgnCol(eps(p)), 2.5);
    }
    legend(g, [[sgnCol(1), "ε = +1"], [sgnCol(-1), "ε = −1"]], "· size |Ψ(t)|² · colour phase");
    label(g, "no seam: the 8 corners are not linked to each other", 10, h - 28, css("--green"));
    label(g, `${box.join(" × ")} · open box`, 10, h - 10, css("--muted"));
  }
  function drawPosMini(cv, c) {
    const { box } = ST(), [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 4, S = Math.min(w, h) * 0.32;
    const p = site(c), pmax = PROB.map((q) => Math.max(...q)).reduce((a, b) => a * b, 1);
    for (let mu = 0; mu < 3; mu++) for (const dir of [1, -1]) {
      const q = p[mu] + dir, wall = q < 0 || q > box[mu] - 1, e = [0, 0, 0]; e[mu] = dir;
      const P0 = proj(W([0, 0, 0]), cx, cy, S), P1 = proj(W(e.map((v) => v * 0.85)), cx, cy, S);
      g.strokeStyle = wall ? css("--red") : css("--ink2"); g.lineWidth = 1.4;
      if (wall) g.setLineDash([2, 3]);
      g.beginPath(); g.moveTo(P0[0], P0[1]); g.lineTo(P1[0], P1[1]); g.stroke(); g.setLineDash([]);
      if (!wall) ball(g, P1, S * 0.1, css("--grid"));
    }
    const pr = PROB[0][p[0]] * PROB[1][p[1]] * PROB[2][p[2]];
    ball(g, proj(W([0, 0, 0]), cx, cy, S), S * (0.08 + 0.18 * Math.sqrt(pr / pmax)), hue(PHASE[0][p[0]] + PHASE[1][p[1]] + PHASE[2][p[2]]), sgnCol(eps(p)), 2.5);
    label(g, `(${p.join(",")})`, 5, 13, css("--ink2"), 10.5);
    label(g, `3 links · |Ψ|² ${(100 * pr).toFixed(2)}%`, 5, h - 6, css("--muted"), 10);
  }

  // waves: every standing wave k of the box at its speed λ_k, the 8 extremes marked, ε pairs by lines through the centre
  function drawMom() {
    const { box, A } = ST(), [g, w, h] = setup($("dmom")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22;
    cube(g, cx, cy, S, 1, css("--grid")); cube(g, cx, cy, S, 0.5, css("--grid"), [3, 3]);
    const mmax = MODE.map((q) => Math.max(...q)).reduce((a, b) => a * b, 1);
    const ext = new Set(CORNERS.map((c) => wave(c).join(",")));
    const idx = box.map((d) => Array.from({ length: d }, (_, k) => k));
    const lam = (i, k) => A[i].lam[k];
    const pts = [];
    for (const a of idx[0]) for (const b of idx[1]) for (const c of idx[2]) {
      const k = [a, b, c];
      pts.push([proj(W([lam(0, a), lam(1, b), lam(2, c)]), cx, cy, S), k, MODE[0][a] * MODE[1][b] * MODE[2][c] / mmax]);
    }
    pts.sort((p, q) => q[0][2] - p[0][2]);
    const sg = (k) => k.reduce((s, v, i) => s * (lam(i, v) >= 0 ? 1 : -1), 1);
    for (const c of CORNERS) {   // ε: k → d−1−k, drawn once per pair
      const k = [0, 1, 2].map((i) => (c[i] ? box[i] - 1 : 0)), k2 = pair(k);
      if (k.join() > k2.join()) continue;
      const P = proj(W(k.map((v, i) => lam(i, v))), cx, cy, S), Q = proj(W(k2.map((v, i) => lam(i, v))), cx, cy, S);
      g.strokeStyle = css("--violet"); g.globalAlpha = 0.5; g.setLineDash([4, 3]); g.beginPath(); g.moveTo(P[0], P[1]); g.lineTo(Q[0], Q[1]); g.stroke(); g.setLineDash([]); g.globalAlpha = 1;
    }
    for (const [P, k, pr] of pts) {
      if (ext.has(k.join(","))) { ball(g, P, S * (0.04 + 0.08 * Math.sqrt(pr)), css("--ink"), sgnCol(sg(k)), 2.5); continue; }
      g.fillStyle = css("--muted"); g.globalAlpha = 0.25 + 0.6 * Math.sqrt(pr);
      g.beginPath(); g.arc(P[0], P[1], Math.max(1, S * 0.06 * Math.sqrt(pr) * P[3]), 0, 7); g.fill(); g.globalAlpha = 1;
    }
    legend(g, [[sgnCol(1), "sign of the speed product +"], [sgnCol(-1), "−"]], "· size |⟨k|Ψ⟩|² · m = " + effMass().toFixed(2));
    label(g, "violet: ε sends k to d−1−k (opposite speed); one wave per speed, no doubler", 10, h - 28, css("--violet"));
    label(g, "speed cube [−1, 1]³ · dashed: half speed", 10, h - 10, css("--muted"));
  }
  function drawModeMini(cv, c) {
    const { A } = ST(), [g, w, h] = setup(cv), k = wave(c), k2 = pair(k);
    const x0 = 6, x1 = w - 6, yb = h - 20, yt = 22;
    for (let i = 0; i < 3; i++) {
      const d = A[i].d, row = yt + (yb - yt) * i / 2;
      const f = (kk) => Array.from({ length: d }, (_, j) => A[i].U[kk][j]);
      for (const [kk, col, dash] of [[k[i], css("--blue"), []], [k2[i], css("--violet"), [3, 3]]]) {
        const u = f(kk), amp = (yb - yt) / 5 / (Math.max(...u.map(Math.abs)) || 1);
        g.strokeStyle = col; g.setLineDash(dash); g.lineWidth = 1.2; g.beginPath();
        u.forEach((v, j) => { const X = x0 + (x1 - x0) * (j / Math.max(1, d - 1)); j ? g.lineTo(X, row - v * amp) : g.moveTo(X, row - v * amp); });
        g.stroke(); g.setLineDash([]);
      }
    }
    const wgt = k.reduce((p, kk, i) => p * MODE[i][kk], 1);
    label(g, `k = (${k.join(",")})`, 5, 13, css("--ink2"), 10);
    label(g, `Ψ on it ${(100 * wgt).toFixed(1)}%`, 5, h - 6, css("--orange"), 10);
  }


  // ---------- bottom: the extreme wave on the corner cube (3D or 4D) ----------
  const energy = (k) => Math.sqrt(k.reduce((s, v, i) => s + ST().A[i].lam[v] ** 2, 0) + effMass() ** 2);
  function blockPoints(c, t) {
    const { A } = ST(), k = wave(c), E = energy(k), out = [];
    for (const w of fiber ? [0, 1, 2] : [0]) for (const x of CORNERS) {
      const p = site(x), sg = p.reduce((s, v, i) => s + (A[i].U[k[i]][v] < 0 ? Math.PI : 0), 0);
      const q = x.map((v) => v - 0.5), pw = fiber ? (w - 1) * 0.55 : 0;
      out.push({ v: fiber ? four([q[0], q[1], q[2], pw]) : q, ph: sg + (fiber ? 2 * Math.PI * w / 3 : 0) - E * t, e: eps(p), w, x, pr: PROB[0][p[0]] * PROB[1][p[1]] * PROB[2][p[2]] });
    }
    return out;
  }
  function drawBlock(g, cx, cy, S, c, t, r, off = [0, 0, 0], kk = 1) {
    const P = blockPoints(c, t), pr = P.map((q) => proj(W(q.v.map((v, m) => off[m] + v * kk)), cx, cy, S));
    const pm = Math.max(...P.map((q) => q.pr)) || 1;
    g.strokeStyle = css("--grid"); g.lineWidth = 1;
    for (let i = 0; i < P.length; i++) for (let j = i + 1; j < P.length; j++) {
      const a = P[i], b = P[j], dx = a.x.reduce((n, v, m) => n + Math.abs(v - b.x[m]), 0);
      if (!((a.w === b.w && dx === 1) || (dx === 0 && Math.abs(a.w - b.w) === 1))) continue;
      g.beginPath(); g.moveTo(pr[i][0], pr[i][1]); g.lineTo(pr[j][0], pr[j][1]); g.stroke();
    }
    P.map((q, i) => [q, pr[i]]).sort((a, b) => b[1][2] - a[1][2])
      .forEach(([q, p]) => ball(g, p, r * (0.6 + 0.6 * Math.sqrt(q.pr / pm)), hue(q.ph), sgnCol(q.e)));
  }
  function drawSum() {
    const [g, w, h] = setup($("dsum")), cx = w / 2, cy = h / 2 + 4, S = Math.min(w / 2.4, h) * 0.19;
    cube(g, cx, cy, S, 1, css("--grid"), [3, 3]);
    CORNERS.map((c) => { const s = c.map((v) => (v ? 1 : -1)); return [proj(W(s), cx, cy, S), s, c]; })
      .sort((a, b) => b[0][2] - a[0][2]).forEach(([, s, c]) => drawBlock(g, cx, cy, S, c, time, S * 0.045, s, 0.5));
    label(g, fiber ? "box × w: each extreme wave on the 2×2×2×3 block, phase sign + 2πw/3 − E t, size |Ψ(t)|²"
      : "each extreme wave k (outer corner) on the corner sites x (inner block): colour sign(k, x) − E t, size |Ψ(t)|²", 10, h - 10, css("--muted"));
  }
  function drawSumMini(cv, c) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.42, k = wave(c);
    drawBlock(g, cx, cy, S, c, time, S * 0.09);
    label(g, `k = (${k.join(",")})`, 5, 13, css("--ink2"), 10);
    label(g, `E ${energy(k).toFixed(2)}`, 5, h - 6, css("--orange"), 10);
  }

  const minis = { mpos: [], mmom: [], msum: [] };
  for (const id of Object.keys(minis)) CORNERS.forEach((c, i) => {
    const cv = document.createElement("canvas"); cv.setAttribute("aria-label", `local zoom on corner ${i + 1}`);
    $(id).appendChild(cv); minis[id].push([cv, c]);
  });
  for (const c of [$("dpos"), $("dmom"), $("dsum"), ...Object.values(minis).flat().map(([cv]) => cv)]) {
    let drag = null;
    c.addEventListener("pointerdown", (e) => { const s = ST(); if (!s) return; drag = [e.clientX, e.clientY, s.yaw, s.pitch]; c.setPointerCapture(e.pointerId); });
    c.addEventListener("pointermove", (e) => {
      if (!drag) return;
      window.NRS3Rotate(drag[2] + (e.clientX - drag[0]) * 0.01, Math.max(-1.45, Math.min(1.45, drag[3] + (e.clientY - drag[1]) * 0.01)));
    });
    c.addEventListener("pointerup", () => { drag = null; });
  }
  $("dmass").addEventListener("input", (e) => { mass = +e.target.value; $("vmass").textContent = mass.toFixed(2); });
  $("dfiber").addEventListener("click", (e) => {
    fiber = !fiber; e.target.setAttribute("aria-pressed", String(fiber));
    $("dmass").disabled = fiber; $("vmass").textContent = fiber ? "½ (fibre)" : mass.toFixed(2);
  });
  const visible = (el) => { const r = el.getBoundingClientRect(); return r.bottom > 0 && r.top < innerHeight; };
  let last = 0;
  function frame(ts) {
    const dt = last ? Math.min(0.05, (ts - last) / 1000) : 0; last = ts;
    if (ST() && visible($("dblcard"))) {
      const { V, A } = ST(); time = ST().t; phi4 += dt * 0.5;
      PROB = V.map((v) => Array.from(v.re, (r, j) => r * r + v.im[j] * v.im[j]));
      PHASE = V.map((v) => Array.from(v.re, (r, j) => Math.atan2(v.im[j], r)));
      MODE = A.map((a) => a.cr.map((r, k) => r * r + a.ci[k] * a.ci[k]));
      drawPos(); drawMom(); drawSum();
      minis.mpos.forEach(([cv, c]) => drawPosMini(cv, c));
      minis.mmom.forEach(([cv, c]) => drawModeMini(cv, c));
      minis.msum.forEach(([cv, c]) => drawSumMini(cv, c));
    }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
})();

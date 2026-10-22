// The eight corners of T³: position, momentum and their sum, driven by the page itself
// (window.NRS3Shared, written by t3-box.js on every frame): the same torus dx × dy × dz, the same
// Ψ(t) of the transport, the same turn.
// Position: the corners {0, d−1}³ are neighbours through the three seams, one 2×2×2 cube; they light
// up with |Ψ(t)|². The colour is the staggered sign ε = (−1)^(x+y+z) (Dirac's β); on an odd axis it
// does not alternate across the seam, and the staggered Dirac operator does not close.
// Momentum: |Ψ(t)|² in momentum on the Brillouin cube; the doublers are the modes at (±π/2)³, exact
// when 4 divides the size, the nearest modes otherwise; index ±1, adding to 0.
// Sum: the phase θ·x of each doubler on the corner cube, with the weight of Ψ(t) on it; the closed
// fibre w adds a fourth axis (D₄ = D₃ + ε T_w, Kaluza–Klein masses 1, −½, −½).
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const CORNERS = [];
  for (const a of [0, 1]) for (const b of [0, 1]) for (const c of [0, 1]) CORNERS.push([a, b, c]);
  let mass = 0, fiber = false, time = 0, phi4 = 0;
  const ST = () => window.NRS3Shared;

  function rot([x, y, z]) {
    const { yaw, pitch } = ST(), cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x1 = cy * x + sy * z, z1 = -sy * x + cy * z;
    return [x1, cp * y - sp * z1, sp * y + cp * z1];
  }
  const proj = (v, cx, cy, S) => { const [x, y, z] = rot(v), f = 3.6 / (3.6 + z); return [cx + x * S * f, cy - y * S * f, z, f]; };
  const W = ([x, y, z]) => [x, z, y];
  function four([x, y, z, w]) {
    const c = Math.cos(phi4), s = Math.sin(phi4), x1 = c * x - s * w, w1 = s * x + c * w, f = 2.4 / (2.4 + w1);
    return [x1 * f, y * f, z * f];
  }
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

  // ---------- what the page says ----------
  const par = (j) => (j % 2 ? -1 : 1);
  const eps = (p) => par(p[0] + p[1] + p[2]);
  const eta = ([x, y]) => [1, par(x), par(x + y)];
  const site = (c) => c.map((v, i) => (v ? 0 : ST().box[i] - 1));    // corner block: 0 → d − 1, 1 → 0 (across the seam)
  const probAxis = () => ST().V.map((v) => Array.from(v.re, (r, j) => r * r + v.im[j] * v.im[j]));
  const phaseAxis = () => ST().V.map((v) => Array.from(v.re, (r, j) => Math.atan2(v.im[j], r)));
  function dft(v) {   // |⟨k|ψ⟩|² for every mode k of one axis
    const d = v.re.length, out = new Array(d).fill(0);
    for (let k = 0; k < d; k++) {
      let re = 0, im = 0;
      for (let j = 0; j < d; j++) { const th = -2 * Math.PI * k * j / d, c = Math.cos(th), s = Math.sin(th); re += v.re[j] * c - v.im[j] * s; im += v.re[j] * s + v.im[j] * c; }
      out[k] = (re * re + im * im) / d;
    }
    return out;
  }
  const near = () => ST().box.map((d) => [Math.round(d / 4) % d, Math.round(3 * d / 4) % d]);
  const doubler = (c) => { const n = near(); return c.map((v, i) => n[i][v ? 0 : 1]); };   // corner bit 1 → θ ≈ +π/2
  const thetaOf = (d, k) => { const t = 2 * Math.PI * k / d; return t > Math.PI ? t - 2 * Math.PI : t; };
  const index = (ks) => ks.reduce((s, k, i) => s * -Math.sign(Math.sin(thetaOf(ST().box[i], k))), 1);
  const exactAxis = (i) => ST().box[i] % 4 === 0;
  const oddAxes = () => ST().box.map((d, i) => (d % 2 ? "xyz"[i] : null)).filter(Boolean);
  let PROB, PHASE, MOM;
  const effMass = () => (fiber ? 0.5 : mass);

  // ---------- top left: position ----------
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
      if (!corner) { if (pr > 0.01) ball(g, P, S * 0.05 * Math.sqrt(pr), hue(PHASE[0][p[0]] + PHASE[1][p[1]] + PHASE[2][p[2]], 0.35)); else { g.fillStyle = css("--grid"); g.fillRect(P[0] - 1, P[1] - 1, 2, 2); } continue; }
      ball(g, P, S * (0.03 + 0.09 * Math.sqrt(pr)), hue(PHASE[0][p[0]] + PHASE[1][p[1]] + PHASE[2][p[2]]), sgnCol(eps(p)), 2.5);
    }
    legend(g, [[sgnCol(1), "ring ε = +1"], [sgnCol(-1), "ring ε = −1"]], "· size |Ψ(t)|² · colour phase");
    const odd = oddAxes();
    if (odd.length) label(g, `✕ ${odd.join(", ")} odd: ε does not alternate across the seam`, 10, h - 28, css("--red"));
    label(g, `${box.join(" × ")} · the 8 corners are one 2×2×2 cube through the seams`, 10, h - 10, css("--muted"));
  }
  function drawPosMini(cv, c) {
    const { box } = ST(), [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 4, S = Math.min(w, h) * 0.32;
    const p = site(c), et = eta(p), pmax = PROB.map((q) => Math.max(...q)).reduce((a, b) => a * b, 1);
    let seamBreak = false;
    for (let mu = 0; mu < 3; mu++) for (const dir of [1, -1]) {
      const e = [0, 0, 0]; e[mu] = dir;
      const nb = p.map((v, k) => (v + e[k] + box[k]) % box[k]), seam = Math.abs(nb[mu] - p[mu]) > 1;
      if (seam && eps(nb) === eps(p)) seamBreak = true;
      const P0 = proj(W([0, 0, 0]), cx, cy, S), P1 = proj(W(e.map((v) => v * 0.85)), cx, cy, S);
      g.strokeStyle = seam ? css("--violet") : css("--ink2"); g.lineWidth = seam ? 2.4 : 1.4;
      if (et[mu] < 0) g.setLineDash([4, 3]);
      g.beginPath(); g.moveTo(P0[0], P0[1]); g.lineTo(P1[0], P1[1]); g.stroke(); g.setLineDash([]);
      ball(g, P1, S * 0.1, seam ? sgnCol(eps(nb)) : css("--grid"));
    }
    const pr = PROB[0][p[0]] * PROB[1][p[1]] * PROB[2][p[2]];
    ball(g, proj(W([0, 0, 0]), cx, cy, S), S * (0.08 + 0.18 * Math.sqrt(pr / pmax)), hue(PHASE[0][p[0]] + PHASE[1][p[1]] + PHASE[2][p[2]]), sgnCol(eps(p)), 2.5);
    label(g, `(${p.join(",")})`, 5, 13, css("--ink2"), 10.5);
    label(g, seamBreak ? "seam: same ε ✕" : `|Ψ|² ${(100 * pr).toFixed(2)}%`, 5, h - 6, seamBreak ? css("--red") : css("--muted"), 10);
  }

  // ---------- top right: momentum ----------
  function drawMom() {
    const { box } = ST(), [g, w, h] = setup($("dmom")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22;
    cube(g, cx, cy, S, 1, css("--grid")); cube(g, cx, cy, S, 0.5, css("--grid"), [3, 3]);
    const mmax = MOM.map((q) => Math.max(...q)).reduce((a, b) => a * b, 1);
    const dbl = new Set(CORNERS.map((c) => doubler(c).join(",")));
    const idx = box.map((d) => Array.from({ length: d }, (_, k) => k));
    const pts = [];
    for (const a of idx[0]) for (const b of idx[1]) for (const c of idx[2]) {
      const k = [a, b, c], th = k.map((v, i) => thetaOf(box[i], v) / Math.PI);
      pts.push([proj(W(th), cx, cy, S), k, MOM[0][a] * MOM[1][b] * MOM[2][c] / mmax]);
    }
    pts.sort((p, q) => q[0][2] - p[0][2]);
    for (const [P, k, pr] of pts) {
      if (dbl.has(k.join(","))) { ball(g, P, S * (0.04 + 0.08 * Math.sqrt(pr)), css("--ink"), sgnCol(index(k)), 2.5); continue; }
      g.fillStyle = css("--muted"); g.globalAlpha = 0.25 + 0.6 * Math.sqrt(pr);
      g.beginPath(); g.arc(P[0], P[1], Math.max(1, S * 0.06 * Math.sqrt(pr) * P[3]), 0, 7); g.fill(); g.globalAlpha = 1;
    }
    legend(g, [[sgnCol(1), "index +1"], [sgnCol(-1), "index −1"]], "· size |Ψ(t)|² in momentum");
    const inexact = box.map((d, i) => (d % 4 ? "xyz"[i] : null)).filter(Boolean);
    label(g, inexact.length ? `4 ∤ size on ${inexact.join(", ")}: nearest modes to ±π/2` : "4 divides every size: the doublers are exact", 10, h - 28, css(inexact.length ? "--orange" : "--green"));
    label(g, "Brillouin cube (−π, π]³ · dashed: (±π/2)³", 10, h - 10, css("--muted"));
  }
  function drawMomMini(cv, c) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 6, S = Math.min(w, h) * 0.34, m = effMass();
    const k = doubler(c), ix = index(k), n = 9, col = sgnCol(ix);
    for (const sheet of [1, -1]) {
      g.strokeStyle = col; g.globalAlpha = sheet > 0 ? 0.9 : 0.45; g.lineWidth = 1;
      for (let a = 0; a < n; a++) for (const along of [0, 1]) {
        g.beginPath();
        for (let b = 0; b <= 24; b++) {
          const u = -1 + 2 * a / (n - 1), v = -1 + 2 * b / 24, [qx, qy] = along ? [u, v] : [v, u];
          const P = proj(W([qx * 0.8, qy * 0.8, sheet * Math.sqrt(qx * qx + qy * qy + m * m) * 0.55]), cx, cy, S);
          b ? g.lineTo(P[0], P[1]) : g.moveTo(P[0], P[1]);
        }
        g.stroke();
      }
    }
    g.globalAlpha = 1;
    const wgt = k.reduce((p, kk, i) => p * MOM[i][kk], 1);
    label(g, `k = (${k.join(",")})${k.every((_, i) => exactAxis(i)) ? "" : " ≈"}`, 5, 13, css("--ink2"), 10);
    label(g, `index ${ix > 0 ? "+1" : "−1"} · Ψ ${(100 * wgt).toFixed(1)}%`, 5, h - 6, col, 10);
  }

  // ---------- bottom: the doubler phase on the corner cube (3D or 4D) ----------
  function blockPoints(c, t) {
    const { box } = ST(), k = doubler(c), th = k.map((v, i) => thetaOf(box[i], v)), m = effMass(), out = [];
    for (const w of fiber ? [0, 1, 2] : [0]) for (const x of CORNERS) {
      const p = site(x), ph = th[0] * p[0] + th[1] * p[1] + th[2] * p[2] + (fiber ? 2 * Math.PI * w / 3 : 0) - m * t;
      const q = x.map((v) => v - 0.5), pw = fiber ? (w - 1) * 0.55 : 0;
      out.push({ v: fiber ? four([q[0], q[1], q[2], pw]) : q, ph, e: eps(p), w, x, pr: PROB[0][p[0]] * PROB[1][p[1]] * PROB[2][p[2]] });
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
  const wOn = (c) => doubler(c).reduce((p, kk, i) => p * MOM[i][kk], 1);
  function drawSum() {
    const [g, w, h] = setup($("dsum")), cx = w / 2, cy = h / 2 + 4, S = Math.min(w / 2.4, h) * 0.19;
    cube(g, cx, cy, S, 1, css("--grid"), [3, 3]);
    CORNERS.map((c) => { const s = c.map((v) => (v ? 1 : -1)); return [proj(W(s), cx, cy, S), s, c]; })
      .sort((a, b) => b[0][2] - a[0][2]).forEach(([, s, c]) => drawBlock(g, cx, cy, S, c, time, S * 0.045, s, 0.5));
    label(g, fiber ? "T³ × w: each doubler on the 2×2×2×3 block, phase θ·x + 2πw/3 − (½)t, size |Ψ(t)|²"
      : "each doubler θ (outer corner) on the corner cube x (inner block): colour θ·x − m t, size |Ψ(t)|²", 10, h - 10, css("--muted"));
  }
  function drawSumMini(cv, c) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.42;
    drawBlock(g, cx, cy, S, c, time, S * 0.09);
    label(g, `k = (${doubler(c).join(",")})`, 5, 13, css("--ink2"), 10);
    label(g, `Ψ on it ${(100 * wOn(c)).toFixed(1)}%`, 5, h - 6, css("--orange"), 10);
  }

  // ---------- minis, controls, loop ----------
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
      time = ST().t; phi4 += dt * 0.5;
      PROB = probAxis(); PHASE = phaseAxis(); MOM = ST().V.map(dft);
      drawPos(); drawMom(); drawSum();
      minis.mpos.forEach(([cv, c]) => drawPosMini(cv, c));
      minis.mmom.forEach(([cv, c]) => drawMomMini(cv, c));
      minis.msum.forEach(([cv, c]) => drawSumMini(cv, c));
    }
    requestAnimationFrame(frame);
  }
  if (location.hash === "#fibre") $("dfiber").click();
  requestAnimationFrame(frame);
})();

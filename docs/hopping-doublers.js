// The eight doublers on the hopping page, driven by the page itself (window.NRS3Shared, written by
// hopping.js on every frame): the same torus dx × dy × dz, the same mode, the same Ψ(s), the same turn.
// Every mode (a, b, c) sits at (cos θa, cos θb, cos θc) in the cube of cosines.
// Hopping: E = −2t Σ cos vanishes on the plane Σ cos = 0. Dirac (Kogut–Susskind signs, even sizes):
// E = ±√(Σ cos² + m²) vanishes only at the origin, the 8 doublers (±π/2)³, which exist exactly when
// 4 divides every size; otherwise the 8 nearest modes are drawn and the gap stays open.
// Sum: in the squares, E² − m² = cos² + cos² + cos² (TorusDirac3.dirac3_sq); Ψ(s) sits at ⟨T²⟩ per axis.
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  let mass = 0, fiber = false;
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
  const diverge = (u) => `hsl(${u < 0 ? 214 : 18}, ${dark() ? 70 : 75}%, ${dark() ? 62 - 30 * (1 - Math.abs(u)) : 45 + 25 * (1 - Math.abs(u))}%)`;
  const seq = (u) => `hsl(${150 - 120 * Math.min(1, u)}, ${dark() ? 60 : 65}%, ${dark() ? 60 : 42}%)`;
  const mEff = () => (fiber ? 0.5 : mass);
  function cubeEdges(g, cx, cy, S) {
    const C = [];
    for (const a of [-1, 1]) for (const b of [-1, 1]) for (const c of [-1, 1]) C.push([a, b, c]);
    g.strokeStyle = css("--grid"); g.lineWidth = 1;
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(([i, j]) => {
      const p = proj(W(C[i]), cx, cy, S), q = proj(W(C[j]), cx, cy, S);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    });
  }
  const dot = (g, P, r, fill, ring, lw = 1.5) => {
    g.fillStyle = fill; g.beginPath(); g.arc(P[0], P[1], Math.max(1, r * P[3]), 0, 7); g.fill();
    if (ring) { g.strokeStyle = ring; g.lineWidth = lw; g.stroke(); }
  };
  const ringAt = (g, P, r, col) => { g.strokeStyle = col; g.lineWidth = 2; g.beginPath(); g.arc(P[0], P[1], r, 0, 7); g.stroke(); };
  const text = (g, s, x, y, col, size = 12) => { g.font = `${size}px system-ui, sans-serif`; g.fillStyle = col; g.fillText(s, x, y); };

  // ---------- what the page says, read once per frame ----------
  const cosOf = (d, a) => Math.cos(2 * Math.PI * a / d);
  let key = "", POINTS = [], SQUARES = [], NEAR = [];
  function refresh(box) {
    const k = box.join("x"); if (k === key) return; key = k;
    const m = new Map(), q = new Map();
    for (let a = 0; a < box[0]; a++) for (let b = 0; b < box[1]; b++) for (let c = 0; c < box[2]; c++) {
      const p = [cosOf(box[0], a), cosOf(box[1], b), cosOf(box[2], c)].map((v) => Math.round(v * 1e9) / 1e9);
      const s = p.map((v) => Math.round(v * v * 1e9) / 1e9), kp = p.join(","), ks = s.join(",");
      m.set(kp, { p, n: (m.get(kp)?.n || 0) + 1 }); q.set(ks, { p: s, n: (q.get(ks)?.n || 0) + 1 });
    }
    POINTS = [...m.values()]; SQUARES = [...q.values()];
    // the modes at θ = π/2 and 3π/2 on each axis (exact when 4 | d, nearest otherwise)
    const near = box.map((d) => [Math.round(d / 4) % d, Math.round(3 * d / 4) % d]);
    NEAR = [];
    for (const i of [0, 1]) for (const j of [0, 1]) for (const l of [0, 1]) NEAR.push([near[0][i], near[1][j], near[2][l]]);
  }
  // |⟨mode a | ψ⟩|² on one axis: the discrete Fourier weight of the axis state
  function weight(v, d, a) {
    let re = 0, im = 0;
    for (let j = 0; j < d; j++) { const th = -2 * Math.PI * a * j / d, c = Math.cos(th), s = Math.sin(th); re += v.re[j] * c - v.im[j] * s; im += v.re[j] * s + v.im[j] * c; }
    return (re * re + im * im) / d;
  }
  // ⟨T°²⟩ on one axis: ‖T° ψ‖²
  function t2(v) {
    const d = v.re.length; let s = 0;
    for (let j = 0; j < d; j++) { const a = (j + 1) % d, b = (j + d - 1) % d; s += ((v.re[a] + v.re[b]) / 2) ** 2 + ((v.im[a] + v.im[b]) / 2) ** 2; }
    return s;
  }
  const exact = (box) => box.every((d) => d % 4 === 0), even = (box) => box.every((d) => d % 2 === 0);
  const modeCos = () => { const { box, mode } = ST(); return mode.map((a, i) => cosOf(box[i], a)); };
  const psiCos = () => ST().lam;
  const psiSq = () => ST().V.map(t2);

  // ---------- top left: hopping ----------
  function drawHop() {
    const { box, tHop } = ST(), [g, w, h] = setup($("hhop")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22;
    cubeEdges(g, cx, cy, S);
    const hex = [[1, -1, 0], [1, 0, -1], [0, 1, -1], [-1, 1, 0], [-1, 0, 1], [0, -1, 1]].map((v) => proj(W(v), cx, cy, S));
    g.fillStyle = css("--violet"); g.globalAlpha = 0.14; g.beginPath(); hex.forEach((q, i) => (i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]))); g.closePath(); g.fill(); g.globalAlpha = 1;
    POINTS.map((q) => [q, proj(W(q.p), cx, cy, S)]).sort((a, b) => b[1][2] - a[1][2])
      .forEach(([q, P]) => dot(g, P, S * 0.014 * Math.sqrt(q.n), diverge(-2 * tHop * (q.p[0] + q.p[1] + q.p[2]) / (6 * Math.abs(tHop || 1)))));
    const O = proj(W([0, 0, 0]), cx, cy, S);
    dot(g, O, S * 0.05, exact(box) ? css("--ink") : "transparent", css("--violet"));
    ringAt(g, proj(W(modeCos()), cx, cy, S), 9, css("--orange"));
    dot(g, proj(W(psiCos()), cx, cy, S), S * 0.045, css("--ink"), css("--orange"), 2);
    text(g, `${box.join(" × ")} · ○ the mode · ● Ψ(s) at ⟨cos⟩ · plane: Σ cos = 0`, 10, 18, css("--ink2"));
    text(g, exact(box) ? "origin: 8 modes, the doublers" : "origin: no mode, 4 does not divide every size", 10, h - 10, css("--muted"));
  }
  // ---------- top right: Dirac ----------
  function drawDirac() {
    const { box } = ST(), [g, w, h] = setup($("hdir")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22, m = mEff();
    cubeEdges(g, cx, cy, S);
    const c0 = proj(W([0, 0, 0]), cx, cy, S);
    for (const r of [0.5, 1]) { g.strokeStyle = css("--green"); g.globalAlpha = 0.35; g.setLineDash([4, 4]); g.beginPath(); g.arc(c0[0], c0[1], r * S * c0[3], 0, 7); g.stroke(); g.setLineDash([]); g.globalAlpha = 1; }
    const eD = (p) => Math.sqrt(p[0] ** 2 + p[1] ** 2 + p[2] ** 2 + m * m);
    POINTS.map((q) => [q, proj(W(q.p), cx, cy, S)]).sort((a, b) => b[1][2] - a[1][2])
      .forEach(([q, P]) => dot(g, P, S * 0.014 * Math.sqrt(q.n), seq(eD(q.p) / Math.sqrt(3))));
    dot(g, c0, S * 0.05, exact(box) ? css("--ink") : "transparent", css("--green"));
    const mc = modeCos();
    ringAt(g, proj(W(mc), cx, cy, S), 9, css("--orange"));
    dot(g, proj(W(psiCos()), cx, cy, S), S * 0.045, css("--ink"), css("--orange"), 2);
    const gap = Math.sqrt(Math.min(...POINTS.map((q) => q.p[0] ** 2 + q.p[1] ** 2 + q.p[2] ** 2)) + m * m);
    text(g, `|E| of the mode ${eD(mc).toFixed(3)} · lowest |E| on this torus ${gap.toFixed(3)}`, 10, 18, css("--ink2"));
    if (!even(box)) text(g, "✕ an odd size: the staggered signs do not close, D² ≠ ΣT² + m²", 10, h - 28, css("--red"));
    text(g, "zero only at the origin, the 8 doublers (4 | every size, m = 0)", 10, h - 10, css("--muted"));
  }
  // ---------- bottom: the squares ----------
  function drawSum() {
    const { box } = ST(), [g, w, h] = setup($("hsum")), cx = w / 2, cy = h / 2 + 4, S = Math.min(w / 2.4, h) * 0.24, m = mEff();
    const sh = (v) => v.map((x) => 2 * x - 1);
    cubeEdges(g, cx, cy, S);
    const V = [];
    for (const a of [0, 1]) for (const b of [0, 1]) for (const c of [0, 1]) V.push([a, b, c]);
    const E12 = [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]];
    const sq = psiSq(), lev = sq[0] + sq[1] + sq[2];
    for (const r of [0.5, 1, 1.5, 2, 2.5, lev]) {
      const Ps = [];
      for (const [i, j] of E12) {
        const A = V[i], B = V[j], sA = A[0] + A[1] + A[2], sB = B[0] + B[1] + B[2];
        if (sA === sB || (sA - r) * (sB - r) > 0) continue;
        const t = (r - sA) / (sB - sA); Ps.push(proj(W(sh(A.map((v, k) => v + t * (B[k] - v)))), cx, cy, S));
      }
      if (Ps.length < 3) continue;
      const c0 = Ps.reduce((a, p) => [a[0] + p[0] / Ps.length, a[1] + p[1] / Ps.length], [0, 0]);
      Ps.sort((p, q) => Math.atan2(p[1] - c0[1], p[0] - c0[0]) - Math.atan2(q[1] - c0[1], q[0] - c0[0]));
      const mine = r === lev;
      g.fillStyle = css(mine ? "--orange" : "--green"); g.globalAlpha = mine ? 0.18 : 0.05 + 0.02 * r;
      g.beginPath(); Ps.forEach((p, k) => (k ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]))); g.closePath(); g.fill(); g.globalAlpha = 1;
    }
    SQUARES.map((q) => [q, proj(W(sh(q.p)), cx, cy, S)]).sort((a, b) => b[1][2] - a[1][2])
      .forEach(([q, P]) => dot(g, P, S * 0.007 * Math.sqrt(q.n), seq(Math.sqrt(q.p[0] + q.p[1] + q.p[2] + m * m) / Math.sqrt(3))));
    dot(g, proj(W([-1, -1, -1]), cx, cy, S), S * 0.05, exact(box) ? css("--ink") : "transparent", css("--green"));
    ringAt(g, proj(W(sh(modeCos().map((v) => v * v))), cx, cy, S), 9, css("--orange"));
    dot(g, proj(W(sh(sq)), cx, cy, S), S * 0.045, css("--ink"), css("--orange"), 2);
    text(g, `Ψ(s): ⟨D²⟩ = ⟨T_x²⟩ + ⟨T_y²⟩ + ⟨T_z²⟩ + m² = ${(lev + m * m).toFixed(3)} (orange plane) · every state, Lean dirac3_sq`, 10, h - 10, css("--muted"));
  }
  // ---------- minis: the 8 doubler modes of this torus ----------
  function lbl(c) { const { box } = ST(); return c.map((a, i) => (box[i] % 4 === 0 ? (a === box[i] / 4 ? "+" : "−") : "≈")).join(""); }
  function wOn(c) { const { box, V } = ST(); return c.reduce((p, a, i) => p * weight(V[i], box[i], a), 1); }
  function miniBalls(cv, c, f, colour, size) {
    const { box } = ST(), [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.2;
    const out = [];
    for (let i = -1; i <= 1; i++) for (let j = -1; j <= 1; j++) for (let k = -1; k <= 1; k++) {
      const p = [c[0] + i, c[1] + j, c[2] + k].map((a, n) => cosOf(box[n], a));
      out.push([[i, j, k], f(p)]);
    }
    out.map(([v, e]) => [v, e, proj(W(v), cx, cy, S)]).sort((a, b) => b[2][2] - a[2][2])
      .forEach(([v, e, P]) => dot(g, P, size(e) * S, colour(e), v.every((x) => x === 0) ? css("--ink") : null));
    text(g, `(${lbl(c)}) mode ${c.join(",")}`, 5, 13, css("--ink2"), 10);
    text(g, `Ψ ${(100 * wOn(c)).toFixed(1)}%`, 5, h - 6, css("--orange"), 10);
  }
  function miniSum(cv, c) {
    const { box, tHop } = ST(), [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.3, m = mEff(), n = 9;
    const cs = (ax, u) => Math.cos(2 * Math.PI * (c[ax] + u) / box[ax]);
    const sheets = [
      [(u, v) => -2 * tHop * (cs(0, u) + cs(1, v) + cs(2, 0)) * 0.35, css("--violet")],
      [(u, v) => Math.sqrt(cs(0, u) ** 2 + cs(1, v) ** 2 + cs(2, 0) ** 2 + m * m) * 0.9, css("--green")],
      [(u, v) => -Math.sqrt(cs(0, u) ** 2 + cs(1, v) ** 2 + cs(2, 0) ** 2 + m * m) * 0.9, css("--green")],
    ];
    for (const [f, col] of sheets) {
      g.strokeStyle = col; g.globalAlpha = 0.8; g.lineWidth = 1;
      for (let i = 0; i < n; i++) for (const along of [0, 1]) {
        g.beginPath();
        for (let k = 0; k <= 16; k++) {
          const u = -1.2 + 2.4 * i / (n - 1), v = -1.2 + 2.4 * k / 16, [a, b] = along ? [u, v] : [v, u];
          const P = proj(W([a * 0.7, b * 0.7, f(a, b)]), cx, cy, S);
          k ? g.lineTo(P[0], P[1]) : g.moveTo(P[0], P[1]);
        }
        g.stroke();
      }
    }
    g.globalAlpha = 1;
    text(g, `(${lbl(c)})`, 5, 13, css("--ink2"), 10.5);
    text(g, `Ψ ${(100 * wOn(c)).toFixed(1)}%`, 5, h - 6, css("--orange"), 10);
  }

  const minis = { nhop: [], ndir: [], nsum: [] };
  for (const id of Object.keys(minis)) for (let i = 0; i < 8; i++) {
    const cv = document.createElement("canvas"); cv.setAttribute("aria-label", `doubler ${i + 1}, local zoom`);
    $(id).appendChild(cv); minis[id].push(cv);
  }
  for (const c of [$("hhop"), $("hdir"), $("hsum"), ...Object.values(minis).flat()]) {
    let drag = null;
    c.addEventListener("pointerdown", (e) => { const s = ST(); if (!s) return; drag = [e.clientX, e.clientY, s.yaw, s.pitch]; c.setPointerCapture(e.pointerId); });
    c.addEventListener("pointermove", (e) => {
      if (!drag) return;
      window.NRS3Rotate(drag[2] + (e.clientX - drag[0]) * 0.01, Math.max(-1.45, Math.min(1.45, drag[3] + (e.clientY - drag[1]) * 0.01)));
    });
    c.addEventListener("pointerup", () => { drag = null; });
  }
  $("hmass").addEventListener("input", (e) => { mass = +e.target.value; $("vhmass").textContent = mass.toFixed(2); });
  $("hfiber").addEventListener("click", (e) => {
    fiber = !fiber; e.target.setAttribute("aria-pressed", String(fiber));
    $("hmass").disabled = fiber; $("vhmass").textContent = fiber ? "½ (fibre)" : mass.toFixed(2);
  });
  const visible = (el) => { const r = el.getBoundingClientRect(); return r.bottom > 0 && r.top < innerHeight; };
  function frame() {
    if (ST() && visible($("hdblcard"))) {
      refresh(ST().box);
      drawHop(); drawDirac(); drawSum();
      const m = mEff(), tH = ST().tHop;
      minis.nhop.forEach((cv, i) => miniBalls(cv, NEAR[i], (p) => -2 * tH * (p[0] + p[1] + p[2]), (e) => diverge(e / (6 * Math.abs(tH || 1))), () => 0.07));
      minis.ndir.forEach((cv, i) => miniBalls(cv, NEAR[i], (p) => Math.sqrt(p[0] ** 2 + p[1] ** 2 + p[2] ** 2 + m * m), (e) => seq(e / Math.sqrt(3)), (e) => 0.02 + 0.07 * e));
      minis.nsum.forEach((cv, i) => miniSum(cv, NEAR[i]));
    }
    requestAnimationFrame(frame);
  }
  if (location.hash === "#fibre") $("hfiber").click();
  requestAnimationFrame(frame);
})();

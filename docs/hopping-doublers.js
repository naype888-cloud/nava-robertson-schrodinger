// The eight doublers on the hopping page: the spectral side of the corners of T³.
// Every mode (a, b, c) of the torus sits at (cos θa, cos θb, cos θc) in the cosine cube.
// Hopping: E = −2t (cos θa + cos θb + cos θc); its zero is the whole plane Σ cos = 0 (the Fermi surface).
// Dirac (Kogut–Susskind signs): E = ±√(cos²θa + cos²θb + cos²θc + m²); its zero is one point, the
// origin, where the 8 doublers (±π/2)³ sit. Sum: in the squares (cos², cos², cos²) the Dirac energy
// squared is the sum of the three axes plus m², D² = T_x² + T_y² + T_z² + m² (TorusDirac3.dirac3_sq).
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const L = 8, TH = Array.from({ length: L }, (_, k) => 2 * Math.PI * k / L);
  const DOUBLERS = [];
  for (const a of [2, 6]) for (const b of [2, 6]) for (const c of [2, 6]) DOUBLERS.push([a, b, c]);
  let yaw = -0.7, pitch = 0.4, lastInteract = 0, mass = 0, fiber = false;

  function rot([x, y, z]) {
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
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
  // −1 … 1 → blue … orange through the panel colour (hopping); 0 … 1 → green … muted (Dirac)
  const diverge = (u) => `hsl(${u < 0 ? 214 : 18}, ${dark() ? 70 : 75}%, ${dark() ? 62 - 30 * (1 - Math.abs(u)) : 45 + 25 * (1 - Math.abs(u))}%)`;
  const seq = (u) => `hsl(${150 - 120 * Math.min(1, u)}, ${dark() ? 60 : 65}%, ${dark() ? 60 : 42}%)`;
  const mEff = () => (fiber ? 0.5 : mass);
  function cubeEdges(g, cx, cy, S, lo, hi, dash) {
    const C = [];
    for (const a of [lo, hi]) for (const b of [lo, hi]) for (const c of [lo, hi]) C.push([a, b, c]);
    g.strokeStyle = css("--grid"); g.lineWidth = 1; if (dash) g.setLineDash(dash);
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(([i, j]) => {
      const p = proj(W(C[i]), cx, cy, S), q = proj(W(C[j]), cx, cy, S);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    });
    g.setLineDash([]);
  }
  const dot = (g, P, r, fill, ring) => {
    g.fillStyle = fill; g.beginPath(); g.arc(P[0], P[1], Math.max(1, r * P[3]), 0, 7); g.fill();
    if (ring) { g.strokeStyle = ring; g.lineWidth = 1.5; g.stroke(); }
  };
  const text = (g, s, x, y, col, size = 12) => { g.font = `${size}px system-ui, sans-serif`; g.fillStyle = col; g.fillText(s, x, y); };
  // the distinct cosine points of the modes, with how many modes sit on each
  const POINTS = (() => {
    const m = new Map();
    for (const a of TH) for (const b of TH) for (const c of TH) {
      const p = [Math.cos(a), Math.cos(b), Math.cos(c)].map((v) => Math.round(v * 1e9) / 1e9), k = p.join(",");
      m.set(k, { p, n: (m.get(k)?.n || 0) + 1 });
    }
    return [...m.values()];
  })();
  const eH = (p) => -2 * (p[0] + p[1] + p[2]);
  const eD = (p) => Math.sqrt(p[0] ** 2 + p[1] ** 2 + p[2] ** 2 + mEff() ** 2);

  // ---------- top left: hopping, the plane Σ cos = 0 ----------
  function drawHop() {
    const [g, w, h] = setup($("hhop")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22;
    cubeEdges(g, cx, cy, S, -1, 1);
    // the zero plane inside the cube: a regular hexagon
    const hex = [[1, -1, 0], [1, 0, -1], [0, 1, -1], [-1, 1, 0], [-1, 0, 1], [0, -1, 1]].map((v) => proj(W(v), cx, cy, S));
    g.fillStyle = css("--violet"); g.globalAlpha = 0.14; g.beginPath(); hex.forEach((q, i) => (i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]))); g.closePath(); g.fill(); g.globalAlpha = 1;
    POINTS.map((q) => [q, proj(W(q.p), cx, cy, S)]).sort((a, b) => b[1][2] - a[1][2]).forEach(([q, P]) => {
      const origin = q.p.every((v) => Math.abs(v) < 1e-9);
      dot(g, P, origin ? S * 0.07 : S * 0.022 * Math.sqrt(q.n), origin ? css("--ink") : diverge(eH(q.p) / 6), origin ? css("--violet") : null);
    });
    text(g, "the zero of the hopping: the plane Σ cos = 0 (a whole Fermi surface)", 10, h - 10, css("--muted"));
    text(g, `${L} × ${L} × ${L} torus · colour E = −2t Σ cos · ● the origin: 8 modes`, 10, 18, css("--ink2"));
  }
  // ---------- top right: Dirac, one zero point ----------
  function drawDirac() {
    const [g, w, h] = setup($("hdir")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22, m = mEff();
    cubeEdges(g, cx, cy, S, -1, 1);
    for (const r of [0.5, 1]) {                      // two level spheres |E|² − m² = r²
      const c0 = proj(W([0, 0, 0]), cx, cy, S);
      g.strokeStyle = css("--green"); g.globalAlpha = 0.35; g.setLineDash([4, 4]);
      g.beginPath(); g.arc(c0[0], c0[1], r * S * c0[3], 0, 7); g.stroke(); g.setLineDash([]); g.globalAlpha = 1;
    }
    POINTS.map((q) => [q, proj(W(q.p), cx, cy, S)]).sort((a, b) => b[1][2] - a[1][2]).forEach(([q, P]) => {
      const origin = q.p.every((v) => Math.abs(v) < 1e-9);
      dot(g, P, origin ? S * 0.07 : S * 0.022 * Math.sqrt(q.n), origin ? css("--ink") : seq(eD(q.p) / Math.sqrt(3)), origin ? css("--green") : null);
    });
    text(g, `the zero of Dirac: one point, the 8 doublers · gap |E| ≥ ${m.toFixed(2)}`, 10, h - 10, css("--muted"));
    text(g, "colour |E| = √(Σ cos² + m²) · dashed: level spheres", 10, 18, css("--ink2"));
  }
  // ---------- bottom: the squares, E² − m² = cos² + cos² + cos² ----------
  function drawSum() {
    const [g, w, h] = setup($("hsum")), cx = w / 2, cy = h / 2 + 4, S = Math.min(w / 2.4, h) * 0.24;
    const sh = (v) => v.map((x) => 2 * x - 1);      // [0, 1]³ drawn as [−1, 1]³
    cubeEdges(g, cx, cy, S, -1, 1);
    const V = [];
    for (const a of [0, 1]) for (const b of [0, 1]) for (const c of [0, 1]) V.push([a, b, c]);
    const E12 = [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]];
    for (const r of [0.5, 1, 1.5, 2, 2.5]) {         // level polygons x + y + z = r inside the cube
      const Ps = [];
      for (const [i, j] of E12) {
        const A = V[i], B = V[j], sA = A[0] + A[1] + A[2], sB = B[0] + B[1] + B[2];
        if (sA === sB || (sA - r) * (sB - r) > 0) continue;
        const t = (r - sA) / (sB - sA);
        Ps.push(proj(W(sh(A.map((v, m) => v + t * (B[m] - v)))), cx, cy, S));
      }
      if (Ps.length < 3) continue;
      const c0 = Ps.reduce((a, p) => [a[0] + p[0] / Ps.length, a[1] + p[1] / Ps.length], [0, 0]);
      Ps.sort((p, q) => Math.atan2(p[1] - c0[1], p[0] - c0[0]) - Math.atan2(q[1] - c0[1], q[0] - c0[0]));
      g.fillStyle = css("--green"); g.globalAlpha = 0.05 + 0.02 * r;
      g.beginPath(); Ps.forEach((p, k) => (k ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]))); g.closePath(); g.fill(); g.globalAlpha = 1;
    }
    const sq = new Map();
    for (const q of POINTS) { const p = q.p.map((v) => Math.round(v * v * 1e9) / 1e9), k = p.join(","); sq.set(k, { p, n: (sq.get(k)?.n || 0) + q.n }); }
    [...sq.values()].map((q) => [q, proj(W(sh(q.p)), cx, cy, S)]).sort((a, b) => b[1][2] - a[1][2]).forEach(([q, P]) => {
      const origin = q.p.every((v) => v < 1e-9);
      dot(g, P, origin ? S * 0.06 : S * 0.007 * Math.sqrt(q.n), origin ? css("--ink") : seq(Math.sqrt(q.p[0] + q.p[1] + q.p[2] + mEff() ** 2) / Math.sqrt(3)), origin ? css("--green") : null);
    });
    text(g, "squares (cos², cos², cos²): E² − m² is the sum of the three axes, D² = T_x² + T_y² + T_z² + m²", 10, h - 10, css("--muted"));
  }
  // ---------- minis: each doubler in its neighbourhood of modes ----------
  function around(c, f) {   // the 3 × 3 × 3 modes around a doubler, slice drawn as balls
    const out = [];
    for (let i = -1; i <= 1; i++) for (let j = -1; j <= 1; j++) for (let k = -1; k <= 1; k++) {
      const th = [c[0] + i, c[1] + j, c[2] + k].map((n) => 2 * Math.PI * n / L);
      out.push([[i, j, k], f(th.map(Math.cos))]);
    }
    return out;
  }
  const sgn = (c) => c.map((n) => (n === 2 ? "+" : "−")).join("");
  function miniBalls(cv, c, f, colour, size) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.2;
    around(c, f).map(([v, e]) => [v, e, proj(W(v), cx, cy, S)]).sort((a, b) => b[2][2] - a[2][2])
      .forEach(([v, e, P]) => dot(g, P, size(e) * S, colour(e), v.every((x) => x === 0) ? css("--ink") : null));
    text(g, `(${sgn(c)})π/2`, 5, 13, css("--ink2"), 10.5);
  }
  function miniSum(cv, c) {   // slice δc = 0: hopping plane and Dirac cone over (δa, δb)
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.3, m = mEff(), n = 9;
    const sl = 2 * Math.PI / L;
    const sheets = [
      [(u, v) => -2 * (Math.cos((c[0] + u) * sl) + Math.cos((c[1] + v) * sl) + Math.cos(c[2] * sl)) * 0.35, css("--violet")],
      [(u, v) => Math.sqrt(Math.cos((c[0] + u) * sl) ** 2 + Math.cos((c[1] + v) * sl) ** 2 + m * m) * 0.9, css("--green")],
      [(u, v) => -Math.sqrt(Math.cos((c[0] + u) * sl) ** 2 + Math.cos((c[1] + v) * sl) ** 2 + m * m) * 0.9, css("--green")],
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
    text(g, `(${sgn(c)})π/2`, 5, 13, css("--ink2"), 10.5);
    text(g, "plane + cone", 5, h - 6, css("--muted"), 10.5);
  }

  const minis = { nhop: [], ndir: [], nsum: [] };
  for (const id of Object.keys(minis)) DOUBLERS.forEach((c, i) => {
    const cv = document.createElement("canvas"); cv.setAttribute("aria-label", `doubler ${i + 1}, local zoom`);
    $(id).appendChild(cv); minis[id].push([cv, c]);
  });
  for (const c of [$("hhop"), $("hdir"), $("hsum"), ...Object.values(minis).flat().map(([cv]) => cv)]) {
    let drag = null;
    c.addEventListener("pointerdown", (e) => { drag = [e.clientX, e.clientY, yaw, pitch]; c.setPointerCapture(e.pointerId); lastInteract = performance.now(); });
    c.addEventListener("pointermove", (e) => {
      if (!drag) return;
      yaw = drag[2] + (e.clientX - drag[0]) * 0.01;
      pitch = Math.max(-1.45, Math.min(1.45, drag[3] + (e.clientY - drag[1]) * 0.01));
      lastInteract = performance.now();
    });
    c.addEventListener("pointerup", () => { drag = null; });
  }
  $("hmass").addEventListener("input", (e) => { mass = +e.target.value; $("vhmass").textContent = mass.toFixed(2); });
  $("hfiber").addEventListener("click", (e) => {
    fiber = !fiber; e.target.setAttribute("aria-pressed", String(fiber));
    $("hmass").disabled = fiber; $("vhmass").textContent = fiber ? "½ (fibre)" : mass.toFixed(2);
  });
  const visible = (el) => { const r = el.getBoundingClientRect(); return r.bottom > 0 && r.top < innerHeight; };
  let last = 0;
  function frame(ts) {
    const dt = last ? Math.min(0.05, (ts - last) / 1000) : 0; last = ts;
    if (ts - lastInteract > 2500) yaw += dt * 0.25;
    if (visible($("hdblcard"))) {
      drawHop(); drawDirac(); drawSum();
      minis.nhop.forEach(([cv, c]) => miniBalls(cv, c, (p) => eH(p), (e) => diverge(e / 6), (e) => 0.07));
      minis.ndir.forEach(([cv, c]) => miniBalls(cv, c, (p) => eD(p), (e) => seq(e / Math.sqrt(3)), (e) => 0.02 + 0.07 * e));
      minis.nsum.forEach(([cv, c]) => miniSum(cv, c));
    }
    requestAnimationFrame(frame);
  }
  if (location.hash === "#fibre") $("hfiber").click();
  requestAnimationFrame(frame);
})();

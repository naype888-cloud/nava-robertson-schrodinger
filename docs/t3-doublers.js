// The eight corners of T³: position, momentum and their sum.
// Position: the corners {0, d−1}³ of the drawn box are neighbours through the three seams, so on the
// torus they are one 2×2×2 cube; the colour is the staggered sign ε = (−1)^(x+y+z) (Dirac's β).
// Momentum: the transport T_x + T_y + T_z with the Kogut–Susskind signs vanishes at the 8 corners
// (±π/2)³ of the Brillouin cube, the doublers; each carries an index ±1 and the indices add to 0.
// Sum: the phase θ·x of each doubler on the 2×2×2 corner cube, with the closed fibre w as a fourth
// axis (D₄ = D₃ + ε T_w, Kaluza–Klein masses cos(2πk/3) = 1, −½, −½).
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const L = 4;                                     // even sizes: the staggered sign closes on the ring
  const CORNERS = [];
  for (const a of [0, 1]) for (const b of [0, 1]) for (const c of [0, 1]) CORNERS.push([a, b, c]);
  let yaw = -0.7, pitch = 0.4, lastInteract = 0, mass = 0, fiber = false, time = 0, phi4 = 0;

  // ---------- projection (as in t3-box.js), plus a turn in the x–w plane for the fibre ----------
  function rot([x, y, z]) {
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x1 = cy * x + sy * z, z1 = -sy * x + cy * z;
    return [x1, cp * y - sp * z1, sp * y + cp * z1];
  }
  const proj = (v, cx, cy, S) => { const [x, y, z] = rot(v), f = 3.6 / (3.6 + z); return [cx + x * S * f, cy - y * S * f, z, f]; };
  const W = ([x, y, z]) => [x, z, y];            // lattice z is vertical on screen
  function four([x, y, z, w]) {                    // turn x–w, then look along w
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
  const hue = (ph) => `hsl(${((ph * 180 / Math.PI) % 360 + 360) % 360}, ${dark() ? 70 : 80}%, ${dark() ? 62 : 45}%)`;
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
  const ball = (g, P, r, fill, ring) => {
    g.fillStyle = fill; g.beginPath(); g.arc(P[0], P[1], Math.max(1.2, r * P[3]), 0, 2 * Math.PI); g.fill();
    if (ring) { g.strokeStyle = ring; g.lineWidth = 1.5; g.stroke(); }
  };
  const label = (g, txt, x, y, col, size = 12) => { g.font = `${size}px system-ui, sans-serif`; g.fillStyle = col; g.fillText(txt, x, y); };
  // a legend: coloured dot, text, next item
  function legend(g, items, tail) {
    let x = 10; g.font = "12px system-ui, sans-serif";
    for (const [col, txt] of items) {
      g.fillStyle = col; g.beginPath(); g.arc(x + 4, 14, 4, 0, 7); g.fill();
      g.fillStyle = css("--ink2"); g.fillText(txt, x + 12, 18); x += 12 + g.measureText(txt).width + 14;
    }
    if (tail) { g.fillStyle = css("--ink2"); g.fillText(tail, x, 18); }
  }

  // ---------- the physics, read off the lattice ----------
  const eps = ([x, y, z]) => ((x + y + z) % 2 ? -1 : 1);                 // staggered sign, Dirac's β
  const eta = ([x, y]) => [1, x % 2 ? -1 : 1, (x + y) % 2 ? -1 : 1];      // Kogut–Susskind signs of the three links
  const sideOf = (c) => c.map((v) => (v ? 1 : -1));                       // corner of the Brillouin cube: θ = s·π/2
  const index = (s) => -s[0] * s[1] * s[2];                               // sign of det ∂(cos θ)/∂θ at the doubler
  const kk = [1, -0.5, -0.5];                                             // spectrum of T_w on the ring of 3
  const effMass = () => (fiber ? Math.abs(kk[1]) : mass);                 // the light Kaluza–Klein level is ½

  // ---------- top left: position ----------
  function drawPos() {
    const [g, w, h] = setup($("dpos")), cx = w / 2, cy = h / 2 + 14, S = Math.min(w, h) * 0.22;
    const s = 2 / (L - 1), hh = 1, at = (j) => j * s - 1;
    cube(g, cx, cy, S, hh, css("--grid"));
    const pts = [];
    for (let i = 0; i < L; i++) for (let j = 0; j < L; j++) for (let k = 0; k < L; k++) {
      const corner = [i, j, k].every((v) => v === 0 || v === L - 1);
      pts.push([proj(W([at(i), at(j), at(k)]), cx, cy, S), corner, eps([i, j, k])]);
    }
    pts.sort((a, b) => b[0][2] - a[0][2]);
    for (const [P, corner, e] of pts) {
      if (!corner) { g.fillStyle = css("--grid"); g.fillRect(P[0] - 1.2, P[1] - 1.2, 2.4, 2.4); continue; }
      ball(g, P, S * 0.07, sgnCol(e), css("--ink"));
    }
    label(g, `${L} × ${L} × ${L} torus · the 8 corners are one 2×2×2 cube through the seams`, 10, h - 10, css("--muted"));
    legend(g, [[sgnCol(1), "ε = +1"], [sgnCol(-1), "ε = −1"]]);
  }
  // a corner and its six links: three inside the box, three through the seams to other corners
  function drawPosMini(cv, c) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 4, S = Math.min(w, h) * 0.36;
    const site = c.map((v) => v * (L - 1)), et = eta(site);
    for (let mu = 0; mu < 3; mu++) for (const dir of [1, -1]) {
      const e = [0, 0, 0]; e[mu] = dir;
      const nb = site.map((v, m) => (v + e[m] + L) % L), seam = Math.abs(nb[mu] - site[mu]) > 1;
      const P0 = proj(W([0, 0, 0]), cx, cy, S), P1 = proj(W(e.map((v) => v * 0.85)), cx, cy, S);
      g.strokeStyle = seam ? css("--violet") : css("--ink2"); g.lineWidth = seam ? 2.4 : 1.4;
      if (et[mu] < 0) g.setLineDash([4, 3]);
      g.beginPath(); g.moveTo(P0[0], P0[1]); g.lineTo(P1[0], P1[1]); g.stroke(); g.setLineDash([]);
      ball(g, P1, S * 0.1, seam ? sgnCol(eps(nb)) : css("--grid"));
    }
    ball(g, proj(W([0, 0, 0]), cx, cy, S), S * 0.16, sgnCol(eps(site)), css("--ink"));
    label(g, `(${site.join(",")})`, 5, 13, css("--ink2"), 10.5);
  }

  // ---------- top right: momentum ----------
  function drawMom() {
    const [g, w, h] = setup($("dmom")), cx = w / 2, cy = h / 2 + 6, S = Math.min(w, h) * 0.26;
    const N = 8, m = effMass();
    cube(g, cx, cy, S, 1, css("--grid"));
    cube(g, cx, cy, S, 0.5, css("--grid"), [3, 3]);
    const pts = [];
    for (let a = 0; a < N; a++) for (let b = 0; b < N; b++) for (let c = 0; c < N; c++) {
      const th = [a, b, c].map((k) => -Math.PI + 2 * Math.PI * k / N);
      const E = Math.sqrt(th.reduce((s, v) => s + Math.cos(v) ** 2, 0) + m * m);
      pts.push([proj(W(th.map((v) => v / Math.PI)), cx, cy, S), E, th]);
    }
    pts.sort((p, q) => p[0][2] - q[0][2]).reverse();
    for (const [P, E, th] of pts) {
      const isD = th.every((v) => Math.abs(Math.abs(v) - Math.PI / 2) < 1e-9);
      if (isD) { ball(g, P, S * 0.075, sgnCol(index(th.map(Math.sign))), css("--ink")); continue; }
      g.fillStyle = css("--muted"); g.globalAlpha = 0.25 + 0.5 * Math.exp(-2 * E);
      g.beginPath(); g.arc(P[0], P[1], Math.max(1, 2.6 * Math.exp(-E) * P[3]), 0, 7); g.fill(); g.globalAlpha = 1;
    }
    label(g, "Brillouin cube (−π, π]³ · dashed: (±π/2)³", 10, h - 10, css("--muted"));
    legend(g, [[sgnCol(1), "index +1"], [sgnCol(-1), "index −1"]], `· sum of the 8 = 0 · gap ${m.toFixed(2)}`);
  }
  // the Dirac cone at a doubler: E = ±√(q_x² + q_y² + m²) over the slice q_z = 0
  function drawMomMini(cv, c) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 6, S = Math.min(w, h) * 0.34, m = effMass();
    const s = sideOf(c), ix = index(s), n = 9, R = 1;
    const col = sgnCol(ix);
    for (const sheet of [1, -1]) {
      g.strokeStyle = col; g.globalAlpha = sheet > 0 ? 0.9 : 0.45; g.lineWidth = 1;
      for (let a = 0; a < n; a++) for (const along of [0, 1]) {
        g.beginPath();
        for (let b = 0; b <= 24; b++) {
          const u = -R + 2 * R * a / (n - 1), v = -R + 2 * R * b / 24;
          const [qx, qy] = along ? [u, v] : [v, u];
          const E = sheet * Math.sqrt(qx * qx + qy * qy + m * m);
          const P = proj(W([qx * 0.8, qy * 0.8, E * 0.55]), cx, cy, S);
          b ? g.lineTo(P[0], P[1]) : g.moveTo(P[0], P[1]);
        }
        g.stroke();
      }
    }
    g.globalAlpha = 1;
    const sg = s.map((v) => (v > 0 ? "+" : "−")).join("");
    label(g, `${sg} π/2`, 5, 13, css("--ink2"), 10.5);
    label(g, `index ${ix > 0 ? "+1" : "−1"}`, 5, h - 6, col, 10.5);
  }

  // ---------- bottom: position + momentum, the phase θ·x on the corner cube (3D or 4D) ----------
  function blockPoints(s, t) {
    const m = effMass(), out = [];
    const ws = fiber ? [0, 1, 2] : [0];
    for (const w of ws) for (const x of CORNERS) {
      const k = fiber ? 1 : 0;                                   // the light fibre mode, k = 1 (k = 2 turns the other way)
      const ph = Math.PI / 2 * (s[0] * x[0] + s[1] * x[1] + s[2] * x[2]) + 2 * Math.PI * k * w / 3 - m * t;
      const p = x.map((v) => v - 0.5), pw = fiber ? (w - 1) * 0.55 : 0;
      out.push({ v: fiber ? four([p[0], p[1], p[2], pw]) : p, ph, e: eps(x), w, x });
    }
    return out;
  }
  function drawBlock(g, cx, cy, S, s, t, r, off = [0, 0, 0], k = 1) {
    const P = blockPoints(s, t), pr = P.map((q) => proj(W(q.v.map((v, m) => off[m] + v * k)), cx, cy, S));
    g.strokeStyle = css("--grid"); g.lineWidth = 1;
    for (let i = 0; i < P.length; i++) for (let j = i + 1; j < P.length; j++) {
      const a = P[i], b = P[j];
      const dx = a.x.reduce((n, v, m) => n + Math.abs(v - b.x[m]), 0);
      const link = (a.w === b.w && dx === 1) || (dx === 0 && Math.abs(a.w - b.w) === 1);
      if (!link) continue;
      g.beginPath(); g.moveTo(pr[i][0], pr[i][1]); g.lineTo(pr[j][0], pr[j][1]); g.stroke();
    }
    P.map((q, i) => [q, pr[i]]).sort((a, b) => b[1][2] - a[1][2]).forEach(([q, p]) => ball(g, p, r, hue(q.ph), sgnCol(q.e)));
  }
  function drawSum() {
    const [g, w, h] = setup($("dsum")), cx = w / 2, cy = h / 2 + 4, S = Math.min(w / 2.4, h) * 0.19;
    cube(g, cx, cy, S, 1, css("--grid"), [3, 3]);
    CORNERS.map((c) => { const s = sideOf(c); return [proj(W(s), cx, cy, S), s]; })
      .sort((a, b) => b[0][2] - a[0][2])
      .forEach(([, s]) => drawBlock(g, cx, cy, S, s, time, S * 0.045, s, 0.5));
    label(g, fiber ? "T³ × w: every doubler on the 2×2×2×3 block, phase θ·x + 2πw/3 − (½)t"
      : "momentum corner (outer cube) + position corner (inner block): colour = phase θ·x − m t", 10, h - 10, css("--muted"));
  }
  function drawSumMini(cv, c) {
    const [g, w, h] = setup(cv), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.42, s = sideOf(c);
    drawBlock(g, cx, cy, S, s, time, S * 0.09);
    label(g, `θ = (${s.map((v) => (v > 0 ? "+" : "−")).join("")})π/2`, 5, 13, css("--ink2"), 10.5);
    if (fiber) label(g, "4D: x–w turn", 5, h - 6, css("--muted"), 10.5);
  }

  // ---------- minis, controls, loop ----------
  const minis = { mpos: [], mmom: [], msum: [] };
  for (const id of Object.keys(minis)) {
    const box = $(id);
    CORNERS.forEach((c, i) => {
      const cv = document.createElement("canvas");
      cv.setAttribute("aria-label", `local zoom on corner ${i + 1}`);
      box.appendChild(cv); minis[id].push([cv, c]);
    });
  }
  const all = [$("dpos"), $("dmom"), $("dsum"), ...Object.values(minis).flat().map(([cv]) => cv)];
  for (const c of all) {
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
  $("dmass").addEventListener("input", (e) => { mass = +e.target.value; $("vmass").textContent = mass.toFixed(2); });
  $("dfiber").addEventListener("click", (e) => {
    fiber = !fiber; e.target.setAttribute("aria-pressed", String(fiber));
    $("dmass").disabled = fiber;
    $("vmass").textContent = fiber ? "½ (fibre)" : mass.toFixed(2);
  });
  const visible = (el) => { const r = el.getBoundingClientRect(); return r.bottom > 0 && r.top < innerHeight; };
  let last = 0;
  function frame(ts) {
    const dt = last ? Math.min(0.05, (ts - last) / 1000) : 0; last = ts;
    if (ts - lastInteract > 2500) yaw += dt * 0.25;
    time += dt * 2; phi4 += dt * 0.5;
    if (visible($("dblcard"))) {
      drawPos(); drawMom(); drawSum();
      minis.mpos.forEach(([cv, c]) => drawPosMini(cv, c));
      minis.mmom.forEach(([cv, c]) => drawMomMini(cv, c));
      minis.msum.forEach(([cv, c]) => drawSumMini(cv, c));
    }
    requestAnimationFrame(frame);
  }
  if (location.hash === "#fibre") $("dfiber").click();   // a link straight to the 4D view
  requestAnimationFrame(frame);
})();

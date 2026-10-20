// NRS³ on T³: three closed axes. Every number here is computed in the browser from the same
// matrices as in Lean (nrs3-hopf ClosedThree, nrs3-tritoro Torus*):
//   T° = (J − I)/2, P₃ = diag(−1, 0, 1), maxState = (1/2 − i/√6, −i/√6, −1/2 − i/√6).
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const deg = (r) => r * 180 / Math.PI;
  const R6 = Math.sqrt(6), R2 = Math.sqrt(2);

  // ---------- one closed axis ----------
  // complex numbers as [re, im]
  const STATES = {
    c: [[0.5, -1 / R6], [0, -1 / R6], [-0.5, -1 / R6]],                      // ClosedThree.maxState
    sat: [[R2 / 4, R2 / 4], [R2 / 2, 0], [R2 / 4, -R2 / 4]],                 // ClosedThreeBand.satState
  };
  const P = [-1, 0, 1];
  // e^{−itT°}: T° has the eigenvalue 1 on u = (1,1,1)/√3 and −1/2 on its complement
  function evolve(psi, t) {
    const s = [psi[0][0] + psi[1][0] + psi[2][0], psi[0][1] + psi[1][1] + psi[2][1]];
    const a = [s[0] / 3, s[1] / 3];                                 // (u·ψ) u, every entry
    const e1 = [Math.cos(t), -Math.sin(t)], e2 = [Math.cos(t / 2), Math.sin(t / 2)];
    const mul = (z, w) => [z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]];
    return psi.map((z) => {
      const rest = [z[0] - a[0], z[1] - a[1]], p = mul(e1, a), q = mul(e2, rest);
      return [p[0] + q[0], p[1] + q[1]];
    });
  }
  function stats(psi) {
    const s = [psi[0][0] + psi[1][0] + psi[2][0], psi[0][1] + psi[1][1] + psi[2][1]];
    const T = psi.map((z) => [(s[0] - z[0]) / 2, (s[1] - z[1]) / 2]);
    let mT = 0, mP = 0;
    for (let j = 0; j < 3; j++) {
      mT += psi[j][0] * T[j][0] + psi[j][1] * T[j][1];
      mP += P[j] * (psi[j][0] ** 2 + psi[j][1] ** 2);
    }
    let sT = 0, sP = 0, zr = 0, zi = 0;
    const dT = [], dP = [];
    for (let j = 0; j < 3; j++) {
      const x = [T[j][0] - mT * psi[j][0], T[j][1] - mT * psi[j][1]];
      const y = [(P[j] - mP) * psi[j][0], (P[j] - mP) * psi[j][1]];
      dT.push(x); dP.push(y);
      sT += x[0] ** 2 + x[1] ** 2; sP += y[0] ** 2 + y[1] ** 2;
      zr += x[0] * y[0] + x[1] * y[1]; zi += x[0] * y[1] - x[1] * y[0];   // ⟨δT, δP⟩
    }
    const light = sT * sP > 1e-15 ? (zr * zr + zi * zi) / (sT * sP) : 1;
    return {
      sT2: sT, sP2: sP, cov: zr, im: zi, tension: -2 * zi, light, dark: 1 - light,
      theta: Math.acos(Math.min(1, Math.sqrt(light))),
      ratio: zi * zi > 1e-15 ? (sT * sP - zr * zr) / (zi * zi) : Infinity,  // det Σ / |det Ω| of the axis
    };
  }
  function randomBandState() {
    for (;;) {
      const v = [0, 1, 2].map(() => [Math.random() * 2 - 1, Math.random() * 2 - 1]);
      const n = Math.hypot(...v.flat());
      const w = v.map((z) => [z[0] / n, z[1] / n]);
      if (Math.abs(stats(w).tension) > 1.02) return w;
    }
  }

  // ---------- state ----------
  let kind = "c", base = [STATES.c, STATES.c, STATES.c], t = 0, playing = true;
  let yaw = -0.7, pitch = 0.45, lastInteract = 0;
  const ZOOM = { torus: 1, star: 1 };
  const current = () => base.map((psi) => evolve(psi, t));

  // ---------- 3D ----------
  function rot([x, y, z]) {
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x1 = cy * x + sy * z, z1 = -sy * x + cy * z;
    return [x1, cp * y - sp * z1, sp * y + cp * z1];
  }
  function proj(v, cx, cy, S) {
    const [x, y, z] = rot(v), f = 3.6 / (3.6 + z);
    return [cx + x * S * f, cy - y * S * f, z, f];
  }
  const W = ([x, y, z]) => [x, z, y];   // lattice z is vertical on screen
  function setup(c) {
    const r = c.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, r.width, r.height);
    return [g, r.width, r.height];
  }

  // ---------- the torus T³ = 3 × 3 × 3 ----------
  function drawTorus(V) {
    const [g, w, h] = setup($("torus")), cx = w / 2, cy = h / 2 + 4, S = Math.min(w, h) * 0.24 * ZOOM.torus;
    const L = (p) => proj(W(p), cx, cy, S);
    // links: two steps per line and the seam {0, 2} that closes it
    g.lineWidth = 1;
    for (let a = 0; a < 3; a++) {
      for (const u of [-1, 0, 1]) for (const v of [-1, 0, 1]) {
        const at = (s) => { const p = [0, 0, 0]; p[a] = s; p[(a + 1) % 3] = u; p[(a + 2) % 3] = v; return p; };
        g.strokeStyle = css("--grid"); g.setLineDash([]);
        const p0 = L(at(-1)), p2 = L(at(1));
        g.beginPath(); g.moveTo(p0[0], p0[1]); g.lineTo(p2[0], p2[1]); g.stroke();
        // the seam: a loop around the outside, from +1 back to −1
        const out = [0, 0, 0]; out[(a + 2) % 3] = v >= 0 ? 1 : -1;
        const c1 = at(1.9).map((q, i) => q + 0.55 * out[i]), c2 = at(-1.9).map((q, i) => q + 0.55 * out[i]);
        const q1 = L(c1), q2 = L(c2);
        g.strokeStyle = css("--violet"); g.globalAlpha = 0.35; g.setLineDash([3, 3]);
        g.beginPath(); g.moveTo(p2[0], p2[1]); g.bezierCurveTo(q1[0], q1[1], q2[0], q2[1], p0[0], p0[1]); g.stroke();
        g.globalAlpha = 1; g.setLineDash([]);
      }
    }
    // Ψ on every site
    const prob = V.map((psi) => psi.map((z) => z[0] ** 2 + z[1] ** 2));
    const phase = V.map((psi) => psi.map((z) => Math.atan2(z[1], z[0])));
    const pmax = prob.map((p) => Math.max(...p)).reduce((a, b) => a * b, 1);
    const dark = document.documentElement.dataset.theme === "dark";
    const pts = [];
    for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) for (let k = 0; k < 3; k++) {
      pts.push([L([i - 1, j - 1, k - 1]), prob[0][i] * prob[1][j] * prob[2][k] / pmax, phase[0][i] + phase[1][j] + phase[2][k]]);
    }
    pts.sort((a, b) => b[0][2] - a[0][2]);
    for (const [p, pr, ph] of pts) {
      const hue = ((deg(ph) % 360) + 360) % 360;
      g.fillStyle = `hsla(${hue}, ${dark ? 70 : 85}%, ${dark ? 62 : 42}%, ${(dark ? 0.3 : 0.45) + 0.55 * Math.sqrt(pr)})`;
      g.beginPath(); g.arc(p[0], p[1], Math.max(2, S * 0.2 * Math.sqrt(pr) * p[3]), 0, 2 * Math.PI); g.fill();
    }
    g.font = "12px system-ui, sans-serif"; g.fillStyle = css("--muted");
    g.fillText(w > 420 ? "3 × 3 × 3 = 27 positions · dashed: the seam {0, 2} that closes each axis" : "27 positions · dashed: the seams", 10, h - 10);
  }

  // ---------- the star of the three axes ----------
  const E3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
  function drawStar(st) {
    const [g, w, h] = setup($("star")), cx = w / 2, cy = h / 2 + 6, S = Math.min(w, h) * 0.42 * ZOOM.star;
    const L = (p) => proj(W(p), cx, cy, S);
    g.lineWidth = 1; g.font = "12px system-ui, sans-serif";
    E3.forEach((e, i) => {
      const a = L(e.map((v) => -v)), b = L(e);
      g.strokeStyle = css("--grid"); g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
      g.fillStyle = css("--muted"); g.fillText("xyz"[i], b[0] + 4, b[1] - 4);
    });
    const tips = [];
    st.forEach((s, a) => {
      const e = E3[a], f = E3[(a + 1) % 3], hth = s.theta / 2;
      const dir = (phi) => e.map((v, i) => Math.cos(phi) * v + Math.sin(phi) * f[i]);
      const T = dir(hth).map((v) => v * Math.sqrt(s.sT2)), Q = dir(-hth).map((v) => v * Math.sqrt(s.sP2));
      tips.push(T, Q, T.map((v) => -v), Q.map((v) => -v));
    });
    const col = css("--blue");
    const polys = NRS3Draw.hull(tips).map((f) => { const q = f.map(L); return [q, q.reduce((a, p) => a + p[2], 0) / q.length]; });
    polys.sort((a, b) => b[1] - a[1]);
    for (const [q] of polys) {
      g.beginPath(); q.forEach((p, i) => (i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]))); g.closePath();
      g.fillStyle = col + "12"; g.fill(); g.strokeStyle = col + "40"; g.lineWidth = 0.8; g.stroke();
    }
    const O = L([0, 0, 0]);
    st.forEach((s, a) => {
      for (let sgn = 0; sgn < 2; sgn++) {
        const T = L(tips[4 * a + 2 * sgn]), Q = L(tips[4 * a + 1 + 2 * sgn]);
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(T[0], T[1]); g.lineTo(Q[0], Q[1]); g.closePath();
        g.fillStyle = col + (sgn ? "33" : "88"); g.fill();
        g.strokeStyle = col; g.lineWidth = sgn ? 1 : 2.4;
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(T[0], T[1]); g.stroke();
        g.lineWidth = sgn ? 1 : 1.6; g.setLineDash(sgn ? [] : [5, 3]);
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(Q[0], Q[1]); g.stroke(); g.setLineDash([]);
      }
      const lab = L(E3[a].map((v) => v * 0.95)), txt = `${"xyz"[a]}: θ = ${deg(s.theta).toFixed(2)}°`;
      const tw = g.measureText(txt).width, lx = Math.max(6, Math.min(w - tw - 6, lab[0] + 6)), ly = Math.max(16, Math.min(h - 26, lab[1]));
      g.fillStyle = css("--panel"); g.globalAlpha = 0.8; g.fillRect(lx - 3, ly - 12, tw + 6, 16); g.globalAlpha = 1;
      g.fillStyle = css("--ink2"); g.fillText(txt, lx, ly);
    });
    g.fillStyle = css("--muted"); g.font = "11.5px system-ui, sans-serif";
    g.fillText("solid: δT°   dashed: δP₃   wedge: θ, cos²θ = light share", 10, h - 10);
  }

  // ---------- light and dark, tension ----------
  function drawShares(st) {
    const [g, w, h] = setup($("shares"));
    const L = 34, R = 12, T = 26, rowH = (h - T - 4) / 3;
    g.font = "12px system-ui, sans-serif";
    st.forEach((s, a) => {
      const y = T + a * rowH, bw = w - L - R, bh = Math.min(22, rowH * 0.36);
      g.fillStyle = css("--ink2"); g.fillText(`${"xyz"[a]}`, 14, y + bh * 0.75);
      g.fillStyle = css("--blue"); g.globalAlpha = 0.85; g.fillRect(L, y, bw * s.light, bh);
      g.fillStyle = css("--violet"); g.globalAlpha = 0.35; g.fillRect(L + bw * s.light, y, bw * s.dark, bh); g.globalAlpha = 1;
      // the value at c: 4/5
      g.strokeStyle = css("--orange"); g.lineWidth = 2; g.beginPath(); g.moveTo(L + bw * 0.8, y - 4); g.lineTo(L + bw * 0.8, y + bh + 4); g.stroke();
      g.fillStyle = css("--ink2");
      g.fillText(`light ${s.light.toFixed(4)} · dark ${s.dark.toFixed(4)}`, L, y + bh + 16);
      const band = Math.abs(s.tension) > 1;
      g.fillStyle = band ? css("--green") : css("--muted");
      g.fillText(`tension ${s.tension.toFixed(4)} ${band ? "· in the band |t| > 1" : "· |t| ≤ 1"}`, L, y + bh + 31);
    });
    g.fillStyle = css("--orange"); g.fillText("| at c: light 4/5, dark 1/5", L, 14);
  }

  // ---------- the ladder (Torus.ladder) ----------
  function drawLadder(st) {
    const [g, w, h] = setup($("ladder"));
    const rungs = [
      { name: "open cube", v: 1, note: "1" },
      { name: "one closed", v: 5 / 4, note: "5/4" },
      { name: "T³", v: 125 / 64, note: "125/64", hi: true },
      { name: "T⁴", v: 625 / 256, note: "625/256" },
    ];
    const L = 46, R = 16, T = 16, B = 46, VMAX = 2.6;
    const Y = (v) => T + (1 - Math.min(v, VMAX) / VMAX) * (h - T - B);
    g.font = "11px system-ui, sans-serif"; g.strokeStyle = css("--grid"); g.fillStyle = css("--muted"); g.lineWidth = 1;
    for (const v of [0, 0.5, 1, 1.5, 2, 2.5]) {
      g.beginPath(); g.moveTo(L, Y(v)); g.lineTo(w - R, Y(v)); g.stroke(); g.fillText(v.toFixed(1), 10, Y(v) + 4);
    }
    const bw = (w - L - R) / rungs.length;
    rungs.forEach((r, i) => {
      const x = L + i * bw + bw * 0.18, ww = bw * 0.64;
      g.fillStyle = r.hi ? css("--blue") : css("--grid");
      g.fillRect(x, Y(r.v), ww, Y(0) - Y(r.v));
      g.fillStyle = r.hi ? css("--blue") : css("--ink2"); g.font = "600 12px system-ui, sans-serif";
      g.fillText(r.note, x + ww / 2 - g.measureText(r.note).width / 2, Y(r.v) - 6);
      g.font = "11px system-ui, sans-serif"; g.fillStyle = css("--muted");
      g.fillText(r.name, x + ww / 2 - g.measureText(r.name).width / 2, h - B + 16);
    });
    // the live value of T³ at Ψ(t)
    const live = st.reduce((p, s) => p * s.ratio, 1), xT3 = L + 2 * bw + bw * 0.82;
    if (Number.isFinite(live)) {
      g.fillStyle = css("--orange"); g.beginPath(); g.arc(xT3, Y(live), 5, 0, 2 * Math.PI); g.fill();
      if (w > 560) {
        g.font = "11px system-ui, sans-serif";
        g.fillText(`Ψ(t) ${live.toFixed(4)}${live > VMAX ? " ↑" : ""}`, xT3 + 9, Math.max(T + 10, Y(live) + 4));
      }
    }
    g.fillStyle = css("--ink2"); g.fillText("det Σ / |det Ω| at the maximal current state", L, h - 10);
  }

  // ---------- rings of any size: spectrum, time, area ----------
  let rings = [4, 4, 4];
  function drawSpectrum() {
    const [g, w, h] = setup($("spectrum"));
    const [dx, dy, dz] = rings, NB = 96, bins = new Array(NB).fill(0);
    const cx = Array.from({ length: dx }, (_, m) => Math.cos(2 * Math.PI * m / dx));
    const cy = Array.from({ length: dy }, (_, m) => Math.cos(2 * Math.PI * m / dy));
    const cz = Array.from({ length: dz }, (_, m) => Math.cos(2 * Math.PI * m / dz));
    let emax = -Infinity, emin = Infinity;
    for (const a of cx) for (const b of cy) for (const c of cz) {
      const E = a + b + c; emax = Math.max(emax, E); emin = Math.min(emin, E);
      bins[Math.min(NB - 1, Math.floor((E + 3) / 6 * NB))]++;
    }
    const L = 16, R = 16, T = 18, B = 34, top = Math.max(...bins);
    const X = (E) => L + (E + 3) / 6 * (w - L - R), Y = (n) => T + (1 - n / top) * (h - T - B);
    g.strokeStyle = css("--grid"); g.lineWidth = 1; g.font = "11px system-ui, sans-serif"; g.fillStyle = css("--muted");
    for (const E of [-3, -2, -1, 0, 1, 2, 3]) {
      g.beginPath(); g.moveTo(X(E), T); g.lineTo(X(E), h - B); g.stroke(); g.fillText(String(E), X(E) - 4, h - B + 14);
    }
    g.fillStyle = css("--violet");
    const bw = (w - L - R) / NB;
    bins.forEach((n, i) => { if (n) g.fillRect(L + i * bw + 0.5, Y(n), Math.max(1, bw - 1), h - B - Y(n)); });
    g.strokeStyle = css("--red"); g.lineWidth = 1.5; g.setLineDash([4, 3]);
    for (const E of [-3, 3]) { g.beginPath(); g.moveTo(X(E), T); g.lineTo(X(E), h - B); g.stroke(); }
    g.setLineDash([]);
    g.fillStyle = css("--ink2");
    g.fillText(w > 560 ? `E = cos(2πa/${dx}) + cos(2πb/${dy}) + cos(2πc/${dz}) · ${dx * dy * dz} levels · range [${emin.toFixed(3)}, ${emax.toFixed(3)}]`
      : `${dx * dy * dz} levels in [${emin.toFixed(3)}, ${emax.toFixed(3)}]`, L, h - 6);
    g.fillStyle = css("--red"); g.fillText("|E| ≤ 3", X(3) - 44, T + 10);
    const even = rings.every((d) => d % 2 === 0);
    $("r-sites").textContent = `${dx} × ${dy} × ${dz} = ${dx * dy * dz}`;
    $("r-time").textContent = even ? "π/6 ≈ 0.5236, attained (all sizes even)" : "≥ π/6 ≈ 0.5236 (attained when all sizes are even)";
    $("r-cut").textContent = `${dy}·${dz} plane + ${dy}·${dz} seam = ${2 * dy * dz}`;
    $("r-S").textContent = `2·${dy}·${dz}·log 2 ≈ ${(2 * dy * dz * Math.log(2)).toFixed(3)}`;
  }

  // ---------- readouts ----------
  const f4 = (x) => (Math.abs(x) < 5e-5 ? 0 : x).toFixed(4);
  function table(st) {
    $("rows").innerHTML = st.map((s, a) =>
      `<tr><td>${"xyz"[a]}</td><td>${f4(s.sT2)}</td><td>${f4(s.sP2)}</td><td>${f4(s.cov)}</td>` +
      `<td>${f4(s.im)}</td><td>${f4(s.tension)}</td><td>${f4(s.light)}</td><td>${f4(s.dark)}</td>` +
      `<td>${Number.isFinite(s.ratio) ? s.ratio.toFixed(4) : "∞"}</td></tr>`).join("");
    const live = st.reduce((p, s) => p * s.ratio, 1);
    $("b-det").textContent = Number.isFinite(live) ? live.toFixed(5) : "∞ (Ω singular)";
    $("b-band").textContent = st.every((s) => Math.abs(s.tension) > 1) ? "all three axes in the band: strict" : "not every axis in the band";
    $("b-state").textContent = { c: "maximal current state c", sat: "minimum uncertainty, tension 1", rnd: "random, every axis in the band" }[kind] + (t > 0 ? `, evolved to t = ${t.toFixed(2)}` : "");
  }

  // ---------- loop ----------
  let lastTs = 0;
  function frame(ts) {
    const dt = lastTs ? Math.min(0.05, (ts - lastTs) / 1000) : 0; lastTs = ts;
    if (ts - lastInteract > 2500) yaw += dt * 0.25;
    if (playing) { t += dt * 0.8; if (t > 4 * Math.PI) t = 0; $("tt").value = t; $("vt").textContent = t.toFixed(2); }
    const V = current(), st = V.map(stats);
    drawTorus(V); drawStar(st); drawShares(st); drawLadder(st); table(st);
    requestAnimationFrame(frame);
  }

  // ---------- controls ----------
  const stop = () => { playing = false; $("play").setAttribute("aria-pressed", "false"); $("play").textContent = "▶ Transport"; };
  document.querySelectorAll("[data-state]").forEach((el) => el.addEventListener("click", () => {
    kind = el.dataset.state;
    base = kind === "rnd" ? [0, 1, 2].map(randomBandState) : [STATES[kind], STATES[kind], STATES[kind]];
    t = 0; $("tt").value = 0; $("vt").textContent = "0.00";
    document.querySelectorAll("[data-state]").forEach((b) => b.setAttribute("aria-pressed", String(b === el)));
  }));
  $("play").addEventListener("click", (e) => {
    playing = !playing; e.target.setAttribute("aria-pressed", String(playing));
    e.target.textContent = playing ? "❚❚ Transport" : "▶ Transport";
  });
  $("reset").addEventListener("click", () => { t = 0; $("tt").value = 0; $("vt").textContent = "0.00"; stop(); });
  $("tt").addEventListener("input", (e) => { t = +e.target.value; $("vt").textContent = t.toFixed(2); stop(); });
  ["rx", "ry", "rz"].forEach((id, i) => $(id).addEventListener("input", (e) => {
    rings[i] = +e.target.value; $("v" + id).textContent = rings[i]; drawSpectrum();
  }));
  for (const c of [$("torus"), $("star")]) {
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
  for (const id of Object.keys(ZOOM)) {
    const c = $(id);
    c.addEventListener("wheel", (e) => { e.preventDefault(); ZOOM[id] = Math.min(6, Math.max(0.5, ZOOM[id] * Math.exp(-e.deltaY * 0.0015))); }, { passive: false });
    c.addEventListener("dblclick", () => { ZOOM[id] = 1; });
  }
  const themeLabel = () => { $("theme").textContent = document.documentElement.dataset.theme === "dark" ? "☀ Light" : "☾ Dark"; };
  try { document.documentElement.dataset.theme = localStorage.getItem("nrs3-theme") || "dark"; }
  catch (e) { document.documentElement.dataset.theme = "dark"; }
  themeLabel();
  $("theme").addEventListener("click", () => {
    const r = document.documentElement;
    r.dataset.theme = r.dataset.theme === "dark" ? "light" : "dark";
    try { localStorage.setItem("nrs3-theme", r.dataset.theme); } catch (e) { /* private mode */ }
    themeLabel(); drawSpectrum();
  });
  addEventListener("resize", drawSpectrum);
  document.querySelector('[data-state="c"]').setAttribute("aria-pressed", "true");
  $("play").setAttribute("aria-pressed", "true"); $("play").textContent = "❚❚ Transport";
  drawSpectrum();
  requestAnimationFrame(frame);

  // exposed for the checks in the page footer
  window.NRS3T3 = { stats, evolve, STATES };
})();

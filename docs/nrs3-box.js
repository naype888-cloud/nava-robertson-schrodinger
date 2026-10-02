(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const FAM = { regular: "--blue", two: "--violet", distinct: "--green" };  // red is reserved for d < 4
  // ---------- the pair (T_d, P_d) and the state ψ* on one axis ----------
  const cache = {};
  function axis(d) {
    if (cache[d]) return cache[d];
    const rho = 2 * Math.cos(Math.PI / (d + 1));
    const p = Array.from({ length: d }, (_, j) => (2 * (j + 1) - (d + 1)) / (d - 1));
    const U = [], lam = [];
    for (let k = 0; k < d; k++) {
      lam.push(2 * Math.cos((k + 1) * Math.PI / (d + 1)) / rho);
      U.push(Array.from({ length: d }, (_, j) => Math.sqrt(2 / (d + 1)) * Math.sin((j + 1) * (k + 1) * Math.PI / (d + 1))));
    }
    const re = [], im = [];
    let nn = 0;
    for (let j = 0; j < d; j++) {
      const s = Math.sin((j + 1) * Math.PI / (d + 1)), ph = j % 4;  // (−i)^j
      re.push(ph === 0 ? s : ph === 2 ? -s : 0); im.push(ph === 1 ? -s : ph === 3 ? s : 0);
      nn += s * s;
    }
    const n = Math.sqrt(nn);
    for (let j = 0; j < d; j++) { re[j] /= n; im[j] /= n; }
    const cr = U.map((u) => u.reduce((a, x, j) => a + x * re[j], 0));
    const ci = U.map((u) => u.reduce((a, x, j) => a + x * im[j], 0));
    const a = { d, rho, p, U, lam, cr, ci };
    a.theta0 = stats(a, evolve(a, 0)).theta;
    return (cache[d] = a);
  }
  function evolve(a, t) {
    const re = new Float64Array(a.d), im = new Float64Array(a.d);
    for (let k = 0; k < a.d; k++) {
      const c = Math.cos(a.lam[k] * t), s = -Math.sin(a.lam[k] * t);
      const zr = c * a.cr[k] - s * a.ci[k], zi = c * a.ci[k] + s * a.cr[k];
      for (let j = 0; j < a.d; j++) { re[j] += zr * a.U[k][j]; im[j] += zi * a.U[k][j]; }
    }
    return { re, im };
  }
  function stats(a, v) {
    const d = a.d, Tr = new Float64Array(d), Ti = new Float64Array(d);
    for (let j = 0; j < d; j++) {
      Tr[j] = ((j > 0 ? v.re[j - 1] : 0) + (j < d - 1 ? v.re[j + 1] : 0)) / a.rho;
      Ti[j] = ((j > 0 ? v.im[j - 1] : 0) + (j < d - 1 ? v.im[j + 1] : 0)) / a.rho;
    }
    let mT = 0, mP = 0;
    for (let j = 0; j < d; j++) { mT += v.re[j] * Tr[j] + v.im[j] * Ti[j]; mP += a.p[j] * (v.re[j] ** 2 + v.im[j] ** 2); }
    const xr = new Float64Array(d), xi = new Float64Array(d), yr = new Float64Array(d), yi = new Float64Array(d);
    let sT = 0, sP = 0, ir = 0, ii = 0;
    for (let j = 0; j < d; j++) {
      xr[j] = Tr[j] - mT * v.re[j]; xi[j] = Ti[j] - mT * v.im[j];
      yr[j] = (a.p[j] - mP) * v.re[j]; yi[j] = (a.p[j] - mP) * v.im[j];
      sT += xr[j] ** 2 + xi[j] ** 2; sP += yr[j] ** 2 + yi[j] ** 2;
      ir += xr[j] * yr[j] + xi[j] * yi[j]; ii += xr[j] * yi[j] - xi[j] * yr[j];
    }
    // angleG = arccos(‖⟨δT, δP⟩‖ / (σT σP)), evaluated stably as atan2(σT ‖δP⊥‖, ‖⟨δT, δP⟩‖)
    let perp = 0;
    if (sT > 1e-24) {
      const cr = ir / sT, ci = ii / sT;
      for (let j = 0; j < d; j++) perp += (yr[j] - cr * xr[j] + ci * xi[j]) ** 2 + (yi[j] - cr * xi[j] - ci * xr[j]) ** 2;
    }
    sT = Math.sqrt(sT); sP = Math.sqrt(sP);
    return { sT, sP, theta: Math.atan2(sT * Math.sqrt(perp), Math.hypot(ir, ii)), mP };
  }

  // ---------- state ----------
  let showBand = true, box = [4, 7, 10], t = 0, playing = false, touring = false, tourIdx = 0, tourNext = 0;
  let yaw = -0.75, pitch = 0.42, autoSpin = true, lastInteract = 0;
  let tips = null, tipsFrom = null, tipsTo = null, morph0 = 0;
  const TOUR = [[4, 4, 4], [4, 4, 10], [4, 10, 10], [10, 10, 10], [4, 7, 10], [16, 5, 8],
                [5, 9, 12], [6, 6, 15], [12, 6, 4], [16, 16, 16], [9, 4, 13], [4, 4, 4]];
  // the quantum needs 4 or more sites on every axis: Random and Tour stay in 4..16
  const randomBox = () => [0, 0, 0].map(() => 4 + Math.floor(Math.random() * 13));
  const low = (d) => d < 4;
  const family = (b) => { const k = new Set(b).size; return k === 1 ? "regular" : k === 2 ? "two" : "distinct"; };

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
  function setup(c) {
    const r = c.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, r.width, r.height);
    return [g, r.width, r.height];
  }
  // y is "up" on screen, so map lattice (x, y, z) -> world (x, z, y): z is vertical
  const W = ([x, y, z]) => [x, z, y];

  function drawAxes(g, cx, cy, S, L, labels) {
    const ax = [[1, 0, 0], [0, 1, 0], [0, 0, 1]], names = ["x", "y", "z"];
    g.lineWidth = 1; g.font = "12px system-ui, sans-serif";
    ax.forEach((e, i) => {
      const a = proj(W(e.map((v) => -v * L)), cx, cy, S), b = proj(W(e.map((v) => v * L)), cx, cy, S);
      g.strokeStyle = css("--grid"); g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
      g.fillStyle = css("--muted"); g.fillText(labels ? labels[i] : names[i], b[0] + 4, b[1] - 4);
    });
  }

  function drawBox() {
    const [g, w, h] = setup($("box")), cx = w / 2, cy = h / 2 + 6, S = Math.min(w, h) * 0.36;
    const A = box.map(axis), V = A.map((a) => evolve(a, t));
    const m = Math.max(...box), s = 2 / (m - 1 || 1);
    const prob = V.map((v) => Array.from(v.re, (r, j) => r * r + v.im[j] * v.im[j]));
    const phase = V.map((v) => Array.from(v.re, (r, j) => Math.atan2(v.im[j], r)));
    const pmax = prob.map((p) => Math.max(...p)).reduce((a, b) => a * b, 1);
    // edges of the box
    const hx = (box[0] - 1) * s / 2, hy = (box[1] - 1) * s / 2, hz = (box[2] - 1) * s / 2;
    const C = [];
    for (const a of [-hx, hx]) for (const b of [-hy, hy]) for (const c of [-hz, hz]) C.push([a, b, c]);
    g.strokeStyle = css("--grid"); g.lineWidth = 1;
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(([i, j]) => {
      const p = proj(W(C[i]), cx, cy, S), q = proj(W(C[j]), cx, cy, S);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    });
    const pts = [];
    for (let i = 0; i < box[0]; i++) for (let j = 0; j < box[1]; j++) for (let k = 0; k < box[2]; k++) {
      const pr = prob[0][i] * prob[1][j] * prob[2][k] / pmax;
      const P = proj(W([i * s - hx, j * s - hy, k * s - hz]), cx, cy, S);
      pts.push([P, pr, phase[0][i] + phase[1][j] + phase[2][k]]);
    }
    pts.sort((a, b) => b[0][2] - a[0][2]);
    const dark = css("--bg").startsWith("#0") || css("--bg").startsWith("#1");
    const rmax = Math.max(2, S * s * 0.4);
    for (const [P, pr, ph] of pts) {
      if (pr < 0.004) {
        g.fillStyle = css("--grid"); g.fillRect(P[0] - 0.8, P[1] - 0.8, 1.6, 1.6); continue;
      }
      const hue = ((ph * 180 / Math.PI) % 360 + 360) % 360;
      g.fillStyle = `hsla(${hue}, 70%, ${dark ? 62 : 50}%, ${0.25 + 0.6 * Math.sqrt(pr)})`;
      g.beginPath(); g.arc(P[0], P[1], Math.max(1.2, rmax * Math.sqrt(pr) * P[3]), 0, 2 * Math.PI); g.fill();
    }
    g.font = "12px system-ui, sans-serif"; g.fillStyle = css("--muted");
    g.fillText(`${box[0]} × ${box[1]} × ${box[2]} = ${box[0] * box[1] * box[2]} sites`, 10, h - 10);
    const bad = box.map((d, i) => (low(d) ? `${"xyz"[i]} = ${d}` : null)).filter(Boolean);
    if (bad.length) {
      g.fillStyle = css("--red"); g.font = "600 12px system-ui, sans-serif";
      g.fillText(`✕ ${bad.join(", ")}: below 4 sites, no quantum`, 10, h - 28);
    }
  }

  // ---------- the star ----------
  const E3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
  const SCALE = 1.25;
  function starTips(st) {
    const out = [];
    for (let a = 0; a < 3; a++) {
      const e = E3[a], f = E3[(a + 1) % 3], hth = st[a].theta / 2;
      const dir = (phi) => e.map((v, i) => Math.cos(phi) * v + Math.sin(phi) * f[i]);
      const T = dir(hth).map((v) => v * st[a].sT * SCALE), P = dir(-hth).map((v) => v * st[a].sP * SCALE);
      out.push(T, P, T.map((v) => -v), P.map((v) => -v));
    }
    return out;
  }
  function drawStar(st) {
    const [g, w, h] = setup($("star")), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.5;
    const famCol = css(FAM[family(box)]), col = box.some(low) ? css("--red") : famCol;
    drawAxes(g, cx, cy, S, 0.95);
    const P = (v) => proj(W(v), cx, cy, S);
    if (showBand) NRS3Draw.arcs(g, P, E3, Math.max(...tips.map((q) => Math.hypot(...q))) * 1.08, css("--ink2"));
    // hull faces, back to front
    const polys = NRS3Draw.hull(tips).map((f) => { const q = f.map(P); return [q, q.reduce((a, p) => a + p[2], 0) / q.length]; });
    polys.sort((a, b) => b[1] - a[1]);
    g.lineJoin = "round";
    for (const [q] of polys) {
      g.beginPath(); q.forEach((p, i) => (i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]))); g.closePath();
      g.fillStyle = col + "12"; g.fill(); g.strokeStyle = col + "40"; g.lineWidth = 0.8; g.stroke();
    }
    // wedges and rays
    const O = P([0, 0, 0]);
    for (let a = 0; a < 3; a++) {
      const col = low(box[a]) ? css("--red") : famCol;
      for (let sgn = 0; sgn < 2; sgn++) {
        const T = P(tips[4 * a + 2 * sgn]), Q = P(tips[4 * a + 1 + 2 * sgn]);
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(T[0], T[1]); g.lineTo(Q[0], Q[1]); g.closePath();
        g.fillStyle = col + (sgn ? "33" : "88"); g.fill();
        g.strokeStyle = col; g.lineWidth = sgn ? 1 : 2.4;
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(T[0], T[1]); g.stroke();
        g.lineWidth = sgn ? 1 : 1.6; g.setLineDash(sgn ? [] : [5, 3]);
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(Q[0], Q[1]); g.stroke(); g.setLineDash([]);
      }
      for (let k = 0; k < 2; k++) {
        const q = P(tips[4 * a + k]);
        g.fillStyle = col; g.beginPath(); g.arc(q[0], q[1], 3.2 * q[3], 0, 2 * Math.PI); g.fill();
      }
      const lab = P(E3[a].map((v) => v * 0.98));
      const th0 = (axis(box[a]).theta0 * 180 / Math.PI).toFixed(2), tht = (st[a].theta * 180 / Math.PI).toFixed(2);
      const txt = low(box[a]) ? `✕ ${"xyz"[a]}: ${box[a]} sites < 4` :
        t > 0 ? `${"xyz"[a]}: ${box[a]} sites, Ψ(t) ${tht}° · θ_NRS ${th0}°` :
        `${"xyz"[a]}: ${box[a]} sites, ${tht}°`;
      g.font = "12px system-ui, sans-serif";
      const tw = g.measureText(txt).width;
      const lx = Math.max(6, Math.min(w - tw - 6, lab[0] + 6)), ly = Math.max(16, Math.min(h - 26, lab[1]));
      g.fillStyle = css("--panel"); g.globalAlpha = 0.8; g.fillRect(lx - 3, ly - 12, tw + 6, 16); g.globalAlpha = 1;
      g.fillStyle = low(box[a]) ? css("--red") : css("--ink2"); g.fillText(txt, lx, ly);
    }
    g.fillStyle = css("--muted"); g.font = "11.5px system-ui, sans-serif";
    g.fillText("solid: δT   dashed: δP   wedge: θ", 10, h - 10);
    if (t > 0) {
      g.fillStyle = css("--ink2"); g.font = "600 12px system-ui, sans-serif";
      g.fillText(`t = ${t.toFixed(1)}: the star shows Ψ(t), not the quantum (press t = 0)`, 10, h - 28);
    }
  }

  // ---------- speed and the quantum (D44) ----------
  // v = ((d − 1)/2)·⟨K⟩, K = i[T, P] (D38); on the path this is −(2/ρ)·Σ Im(z̄_j z_{j+1})
  function speedOf(a, v) {
    let s = 0;
    for (let j = 0; j < a.d - 1; j++) s += v.re[j] * v.im[j + 1] - v.im[j] * v.re[j + 1];
    return -2 / a.rho * s;
  }
  function drawSpeed() {
    const [g, w, h] = setup($("speed")), stack = w < 640;
    const deg = (r) => r * 180 / Math.PI;
    const XS = (u) => (u <= 0.9 ? u / 0.9 * 0.35 : 0.35 + (u - 0.9) / 0.1 * 0.65);  // stretched above 0.9
    for (let a = 0; a < 3; a++) {
      const d = box[a], ax = axis(d), bad = low(d), data = NRS3Speed[d];
      const pw = stack ? w : w / 3, ph = stack ? h / 3 : h, ox = stack ? 0 : a * pw, oy = stack ? a * ph : 0;
      const L = ox + 40, R = ox + pw - 12, T = oy + 26, B = oy + ph - 26;
      const X = (u) => L + XS(Math.min(1, Math.max(0, u))) * (R - L), Y = (th) => B - Math.min(90, th) / 90 * (B - T);
      const col = bad ? css("--red") : css(FAM[family(box)]);
      g.font = "12px system-ui, sans-serif";
      // frame and ticks
      g.strokeStyle = css("--grid"); g.lineWidth = 1; g.strokeRect(L, T, R - L, B - T);
      g.fillStyle = css("--muted");
      for (const u of [0, 0.5, 0.9, 0.95, 1]) {
        g.beginPath(); g.moveTo(X(u), B); g.lineTo(X(u), B + 4); g.stroke();
        g.fillText(String(u), X(u) - (u === 1 ? 6 : 9), B + 15);
      }
      for (const th of [0, 30, 60, 90]) { g.beginPath(); g.moveTo(L - 4, Y(th)); g.lineTo(L, Y(th)); g.stroke(); g.fillText(th + "°", ox + 6, Y(th) + 4); }
      g.setLineDash([2, 3]); g.beginPath(); g.moveTo(X(0.9), T); g.lineTo(X(0.9), B); g.stroke(); g.setLineDash([]);
      // title
      g.font = "600 12.5px system-ui, sans-serif"; g.fillStyle = bad ? css("--red") : css("--ink");
      const title = bad ? `✕ ${"xyz"[a]}: ${d} sites · Ϙ(${d}) empty, no quantum` :
        `${"xyz"[a]}: ${d} sites · v* = ${data.vstar.toFixed(4)}${d === 4 ? " (exact)" : " (numerical)"}`;
      g.fillText(title, L, T - 9);
      g.font = "11px system-ui, sans-serif";
      if (!bad) {
        // minimum uncertainty possible up to v*, the band, the envelope and the quantum
        g.strokeStyle = css("--ink2"); g.lineWidth = 3; g.beginPath(); g.moveTo(X(0), Y(0)); g.lineTo(X(data.vstar), Y(0)); g.stroke();
        g.fillStyle = css("--ink2"); g.fillText("θ = 0 possible", X(0.2), Y(0) - 6);
        g.fillStyle = css("--blue"); g.globalAlpha = 0.13; g.fillRect(X(data.vstar), T, X(1) - X(data.vstar), B - T); g.globalAlpha = 1;
        g.fillStyle = css("--blue"); g.fillText(`Ϙ(${d})`, X(data.vstar) + 3, T + 13);
        g.strokeStyle = css("--blue"); g.lineWidth = 1.4; g.setLineDash([3, 3]); g.beginPath(); g.moveTo(X(data.vstar), Y(0));
        for (const [u, th] of data.env) g.lineTo(X(u), Y(th));
        g.stroke(); g.setLineDash([]);
        const q = deg(ax.theta0);
        g.lineWidth = 2; g.beginPath(); g.arc(X(1), Y(q), 6, 0, 2 * Math.PI); g.stroke();
        g.fillText(`quantum ${q.toFixed(2)}°`, X(1) - 92, Y(q) - 9);
      }
      // the path of Ψ(t) on this axis
      const n = Math.min(600, Math.ceil(t / 0.05)), pts = [];
      for (let k = 0; k <= n; k++) {
        const tk = n ? t * k / n : 0, vk = evolve(ax, tk);
        pts.push([Math.abs(speedOf(ax, vk)), deg(stats(ax, vk).theta)]);
      }
      g.strokeStyle = col; g.lineWidth = 1.3; g.globalAlpha = 0.75; g.beginPath();
      pts.forEach(([u, th], k) => (k ? g.lineTo(X(u), Y(th)) : g.moveTo(X(u), Y(th)))); g.stroke(); g.globalAlpha = 1;
      const [u1, th1] = pts[pts.length - 1];
      g.fillStyle = col; g.beginPath(); g.arc(X(u1), Y(th1), 4.5, 0, 2 * Math.PI); g.fill();
      g.fillStyle = css("--ink2");
      g.fillText(`now: |v| = ${u1.toFixed(3)}, θ = ${th1.toFixed(2)}°`, L + 4, T + 28);
    }
  }

  // ---------- readouts ----------
  function readouts(st) {
    const fam = family(box), names = { regular: "regular", two: "two equal axes", distinct: "three different axes" };
    const f = $("b-fam"); f.textContent = names[fam]; f.style.color = css(FAM[fam]);
    $("b-orb").textContent = { regular: "1 box", two: "3 boxes", distinct: "6 boxes" }[fam];
    $("b-sym").textContent = box.every((d) => d >= 4) ? { regular: "48", two: "16", distinct: "8" }[fam] : "— (needs ≥ 4 sites)";
    const lows = box.map((d, i) => (low(d) ? "xyz"[i] : null)).filter(Boolean);
    const q = $("b-q");
    q.textContent = lows.length ? `✕ none on ${lows.join(", ")} (below 4 sites)` : "present on every axis";
    q.style.color = lows.length ? css("--red") : "";
    $("rows").innerHTML = st.map((s, i) => {
      const a = axis(box[i]), th0 = a.theta0 * 180 / Math.PI;
      const C = a.theta0 > 1e-9 ? (1 / Math.cos(a.theta0)).toFixed(4) : "1";
      return `<tr${low(box[i]) ? ' class="bad"' : ""}><td>${"xyz"[i]}</td><td>${box[i]}</td><td>${(s.theta * 180 / Math.PI).toFixed(2)}°</td>` +
        `<td>${th0.toFixed(2)}°</td><td>${C}</td><td>${s.sT.toFixed(4)}</td><td>${s.sP.toFixed(4)}</td><td>${s.mP.toFixed(3)}</td></tr>`;
    }).join("");
  }

  // ---------- loop ----------
  const ease = (x) => (x < 0.5 ? 2 * x * x : 1 - (-2 * x + 2) ** 2 / 2);
  function currentStats() { return box.map((d) => stats(axis(d), evolve(axis(d), t))); }
  function retarget(animate) {
    const target = starTips(currentStats());
    if (!tips || !animate) { tips = target; tipsTo = null; return; }
    tipsFrom = tips.map((p) => p.slice()); tipsTo = target; morph0 = performance.now();
  }
  // a new box always starts at Ψ* (t = 0): the quantum θ_NRS(d) is read there, not at Ψ(t)
  function stopTransport() {
    playing = false; $("play").setAttribute("aria-pressed", "false"); $("play").textContent = "▶ Transport";
  }
  function setBox(b, animate = true) {
    if (b.join(",") !== box.join(",")) {
      t = 0; $("tt").value = 0; $("vt").textContent = "0.0"; stopTransport();
    }
    box = b.slice();
    ["dx", "dy", "dz"].forEach((id, i) => {
      $(id).value = box[i]; $("v" + "xyz"[i]).textContent = box[i];
      $(id).closest(".sl").classList.toggle("bad", low(box[i]));
    });
    const bad = box.map((d, i) => (low(d) ? `d${"xyz"[i]} = ${d}` : null)).filter(Boolean);
    $("alert").hidden = !bad.length;
    $("alert").textContent = bad.length ? `✕ ${bad.join(", ")} < 4: on ${bad.length > 1 ? "these axes" : "this axis"} ` +
      "Robertson saturates (θ = 0, D37b) and there is no quantum. The quantum needs 4 or more sites on " +
      "every axis: dx, dy, dz ≥ 4." : "";
    document.querySelectorAll("[data-box]").forEach((el) =>
      el.setAttribute("aria-pressed", String(el.dataset.box === box.join(","))));
    retarget(animate);
  }
  let lastTs = 0;
  function frame(ts) {
    const dt = lastTs ? Math.min(0.05, (ts - lastTs) / 1000) : 0; lastTs = ts;
    if (autoSpin && ts - lastInteract > 2500) yaw += dt * 0.25;
    if (playing) { t += dt * 1.6; if (t > 40) t = 0; $("tt").value = t; $("vt").textContent = t.toFixed(1); }
    if (touring && ts > tourNext) {
      tourIdx = (tourIdx + 1) % TOUR.length;
      setBox(tourIdx % 2 ? randomBox() : TOUR[tourIdx]); tourNext = ts + 2600;
    }
    const st = currentStats();
    if (tipsTo) {
      const u = Math.min(1, (ts - morph0) / 900), e = ease(u);
      tips = tipsFrom.map((p, i) => p.map((v, m) => v + (tipsTo[i][m] - v) * e));
      if (u >= 1) tipsTo = null;
    } else if (playing || ts - lastInteract < 50) {
      tips = starTips(st);
    }
    drawBox(); drawStar(st); readouts(st); drawSpeed();
    NRS3Draw.gauge($("band"), st.map((s, i) => ({ name: "xyz"[i], d: box[i], th0: axis(box[i]).theta0, tht: s.theta,
      col: low(box[i]) ? css("--red") : css(FAM[family(box)]) })), SPECTRUM, css, t);
    requestAnimationFrame(frame);
  }

  // ---------- controls ----------
  ["dx", "dy", "dz"].forEach((id, i) => $(id).addEventListener("input", (e) => {
    const b = box.slice(); b[i] = +e.target.value; touring = false; $("tour").setAttribute("aria-pressed", "false"); setBox(b);
  }));
  $("tt").addEventListener("input", (e) => { t = +e.target.value; $("vt").textContent = t.toFixed(1); tips = starTips(currentStats()); tipsTo = null; });
  document.querySelectorAll("[data-box]").forEach((el) => el.addEventListener("click", () => {
    touring = false; $("tour").setAttribute("aria-pressed", "false"); setBox(el.dataset.box.split(",").map(Number));
  }));
  $("random").addEventListener("click", () => {
    touring = false; $("tour").setAttribute("aria-pressed", "false"); setBox(randomBox());
  });
  $("tour").addEventListener("click", (e) => {
    touring = !touring; if (touring) stopTransport(); e.target.setAttribute("aria-pressed", String(touring)); tourNext = 0;
  });
  $("play").addEventListener("click", (e) => {
    playing = !playing; if (playing) { touring = false; $("tour").setAttribute("aria-pressed", "false"); } e.target.setAttribute("aria-pressed", String(playing));
    e.target.textContent = playing ? "❚❚ Transport" : "▶ Transport";
  });
  $("reset").addEventListener("click", () => { t = 0; $("tt").value = 0; $("vt").textContent = "0.0"; retarget(true); });
  for (const c of [$("box"), $("star")]) {
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
  $("theme").addEventListener("click", () => {
    const r = document.documentElement, dark = matchMedia("(prefers-color-scheme: dark)").matches;
    r.dataset.theme = (r.dataset.theme || (dark ? "dark" : "light")) === "dark" ? "light" : "dark";
  });
  const SPECTRUM = Array.from({ length: 63 }, (_, k) => ({ d: k + 2, th: axis(k + 2).theta0 }));
  $("showband").addEventListener("change", (e) => { showBand = e.target.checked; });
  setBox(box, false);
  requestAnimationFrame(frame);
})();

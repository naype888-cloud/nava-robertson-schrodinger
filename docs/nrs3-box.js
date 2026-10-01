(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const FAM = { regular: "--blue", two: "--orange", distinct: "--green" };
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
    let sT = 0, sP = 0, ir = 0, ii = 0;
    for (let j = 0; j < d; j++) {
      const xr = Tr[j] - mT * v.re[j], xi = Ti[j] - mT * v.im[j];
      const yr = (a.p[j] - mP) * v.re[j], yi = (a.p[j] - mP) * v.im[j];
      sT += xr * xr + xi * xi; sP += yr * yr + yi * yi;
      ir += xr * yr + xi * yi; ii += xr * yi - xi * yr;
    }
    sT = Math.sqrt(sT); sP = Math.sqrt(sP);
    const c = sT * sP > 1e-12 ? Math.min(1, Math.hypot(ir, ii) / (sT * sP)) : 1;
    return { sT, sP, theta: Math.acos(c), mP };
  }

  // ---------- state ----------
  let box = [4, 7, 10], t = 0, playing = false, touring = false, tourIdx = 0, tourNext = 0;
  let yaw = -0.75, pitch = 0.42, autoSpin = true, lastInteract = 0;
  let tips = null, tipsFrom = null, tipsTo = null, morph0 = 0;
  const TOUR = [[4, 4, 4], [4, 4, 10], [4, 10, 10], [10, 10, 10], [4, 7, 10], [16, 5, 8],
                [2, 3, 12], [6, 6, 15], [12, 3, 4], [16, 16, 16], [9, 4, 13], [4, 4, 4]];
  const randomBox = () => [0, 0, 0].map(() => 2 + Math.floor(Math.random() * 15));
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
  function hull(ps) {
    const n = ps.length, faces = new Map(), eps = 1e-7;
    const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
    const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
    const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) for (let k = j + 1; k < n; k++) {
      let nv = cross(sub(ps[j], ps[i]), sub(ps[k], ps[i]));
      const L = Math.hypot(...nv); if (L < 1e-9) continue;
      nv = nv.map((v) => v / L);
      let d0 = dot(nv, ps[i]), pos = 0, neg = 0;
      for (const q of ps) { const s = dot(nv, q) - d0; if (s > eps) pos++; else if (s < -eps) neg++; }
      if (pos && neg) continue;
      if (pos) { nv = nv.map((v) => -v); d0 = -d0; }
      const key = nv.map((v) => Math.round(v * 1e4)).join(",") + "|" + Math.round(d0 * 1e4);
      if (faces.has(key)) continue;
      const on = ps.filter((q) => Math.abs(dot(nv, q) - d0) < 1e-6);
      const c = on.reduce((a, q) => a.map((v, m) => v + q[m] / on.length), [0, 0, 0]);
      const u = sub(on[0], c), Lu = Math.hypot(...u) || 1, uu = u.map((v) => v / Lu), vv = cross(nv, uu);
      on.sort((p, q) => Math.atan2(dot(sub(p, c), vv), dot(sub(p, c), uu)) - Math.atan2(dot(sub(q, c), vv), dot(sub(q, c), uu)));
      faces.set(key, on);
    }
    return [...faces.values()];
  }
  function drawStar(st) {
    const [g, w, h] = setup($("star")), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.5;
    const col = css(FAM[family(box)]);
    drawAxes(g, cx, cy, S, 0.95);
    const P = (v) => proj(W(v), cx, cy, S);
    // hull faces, back to front
    const polys = hull(tips).map((f) => { const q = f.map(P); return [q, q.reduce((a, p) => a + p[2], 0) / q.length]; });
    polys.sort((a, b) => b[1] - a[1]);
    g.lineJoin = "round";
    for (const [q] of polys) {
      g.beginPath(); q.forEach((p, i) => (i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]))); g.closePath();
      g.fillStyle = col + "12"; g.fill(); g.strokeStyle = col + "40"; g.lineWidth = 0.8; g.stroke();
    }
    // wedges and rays
    const O = P([0, 0, 0]);
    for (let a = 0; a < 3; a++) {
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
      const lab = P(E3[a].map((v) => v * 0.98)), txt = `${"xyz"[a]}: ${box[a]} sites, ${(st[a].theta * 180 / Math.PI).toFixed(2)}°`;
      g.font = "12px system-ui, sans-serif";
      const tw = g.measureText(txt).width;
      const lx = Math.max(6, Math.min(w - tw - 6, lab[0] + 6)), ly = Math.max(16, Math.min(h - 26, lab[1]));
      g.fillStyle = css("--panel"); g.globalAlpha = 0.8; g.fillRect(lx - 3, ly - 12, tw + 6, 16); g.globalAlpha = 1;
      g.fillStyle = css("--ink2"); g.fillText(txt, lx, ly);
    }
    g.fillStyle = css("--muted"); g.font = "11.5px system-ui, sans-serif";
    g.fillText("solid: δT   dashed: δP   wedge: θ", 10, h - 10);
  }

  // ---------- readouts ----------
  function readouts(st) {
    const fam = family(box), names = { regular: "regular", two: "two equal axes", distinct: "three different axes" };
    const f = $("b-fam"); f.textContent = names[fam]; f.style.color = css(FAM[fam]);
    $("b-orb").textContent = { regular: "1 box", two: "3 boxes", distinct: "6 boxes" }[fam];
    $("b-sym").textContent = box.every((d) => d >= 4) ? { regular: "48", two: "16", distinct: "8" }[fam] : "— (needs ≥ 4 sites)";
    const low = box.map((d, i) => (d <= 3 ? "xyz"[i] : null)).filter(Boolean);
    $("b-q").textContent = low.length ? `erased on ${low.join(", ")} (2 or 3 sites)` : "present on every axis";
    $("rows").innerHTML = st.map((s, i) => {
      const a = axis(box[i]), th0 = a.theta0 * 180 / Math.PI;
      const C = a.theta0 > 1e-9 ? (1 / Math.cos(a.theta0)).toFixed(4) : "1";
      return `<tr><td>${"xyz"[i]}</td><td>${box[i]}</td><td>${(s.theta * 180 / Math.PI).toFixed(2)}°</td>` +
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
  function setBox(b, animate = true) {
    box = b.slice();
    ["dx", "dy", "dz"].forEach((id, i) => { $(id).value = box[i]; $("v" + "xyz"[i]).textContent = box[i]; });
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
    drawBox(); drawStar(st); readouts(st);
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
    touring = !touring; e.target.setAttribute("aria-pressed", String(touring)); tourNext = 0;
  });
  $("play").addEventListener("click", (e) => {
    playing = !playing; e.target.setAttribute("aria-pressed", String(playing));
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
  setBox(box, false);
  requestAnimationFrame(frame);
})();

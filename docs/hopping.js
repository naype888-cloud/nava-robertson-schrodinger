(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const FAM = { regular: "--blue", two: "--violet", distinct: "--green" };

  // H = −2 t T° on one ring. T° has 1/2 on each neighbour, so (H ψ)_j = −t (ψ_{j−1} + ψ_{j+1}).
  const cosK = (d, m) => {
    const k = ((m % d) + d) % d;
    return Math.cos((2 * Math.PI * k) / d);
  };
  const epsOf = (d, m, tHop) => -2 * tHop * cosK(d, m);
  function centred(d) {
    return Array.from({ length: d }, (_, j) => (2 * (j + 1) - (d + 1)) / (d - 1));
  }

  // Ψ(s) on one axis: s = 0 is the site j = 0, s = 1 is the hopping mode m.
  // The two vectors are superposed and renormalised. At the ends one of them has weight 0.
  function stateOf(d, m, s) {
    const phi = Math.max(0, Math.min(1, s)) * Math.PI / 2;
    const alpha = Math.cos(phi), beta = Math.sin(phi);
    const re = new Float64Array(d), im = new Float64Array(d);
    const inv = 1 / Math.sqrt(d);
    for (let j = 0; j < d; j++) {
      const ang = 2 * Math.PI * m * j / d;
      re[j] = beta * inv * Math.cos(ang);
      im[j] = beta * inv * Math.sin(ang);
    }
    re[0] += alpha;
    let n2 = 0;
    for (let j = 0; j < d; j++) n2 += re[j] * re[j] + im[j] * im[j];
    const n = Math.sqrt(n2) || 1;
    for (let j = 0; j < d; j++) { re[j] /= n; im[j] /= n; }
    return { re, im };
  }

  function moments(d, m, s, tHop) {
    const v = stateOf(d, m, s);
    const p = centred(d);
    const Hr = new Float64Array(d), Hi = new Float64Array(d);
    for (let j = 0; j < d; j++) {
      const a = (j + d - 1) % d, b = (j + 1) % d;
      Hr[j] = -tHop * (v.re[a] + v.re[b]);
      Hi[j] = -tHop * (v.im[a] + v.im[b]);
    }
    let mH = 0, mP = 0, h2 = 0, p2 = 0;
    for (let j = 0; j < d; j++) {
      const pr = v.re[j] * v.re[j] + v.im[j] * v.im[j];
      mH += v.re[j] * Hr[j] + v.im[j] * Hi[j];
      mP += p[j] * pr;
      h2 += Hr[j] * Hr[j] + Hi[j] * Hi[j];
      p2 += p[j] * p[j] * pr;
    }
    const sH = Math.sqrt(Math.max(0, h2 - mH * mH));
    const sP = Math.sqrt(Math.max(0, p2 - mP * mP));
    const lam = mH / (-2 * tHop || 1);
    return { v, mH, sH, mP, sP, lam, eps: epsOf(d, m, tHop), cos: cosK(d, m) };
  }

  const DMAX = 25;
  const randomBox = () => [0, 0, 0].map(() => 3 + Math.floor(Math.random() * (DMAX - 2)));
  let box = [3, 3, 3], mode = [1, 0, 0], s = 0, tHop = 1;
  let playing = true, touring = true;
  let yaw = -0.75, pitch = 0.42, autoSpin = true, lastInteract = 0;
  const ZOOM = { box: 1, star: 1, octa: 1 };
  const family = (b) => { const k = new Set(b).size; return k === 1 ? "regular" : k === 2 ? "two" : "distinct"; };

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

  function axesNow() {
    return box.map((d, i) => moments(d, mode[i], s, tHop));
  }

  function drawBox(st) {
    const [g, w, h] = setup($("box")), cx = w / 2, cy = h / 2 + 6, S = Math.min(w, h) * 0.36 * ZOOM.box;
    const m = Math.max(...box), sc = 2 / (m - 1 || 1);
    const prob = st.map((a) => Array.from(a.v.re, (r, j) => r * r + a.v.im[j] * a.v.im[j]));
    const phase = st.map((a) => Array.from(a.v.re, (r, j) => Math.atan2(a.v.im[j], r)));
    const pmax = prob.map((p) => Math.max(...p, 1e-15)).reduce((a, b) => a * b, 1);
    const hx = (box[0] - 1) * sc / 2, hy = (box[1] - 1) * sc / 2, hz = (box[2] - 1) * sc / 2;
    const C = [];
    for (const a of [-hx, hx]) for (const b of [-hy, hy]) for (const c of [-hz, hz]) C.push([a, b, c]);
    g.strokeStyle = css("--grid"); g.lineWidth = 1;
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(([i, j]) => {
      const p = proj(W(C[i]), cx, cy, S), q = proj(W(C[j]), cx, cy, S);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    });
    const idx = box.map((d) => { const n = Math.min(d, 25); return Array.from({ length: n }, (_, k) => Math.floor((k + 0.5) * d / n)); });
    const pts = [];
    for (const i of idx[0]) for (const j of idx[1]) for (const k of idx[2]) {
      const pr = prob[0][i] * prob[1][j] * prob[2][k] / pmax;
      const P = proj(W([i * sc - hx, j * sc - hy, k * sc - hz]), cx, cy, S);
      pts.push([P, pr, phase[0][i] + phase[1][j] + phase[2][k]]);
    }
    pts.sort((a, b) => b[0][2] - a[0][2]);
    const dark = css("--bg").startsWith("#0") || css("--bg").startsWith("#1");
    const rmax = Math.max(2, Math.min(S * 0.13, S * 2 / (Math.max(...idx.map((v) => v.length)) - 1 || 1) * 0.4));
    for (const [P, pr, ph] of pts) {
      if (pr < 0.004) {
        g.fillStyle = css("--grid"); g.fillRect(P[0] - 0.8, P[1] - 0.8, 1.6, 1.6); continue;
      }
      const hue = ((ph * 180 / Math.PI) % 360 + 360) % 360;
      g.fillStyle = `hsla(${hue}, ${dark ? 70 : 85}%, ${dark ? 62 : 42}%, ${(dark ? 0.25 : 0.4) + 0.6 * Math.sqrt(pr)})`;
      g.beginPath(); g.arc(P[0], P[1], Math.max(1.2, rmax * Math.sqrt(pr) * P[3]), 0, 2 * Math.PI); g.fill();
    }
    g.font = "12px system-ui, sans-serif"; g.fillStyle = css("--muted");
    const where = s < 0.02 ? "one site" : s > 0.98 ? "hopping mode" : "between the site and the mode";
    g.fillText(`${box[0]} × ${box[1]} × ${box[2]} · ${where}`, 10, h - 10);
  }

  const E3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
  function drawStar(st) {
    const [g, w, h] = setup($("star")), cx = w / 2, cy = h / 2 + 8, S = Math.min(w, h) * 0.42 * ZOOM.star;
    const col = css(FAM[family(box)]);
    drawAxes(g, cx, cy, S, 1.15, ["cos x", "cos y", "cos z"]);
    const P = (v) => proj(W(v), cx, cy, S);
    const O = P([0, 0, 0]);
    // the cube [−1, 1]³ of one cosine per axis
    const cube = [];
    for (const a of [-1, 1]) for (const b of [-1, 1]) for (const c of [-1, 1]) cube.push([a, b, c]);
    g.strokeStyle = css("--grid"); g.lineWidth = 1;
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(([i, j]) => {
      const p = P(cube[i]), q = P(cube[j]);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    });
    st.forEach((a, i) => {
      const e = E3[i];
      const tip = e.map((v) => v * a.lam);
      const T = P(tip);
      const spread = a.sH / (2 * Math.abs(tHop) || 1);
      const f = E3[(i + 1) % 3];
      const q1 = P(tip.map((v, k) => v + f[k] * spread));
      const q2 = P(tip.map((v, k) => v - f[k] * spread));
      g.strokeStyle = col; g.lineWidth = 2;
      g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(T[0], T[1]); g.stroke();
      g.setLineDash([4, 3]); g.lineWidth = 1.4;
      g.beginPath(); g.moveTo(q1[0], q1[1]); g.lineTo(q2[0], q2[1]); g.stroke();
      g.setLineDash([]);
      g.fillStyle = col; g.beginPath(); g.arc(T[0], T[1], 3.4 * T[3], 0, 2 * Math.PI); g.fill();
      const txt = `${"xyz"[i]}: ⟨cos⟩ ${a.lam.toFixed(3)} · mode ${a.cos.toFixed(3)}`;
      g.font = "12px system-ui, sans-serif";
      const lab = P(e.map((v) => v * 1.05));
      g.fillStyle = css("--ink2"); g.fillText(txt, Math.max(6, Math.min(w - 180, lab[0])), Math.max(16, lab[1]));
    });
    g.fillStyle = css("--muted"); g.font = "11.5px system-ui, sans-serif";
    g.fillText("ray: ⟨cos⟩    dashed: σ_H / (2|t|)    cube: the band of one cosine", 10, h - 10);
  }

  function drawBand(st) {
    const [g, w, h] = setup($("band"));
    const edge = 2 * Math.abs(tHop);
    for (let a = 0; a < 3; a++) {
      const d = box[a];
      const top = 28 + a * ((h - 36) / 3), base = top + (h - 36) / 3 - 18;
      const L = 36, R = w - 16;
      const X = (e) => L + (e + edge) / (2 * edge || 1) * (R - L);
      g.strokeStyle = css("--grid"); g.lineWidth = 1;
      g.beginPath(); g.moveTo(L, base); g.lineTo(R, base); g.stroke();
      g.fillStyle = css("--muted"); g.font = "11px system-ui, sans-serif";
      g.fillText((-edge).toFixed(2), L - 4, base + 14);
      g.fillText("0", X(0) - 4, base + 14);
      g.fillText(edge.toFixed(2), R - 28, base + 14);
      for (let m = 0; m < d; m++) {
        const e = epsOf(d, m, tHop);
        const here = m % d === ((mode[a] % d) + d) % d;
        g.strokeStyle = here ? css("--blue") : css("--ink2");
        g.lineWidth = here ? 2 : 1;
        g.beginPath(); g.moveTo(X(e), base); g.lineTo(X(e), here ? top + 8 : top + 16); g.stroke();
      }
      const e0 = st[a].eps, mh = st[a].mH, sh = st[a].sH;
      g.strokeStyle = css("--blue"); g.lineWidth = 2;
      g.beginPath(); g.arc(X(e0), top + 10, 5, 0, 2 * Math.PI); g.stroke();
      g.fillStyle = css(FAM[family(box)]);
      g.beginPath(); g.arc(X(mh), base - 8, 4.5, 0, 2 * Math.PI); g.fill();
      g.globalAlpha = 0.18; g.fillRect(X(mh - sh), top + 18, Math.max(1, X(mh + sh) - X(mh - sh)), base - top - 22); g.globalAlpha = 1;
      g.fillStyle = css("--ink"); g.font = "600 12px system-ui, sans-serif";
      g.fillText(`${"xyz"[a]}: ${d} positions · mode ${mode[a] % d} · ε ${e0.toFixed(3)}`, L, top + 4);
    }
  }

  const OCTA_FACES = [];
  for (const sx of [1, -1]) for (const sy of [1, -1]) for (const sz of [1, -1]) OCTA_FACES.push([[sx, 0, 0], [0, sy, 0], [0, 0, sz]]);
  function octaEdges(g, ab, cx, cy, S, color, dash, width) {
    g.strokeStyle = color; g.lineWidth = width; g.setLineDash(dash);
    const V = [[ab[0], 0, 0], [-ab[0], 0, 0], [0, ab[1], 0], [0, -ab[1], 0], [0, 0, ab[2]], [0, 0, -ab[2]]];
    for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) {
      if (Math.floor(i / 2) === Math.floor(j / 2)) continue;
      const p = proj(W(V[i]), cx, cy, S), q = proj(W(V[j]), cx, cy, S);
      g.beginPath(); g.moveTo(p[0], p[1]); g.lineTo(q[0], q[1]); g.stroke();
    }
    g.setLineDash([]);
  }
  let octaCur = null;
  function drawOcta(st) {
    const [g, w, h] = setup($("octa")), cx = w / 2, cy = h / 2, S = Math.min(w, h) * 0.36 * ZOOM.octa;
    const target = st.map((a) => Math.abs(a.cos));
    if (!octaCur) octaCur = target.slice();
    octaCur = octaCur.map((v, i) => v + (target[i] - v) * 0.12);
    drawAxes(g, cx, cy, S, 1.25, box.map((d, i) => `${"xyz"[i]}: ${d}`));
    octaEdges(g, [1, 1, 1], cx, cy, S, css("--muted"), [5, 5], 1);
    const col = css(FAM[family(box)]);
    const faces = OCTA_FACES.map((f) => f.map((e) => proj(W(e.map((v, k) => v * octaCur[k])), cx, cy, S)));
    faces.sort((a, b) => (b[0][2] + b[1][2] + b[2][2]) - (a[0][2] + a[1][2] + a[2][2]));
    g.fillStyle = col; g.globalAlpha = 0.2;
    for (const f of faces) { g.beginPath(); g.moveTo(f[0][0], f[0][1]); g.lineTo(f[1][0], f[1][1]); g.lineTo(f[2][0], f[2][1]); g.closePath(); g.fill(); }
    g.globalAlpha = 1;
    octaEdges(g, octaCur, cx, cy, S, col, [], 1.6);
    const mark = proj(W(st.map((a) => a.cos)), cx, cy, S);
    g.fillStyle = css("--orange"); g.beginPath(); g.arc(mark[0], mark[1], 5, 0, 2 * Math.PI); g.fill();
    g.font = "12px system-ui, sans-serif"; g.fillStyle = css("--muted");
    g.fillText("dashed: |cos| = 1, the edge of every ring", 10, h - 28);
    g.fillStyle = css("--ink2");
    g.fillText("solid: |cos| of the occupied mode · orange: (cos x, cos y, cos z)", 10, h - 10);
  }

  function drawDisp(st) {
    const [g, w, h] = setup($("delta"));
    const L = 44, R = 16, T = 16, B = 28, Wd = w - L - R, H = h - T - B;
    const edge = 2 * Math.abs(tHop);
    const X = (u) => L + u * Wd;
    const Y = (e) => T + (1 - (e + edge) / (2 * edge || 1)) * H;
    g.strokeStyle = css("--grid"); g.lineWidth = 1; g.font = "11px system-ui, sans-serif"; g.fillStyle = css("--muted");
    for (const e of [-edge, 0, edge]) {
      g.beginPath(); g.moveTo(L, Y(e)); g.lineTo(L + Wd, Y(e)); g.stroke();
      g.fillText(e.toFixed(1), 4, Y(e) + 4);
    }
    g.fillText("m / d", L + Wd * 0.45, T + H + 18);
    const cols = ["--blue", "--orange", "--green"];
    box.forEach((d, i) => {
      g.strokeStyle = css(cols[i]); g.lineWidth = 1.6; g.beginPath();
      for (let m = 0; m < d; m++) {
        const x = X(m / d), y = Y(epsOf(d, m, tHop));
        if (m) g.lineTo(x, y); else g.moveTo(x, y);
      }
      g.stroke();
      const x = X((mode[i] % d) / d), y = Y(st[i].eps);
      g.fillStyle = css(cols[i]); g.beginPath(); g.arc(x, y, 4.5, 0, 2 * Math.PI); g.fill();
    });
    const E = st.reduce((a, r) => a + r.eps, 0);
    g.fillStyle = css("--ink2"); g.font = "12px system-ui, sans-serif";
    g.fillText(`mode energy ${E.toFixed(3)} · bound ±${(3 * edge).toFixed(2)}`, L, T + 12);
  }

  function drawSpeed(st) {
    const [g, w, h] = setup($("speed")), stack = w < 640;
    for (let a = 0; a < 3; a++) {
      const d = box[a];
      const pw = stack ? w : w / 3, ph = stack ? h / 3 : h, ox = stack ? 0 : a * pw, oy = stack ? a * ph : 0;
      const L = ox + 42, R = ox + pw - 12, T = oy + 26, B = oy + ph - 22;
      const sHmax = 2 * Math.abs(tHop) * Math.SQRT2;
      const X = (u) => L + Math.min(sHmax, Math.max(0, u)) / sHmax * (R - L);
      const Y = (u) => B - Math.min(1.15, Math.max(0, u)) / 1.15 * (B - T);
      g.strokeStyle = css("--grid"); g.lineWidth = 1; g.strokeRect(L, T, R - L, B - T);
      g.fillStyle = css("--muted"); g.font = "11px system-ui, sans-serif";
      g.fillText("σH", R - 16, B + 14); g.fillText("σP", ox + 8, T + 12);
      const n = 48, pts = [];
      for (let k = 0; k <= n; k++) {
        const r = moments(d, mode[a], k / n, tHop);
        pts.push([r.sH, r.sP]);
      }
      g.strokeStyle = css(FAM[family(box)]); g.lineWidth = 1.4; g.beginPath();
      pts.forEach(([u, v], k) => (k ? g.lineTo(X(u), Y(v)) : g.moveTo(X(u), Y(v)))); g.stroke();
      const now = st[a];
      g.fillStyle = css(FAM[family(box)]);
      g.beginPath(); g.arc(X(now.sH), Y(now.sP), 4.5, 0, 2 * Math.PI); g.fill();
      g.fillStyle = css("--ink"); g.font = "600 12px system-ui, sans-serif";
      g.fillText(`${"xyz"[a]}: σH ${now.sH.toFixed(3)} · σP ${now.sP.toFixed(3)}`, L, T - 8);
    }
  }

  function readouts(st) {
    const fam = family(box), names = { regular: "regular", two: "two equal axes", distinct: "three different axes" };
    const f = $("b-fam"); f.textContent = names[fam]; f.style.color = css(FAM[fam]);
    $("b-orb").textContent = mode.map((m, i) => m % box[i]).join(", ");
    const E = st.reduce((a, r) => a + r.eps, 0);
    $("b-sym").textContent = E.toFixed(4) + (box.every((d) => d === 3) && mode.every((m, i) => m % box[i] === 0) ? " = −6t" : "");
    const q = $("b-q");
    if (s > 0.98) { q.textContent = "energy sharp, position spread"; q.style.color = css("--blue"); }
    else if (s < 0.02) { q.textContent = "position sharp, energy spread"; q.style.color = css("--orange"); }
    else { q.textContent = "both spreads open"; q.style.color = ""; }
    $("rows").innerHTML = st.map((r, i) =>
      `<tr><td>${"xyz"[i]}</td><td>${box[i]}</td><td>${mode[i] % box[i]}</td><td>${r.cos.toFixed(4)}</td>` +
      `<td>${r.eps.toFixed(4)}</td><td>${r.mH.toFixed(4)}</td><td>${r.sH.toFixed(4)}</td><td>${r.sP.toFixed(4)}</td></tr>`
    ).join("");
    const cs = st.map((r) => r.cos);
    $("o-d").textContent = cs.map((v) => v.toFixed(4)).join(", ");
    $("o-v").textContent = E.toFixed(4);
    $("o-f").textContent = (Math.abs(E) / (6 * Math.abs(tHop) || 1)).toFixed(4);
    const sH = Math.hypot(...st.map((r) => r.sH));
    $("o-c").textContent = sH.toFixed(4);
  }

  function syncModeSliders() {
    ["mx", "my", "mz"].forEach((id, i) => {
      const el = $(id);
      el.max = String(box[i] - 1);
      if (mode[i] > box[i] - 1) mode[i] = box[i] - 1;
      if (mode[i] < 0) mode[i] = 0;
      el.value = mode[i];
      $("v" + id).textContent = String(mode[i]);
    });
  }
  function setBox(b) {
    box = b.slice();
    ["dx", "dy", "dz"].forEach((id, i) => { $(id).value = box[i]; $("v" + "xyz"[i]).textContent = box[i]; });
    document.querySelectorAll("[data-box]").forEach((el) =>
      el.setAttribute("aria-pressed", String(el.dataset.box === box.join(","))));
    syncModeSliders();
  }
  function freshMode() {
    mode = box.map((d) => Math.floor(Math.random() * d));
    syncModeSliders();
  }

  window.NRS3Rotate = (y, p) => { yaw = y; pitch = p; lastInteract = performance.now(); };
  let lastTs = 0;
  function frame(ts) {
    const dt = lastTs ? Math.min(0.05, (ts - lastTs) / 1000) : 0; lastTs = ts;
    if (autoSpin && ts - lastInteract > 2500) yaw += dt * 0.25;
    if (playing) {
      s += dt * 0.08;
      if (s > 1) {
        s = 0;
        if (touring) { setBox(randomBox()); freshMode(); }
      }
      $("tt").value = s; $("vt").textContent = s.toFixed(2);
    }
    const st = axesNow();
    // the state of the page, read by the doubler card (hopping-doublers.js) on every frame
    window.NRS3Shared = { box: box.slice(), mode: mode.map((m, i) => ((m % box[i]) + box[i]) % box[i]), s, tHop, yaw, pitch,
      lam: st.map((a) => a.lam), V: st.map((a) => a.v) };
    drawBox(st); drawStar(st); drawBand(st); drawOcta(st); drawDisp(st); drawSpeed(st); readouts(st);
    requestAnimationFrame(frame);
  }

  ["dx", "dy", "dz"].forEach((id, i) => $(id).addEventListener("input", (e) => {
    const b = box.slice(); b[i] = +e.target.value; touring = false; $("tour").setAttribute("aria-pressed", "false"); setBox(b);
  }));
  ["mx", "my", "mz"].forEach((id, i) => $(id).addEventListener("input", (e) => {
    mode[i] = +e.target.value; $("v" + id).textContent = String(mode[i]);
  }));
  $("tt").addEventListener("input", (e) => { s = +e.target.value; $("vt").textContent = s.toFixed(2); });
  $("thop").addEventListener("input", (e) => { tHop = +e.target.value; $("vth").textContent = tHop.toFixed(2); });
  document.querySelectorAll("[data-box]").forEach((el) => el.addEventListener("click", () => {
    touring = false; $("tour").setAttribute("aria-pressed", "false"); setBox(el.dataset.box.split(",").map(Number));
  }));
  $("random").addEventListener("click", () => {
    touring = false; $("tour").setAttribute("aria-pressed", "false"); setBox(randomBox()); freshMode();
  });
  $("tour").addEventListener("click", (e) => {
    touring = !touring; e.target.setAttribute("aria-pressed", String(touring));
  });
  $("play").addEventListener("click", (e) => {
    playing = !playing; e.target.setAttribute("aria-pressed", String(playing));
    e.target.textContent = playing ? "❚❚ Hop" : "▶ Hop";
  });
  $("reset").addEventListener("click", () => { s = 0; $("tt").value = 0; $("vt").textContent = "0.00"; });
  for (const c of [$("box"), $("star"), $("octa")]) {
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
  const themeLabel = () => { $("theme").textContent = document.documentElement.dataset.theme === "dark" ? "☀ Light" : "☾ Dark"; };
  try { document.documentElement.dataset.theme = localStorage.getItem("nrs3-theme") || "dark"; }
  catch (e) { document.documentElement.dataset.theme = "dark"; }
  themeLabel();
  $("theme").addEventListener("click", () => {
    const r = document.documentElement;
    r.dataset.theme = r.dataset.theme === "dark" ? "light" : "dark";
    try { localStorage.setItem("nrs3-theme", r.dataset.theme); } catch (e) { /* private mode */ }
    themeLabel();
  });
  document.querySelectorAll(".card").forEach((card) => {
    const b = document.createElement("button");
    b.className = "zoombtn"; b.type = "button"; b.textContent = "⤢ zoom"; b.setAttribute("aria-label", "Open this panel full screen");
    b.addEventListener("click", () => {
      const on = !card.classList.contains("full");
      document.querySelectorAll(".card.full").forEach((c) => { c.classList.remove("full"); c.querySelector(".zoombtn").textContent = "⤢ zoom"; });
      if (on) { card.classList.add("full"); b.textContent = "✕ close"; }
    });
    card.appendChild(b);
  });
  addEventListener("keydown", (e) => {
    if (e.key === "Escape") document.querySelectorAll(".card.full").forEach((c) => { c.classList.remove("full"); c.querySelector(".zoombtn").textContent = "⤢ zoom"; });
  });
  for (const id of Object.keys(ZOOM)) {
    const c = $(id);
    c.addEventListener("wheel", (e) => { e.preventDefault(); ZOOM[id] = Math.min(6, Math.max(0.5, ZOOM[id] * Math.exp(-e.deltaY * 0.0015))); }, { passive: false });
    c.addEventListener("dblclick", () => { ZOOM[id] = 1; });
  }
  $("tour").setAttribute("aria-pressed", "true");
  $("play").setAttribute("aria-pressed", "true"); $("play").textContent = "❚❚ Hop";
  setBox(box);
  requestAnimationFrame(frame);
})();

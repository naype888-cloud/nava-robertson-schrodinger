// Robertson 1934 in every basis: the six observables (H, X) of the open tight binding cube in its
// maximal current state, recombined by a real matrix M. Everything is computed from the matrices:
// the state of each axis, H = −t (hopping), X = a · site, their covariances and brackets, then
// M Σ Mᵀ, M Ω Mᵀ and their determinants (Lean: robertson_det_ratio_invariant,
// robertson_det_recombine_maxCurrentCubeState_strict, robertson_det_recombine_maxCurrentCubeState_mem_band).
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();

  // ---------- one axis: state, H, X ----------
  function axisBlock(N, a, t) {
    // ψ_j ∝ sin((j+1)π/(N+1)) (−i)^j, the maximal current state of the open chain
    const re = new Float64Array(N), im = new Float64Array(N);
    let nn = 0;
    for (let j = 0; j < N; j++) {
      const s = Math.sin((j + 1) * Math.PI / (N + 1)), ph = j % 4;
      re[j] = ph === 0 ? s : ph === 2 ? -s : 0; im[j] = ph === 1 ? -s : ph === 3 ? s : 0; nn += s * s;
    }
    const n = Math.sqrt(nn);
    for (let j = 0; j < N; j++) { re[j] /= n; im[j] /= n; }
    // Hψ and Xψ
    const hr = new Float64Array(N), hi = new Float64Array(N), xr = new Float64Array(N), xi = new Float64Array(N);
    for (let j = 0; j < N; j++) {
      hr[j] = -t * ((j > 0 ? re[j - 1] : 0) + (j < N - 1 ? re[j + 1] : 0));
      hi[j] = -t * ((j > 0 ? im[j - 1] : 0) + (j < N - 1 ? im[j + 1] : 0));
      xr[j] = a * j * re[j]; xi[j] = a * j * im[j];
    }
    const dot = (ar, ai, br, bi) => { let r = 0, i = 0; for (let j = 0; j < N; j++) { r += ar[j] * br[j] + ai[j] * bi[j]; i += ar[j] * bi[j] - ai[j] * br[j]; } return [r, i]; };
    const mH = dot(re, im, hr, hi)[0], mX = dot(re, im, xr, xi)[0];
    // centred vectors
    const dHr = hr.map((v, j) => v - mH * re[j]), dHi = hi.map((v, j) => v - mH * im[j]);
    const dXr = xr.map((v, j) => v - mX * re[j]), dXi = xi.map((v, j) => v - mX * im[j]);
    const vH = dot(dHr, dHi, dHr, dHi)[0], vX = dot(dXr, dXi, dXr, dXi)[0];
    const g = dot(dHr, dHi, dXr, dXi);       // ⟨δH ψ, δX ψ⟩ = cov + i ω⟨⁅H, X⁆⟩, as in Physlib
    const cov = g[0], br = g[1];             // covariance and bracket, both real
    return { S: [[vH, cov], [cov, vX]], W: [[0, br], [-br, 0]], C: Math.sqrt(vH * vX) / Math.abs(br) };
  }

  // ---------- matrices ----------
  const zeros = (n) => Array.from({ length: n }, () => new Array(n).fill(0));
  function blockDiag(blocks) {
    const A = zeros(6);
    blocks.forEach((b, k) => { for (let i = 0; i < 2; i++) for (let j = 0; j < 2; j++) A[2 * k + i][2 * k + j] = b[i][j]; });
    return A;
  }
  const mul = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((s, v, k) => s + v * B[k][j], 0)));
  const tr = (A) => A[0].map((_, j) => A.map((r) => r[j]));
  function det(A0) {
    const A = A0.map((r) => r.slice()), n = A.length;
    let d = 1;
    for (let c = 0; c < n; c++) {
      let p = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
      if (A[p][c] === 0) return 0;
      if (p !== c) { [A[p], A[c]] = [A[c], A[p]]; d = -d; }
      d *= A[c][c];
      for (let r = c + 1; r < n; r++) { const f = A[r][c] / A[c][c]; for (let k = c; k < n; k++) A[r][k] -= f * A[c][k]; }
    }
    return d;
  }
  const gauss = () => { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); };
  // a random basis: Gaussian entries, rows rescaled over three orders of magnitude (a change of units)
  const randomM = () => Array.from({ length: 6 }, () => { const s = 10 ** (3 * Math.random() - 1.5); return Array.from({ length: 6 }, () => s * gauss()); });
  const identity = () => Array.from({ length: 6 }, (_, i) => Array.from({ length: 6 }, (_, j) => (i === j ? 1 : 0)));

  // closed form of C² (Lean: CNava_sq_eq), for the ticks of every box
  function C2(N) {
    const th = Math.PI / (N + 1);
    return 2 * (N - 1) / ((N + 1) * Math.cos(th) ** 2) * (((N + 1) ** 2 + 2) / 6 * Math.sin(th) ** 2 - 1);
  }
  const FLOOR = ((99 - 42 * Math.sqrt(5)) / 5) ** 3, CEIL = (Math.PI ** 2 / 3 - 2) ** 3;
  const ALL = [];
  for (let x = 4; x <= 25; x++) for (let y = x; y <= 25; y++) for (let z = y; z <= 25; z++) ALL.push(C2(x) * C2(y) * C2(z));

  // ---------- state ----------
  let N = [4, 7, 12], a = 1, t = 1, M = identity(), auto = true, next = 0;
  const hist = [];
  let cur = null;
  function compute() {
    const blocks = N.map((n) => axisBlock(n, a, t));
    const S = blockDiag(blocks.map((b) => b.S)), W = blockDiag(blocks.map((b) => b.W));
    const Sb = mul(mul(M, S), tr(M)), Wb = mul(mul(M, W), tr(M));
    const dS = det(Sb), dW = Math.abs(det(Wb)), dM = det(M);
    const Cs = blocks.map((b) => b.C);
    cur = { Sb, Wb, dS, dW, dM2: dM * dM, ratio: dS / dW, C2: (Cs[0] * Cs[1] * Cs[2]) ** 2, Cs };
    hist.push({ lS: Math.log10(dS), lW: Math.log10(dW), r: cur.ratio });
    if (hist.length > 48) hist.shift();
    const f = (v) => v.toExponential(3);
    $("n-s").textContent = f(dS); $("n-o").textContent = f(dW); $("n-m").textContent = f(cur.dM2);
    $("n-r").textContent = cur.ratio.toFixed(6); $("n-c").textContent = cur.C2.toFixed(6);
    $("n-cs").textContent = Cs.map((c) => c.toFixed(5)).join(", ");
  }

  // ---------- drawing ----------
  function setup(c) {
    const r = c.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, r.width, r.height);
    return [g, r.width, r.height];
  }
  function drawHist() {
    const [g, w, h] = setup($("hist")), L = 54, R = 16, T = 14, mid = h * 0.56, B = h - 26;
    g.font = "11px system-ui, sans-serif";
    // top: log10 of the determinants
    const ls = hist.flatMap((p) => [p.lS, p.lW]), lo = Math.floor(Math.min(...ls) - 1), hi = Math.ceil(Math.max(...ls) + 1);
    const X = (k) => L + (w - L - R) * (hist.length > 1 ? k / (hist.length - 1) : 0.5);
    const Y1 = (v) => T + (mid - 18 - T) * (1 - (v - lo) / (hi - lo || 1));
    g.strokeStyle = css("--grid"); g.fillStyle = css("--muted"); g.lineWidth = 1;
    const step = Math.max(1, Math.ceil((hi - lo) / 6));
    for (let v = lo; v <= hi; v += step) { g.beginPath(); g.moveTo(L, Y1(v)); g.lineTo(w - R, Y1(v)); g.stroke(); g.fillText(`1e${v}`, 6, Y1(v) + 4); }
    const line = (key, col, yf) => { g.strokeStyle = col; g.lineWidth = 2; g.beginPath();
      hist.forEach((p, k) => (k ? g.lineTo(X(k), yf(p[key])) : g.moveTo(X(k), yf(p[key])))); g.stroke();
      g.fillStyle = col; hist.forEach((p, k) => { g.beginPath(); g.arc(X(k), yf(p[key]), 2.5, 0, 2 * Math.PI); g.fill(); }); };
    line("lS", css("--orange"), Y1); line("lW", css("--violet"), Y1);
    g.fillStyle = css("--orange"); g.fillText("det Σ", L + 6, T + 10);
    g.fillStyle = css("--violet"); g.fillText("|det Ω|", L + 50, T + 10);
    // bottom: the ratio, inside the band
    const r0 = 0.9, r1 = 2.3, Y2 = (v) => mid + (B - mid) * (1 - (v - r0) / (r1 - r0));
    g.fillStyle = css("--blue"); g.globalAlpha = 0.12; g.fillRect(L, Y2(CEIL), w - L - R, Y2(FLOOR) - Y2(CEIL)); g.globalAlpha = 1;
    g.strokeStyle = css("--blue"); g.lineWidth = 1; g.beginPath(); g.moveTo(L, Y2(FLOOR)); g.lineTo(w - R, Y2(FLOOR)); g.stroke();
    g.setLineDash([5, 4]); g.beginPath(); g.moveTo(L, Y2(CEIL)); g.lineTo(w - R, Y2(CEIL)); g.stroke(); g.setLineDash([]);
    g.strokeStyle = css("--red"); g.beginPath(); g.moveTo(L, Y2(1)); g.lineTo(w - R, Y2(1)); g.stroke();
    g.fillStyle = css("--muted");
    for (const v of [1, 1.5, 2]) g.fillText(v.toFixed(1), 22, Y2(v) + 4);
    g.fillStyle = css("--red"); g.fillText("1: saturation, never from 4 × 4 × 4 on", L + 6, Y2(1) - 4);
    g.fillStyle = css("--blue"); g.fillText(`floor ${FLOOR.toFixed(4)}`, w - R - 110, Y2(FLOOR) + 13);
    g.fillText(`ceiling ${CEIL.toFixed(4)}, never reached`, w - R - 190, Y2(CEIL) - 5);
    line("r", css("--blue"), Y2);
    g.fillStyle = css("--ink2"); g.fillText("det Σ / |det Ω|", L + 6, mid + 4);
  }
  function drawMats() {
    const [g, w, h] = setup($("mats")), names = ["Hx", "Xx", "Hy", "Xy", "Hz", "Xz"];
    const side = Math.min((w - 70) / 2, h - 40), cell = side / 6;
    const one = (A, ox, title) => {
      const m = Math.max(...A.flat().map(Math.abs)) || 1;
      for (let i = 0; i < 6; i++) for (let j = 0; j < 6; j++) {
        const v = A[i][j] / m, hue = v >= 0 ? 24 : 215;
        g.fillStyle = `hsla(${hue}, 80%, 50%, ${Math.min(1, Math.abs(v)) * 0.95 + 0.04})`;
        g.fillRect(ox + j * cell + 1, 26 + i * cell + 1, cell - 2, cell - 2);
      }
      g.fillStyle = css("--ink2"); g.font = "600 12px system-ui, sans-serif"; g.fillText(title, ox, 16);
      g.font = "10px system-ui, sans-serif"; g.fillStyle = css("--muted");
      if (M.every((r, i) => r.every((v, j) => v === (i === j ? 1 : 0))))
        names.forEach((n, i) => { g.fillText(n, ox - 20, 26 + (i + 0.6) * cell); });
    };
    one(cur.Sb, 30, "Σ = M Σ Mᵀ (symmetric)");
    one(cur.Wb, 50 + side, "Ω = M Ω Mᵀ (antisymmetric)");
  }
  function drawBand() {
    const [g, w, h] = setup($("band")), L = 20, R = 20, y = h * 0.55;
    const X = (v) => L + (v - 0.95) / (2.25 - 0.95) * (w - L - R);
    g.font = "11px system-ui, sans-serif";
    g.fillStyle = css("--blue"); g.globalAlpha = 0.12; g.fillRect(X(FLOOR), 18, X(CEIL) - X(FLOOR), h - 40); g.globalAlpha = 1;
    g.strokeStyle = css("--blue"); g.lineWidth = 1.2; g.beginPath(); g.moveTo(X(FLOOR), 18); g.lineTo(X(FLOOR), h - 22); g.stroke();
    g.setLineDash([5, 4]); g.beginPath(); g.moveTo(X(CEIL), 18); g.lineTo(X(CEIL), h - 22); g.stroke(); g.setLineDash([]);
    g.strokeStyle = css("--red"); g.beginPath(); g.moveTo(X(1), 18); g.lineTo(X(1), h - 22); g.stroke();
    g.strokeStyle = css("--violet"); g.globalAlpha = 0.06; g.lineWidth = 1;
    for (const v of ALL) { g.beginPath(); g.moveTo(X(v), y - 14); g.lineTo(X(v), y + 14); g.stroke(); }
    g.globalAlpha = 1;
    g.fillStyle = css("--blue"); g.beginPath(); g.arc(X(cur.C2), y, 7, 0, 2 * Math.PI); g.fill();
    g.fillStyle = css("--ink"); g.font = "600 12px system-ui, sans-serif";
    g.fillText(`${N.join(" × ")}: ${cur.C2.toFixed(4)}`, Math.min(X(cur.C2) - 40, w - 150), y - 20);
    g.font = "11px system-ui, sans-serif"; g.fillStyle = css("--muted");
    for (const v of [1, 1.25, 1.5, 1.75, 2, 2.25]) g.fillText(v.toFixed(2), X(v) - 12, h - 6);
    g.fillStyle = css("--red"); g.fillText("1", X(1) + 4, 30);
    g.fillStyle = css("--blue"); g.fillText("floor 4×4×4", X(FLOOR) + 4, 14); g.fillText("ceiling (π²/3 − 2)³", X(CEIL) - 110, 14);
  }

  function frame(ts) {
    if (auto && ts > next) { if (next) { M = randomM(); compute(); } next = ts + 2500; }
    drawHist(); drawMats(); drawBand();
    requestAnimationFrame(frame);
  }

  // ---------- controls ----------
  ["nx", "ny", "nz"].forEach((id, i) => $(id).addEventListener("input", (e) => { N[i] = +e.target.value; $("v" + id).textContent = N[i]; compute(); }));
  $("la").addEventListener("input", (e) => { a = 10 ** +e.target.value; $("va").textContent = a.toPrecision(3); compute(); });
  $("lt").addEventListener("input", (e) => { t = 10 ** +e.target.value; $("vt").textContent = t.toPrecision(3); compute(); });
  $("newM").addEventListener("click", () => { M = randomM(); compute(); });
  $("ident").addEventListener("click", () => { M = identity(); compute(); });
  $("auto").addEventListener("click", (e) => { auto = !auto; e.target.setAttribute("aria-pressed", String(auto)); next = 0; });
  const themeLabel = () => { $("theme").textContent = document.documentElement.dataset.theme === "dark" ? "☀ Light" : "☾ Dark"; };
  try { document.documentElement.dataset.theme = localStorage.getItem("nrs3-theme") || "dark"; }
  catch (e) { document.documentElement.dataset.theme = "dark"; }
  themeLabel();
  $("theme").addEventListener("click", () => {
    const r = document.documentElement; r.dataset.theme = r.dataset.theme === "dark" ? "light" : "dark";
    try { localStorage.setItem("nrs3-theme", r.dataset.theme); } catch (e) { /* private mode */ }
    themeLabel();
  });
  document.querySelectorAll(".card").forEach((card) => {
    const b = document.createElement("button");
    b.className = "zoombtn"; b.type = "button"; b.textContent = "⤢ zoom";
    b.addEventListener("click", () => {
      const on = !card.classList.contains("full");
      document.querySelectorAll(".card.full").forEach((c) => { c.classList.remove("full"); c.querySelector(".zoombtn").textContent = "⤢ zoom"; });
      if (on) { card.classList.add("full"); b.textContent = "✕ close"; }
    });
    card.appendChild(b);
  });
  addEventListener("keydown", (e) => { if (e.key === "Escape") document.querySelectorAll(".card.full").forEach((c) => { c.classList.remove("full"); c.querySelector(".zoombtn").textContent = "⤢ zoom"; }); });

  // open with a few bases already drawn, so the flat line of the ratio shows at once
  compute();
  for (let k = 0; k < 7; k++) { M = randomM(); compute(); }
  requestAnimationFrame(frame);
})();

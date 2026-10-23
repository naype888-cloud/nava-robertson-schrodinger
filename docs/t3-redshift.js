// The windings of T³ and the redshift from the seam (nrs3-tritoro: SeamRedshift, SeamLightShare).
// Left: one closed axis with its seam; the light winds around it and, at every seam, keeps the
// fraction r of its energy (the light share of the ring of 3 at c, 4/5) and leaves 1 − r dark.
// Below, the cover: the same galaxy at d₀, d₀ + L, d₀ + 2L, …, each image redder and dimmer.
// Right: 1 + z = r⁻ⁿ against the apparent distance, Hubble's law 1 + κ(D − d₀) below it.
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const dark = () => css("--bg").startsWith("#0") || css("--bg").startsWith("#1");
  const HUBBLE_GLY = 299792.458 / 67.66 * 3.2616e-3; // c / H₀ in Gly
  const LAMBDA0 = 400, NMAX = 35;
  let r = 0.8, n = 0, phi = 0, playing = false;

  function setup(c) {
    const b = c.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(b.width * dpr), h = Math.round(b.height * dpr);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, b.width, b.height);
    return [g, b.width, b.height];
  }
  const label = (g, txt, x, y, col, size = 12) => { g.font = `${size}px system-ui, sans-serif`; g.fillStyle = col; g.fillText(txt, x, y); };
  const onePlusZ = (k) => Math.pow(1 / r, k);
  const light = (k) => Math.pow(r, k);

  // the colour of a line emitted at 400 nm after k seams; past 750 nm it is infrared
  function lineColour(k, alpha) {
    const l = LAMBDA0 * onePlusZ(k);
    if (l > 750) return `rgba(${dark() ? "150, 60, 60" : "120, 30, 30"}, ${alpha * 0.55})`;
    let R = 0, G = 0, B = 0;
    if (l < 440) { R = (440 - l) / 60; B = 1; }
    else if (l < 490) { G = (l - 440) / 50; B = 1; }
    else if (l < 510) { G = 1; B = (510 - l) / 20; }
    else if (l < 580) { R = (l - 510) / 70; G = 1; }
    else if (l < 645) { R = 1; G = (645 - l) / 65; }
    else R = 1;
    const f = l > 700 ? 0.3 + 0.7 * (750 - l) / 50 : 1;
    return `rgba(${Math.round(255 * R * f)}, ${Math.round(255 * G * f)}, ${Math.round(255 * B * f)}, ${alpha})`;
  }

  function drawRing() {
    const [g, w, h] = setup($("zring"));
    const cx = w / 2, cy = h * 0.3, R = Math.min(w, h) * 0.2;
    g.strokeStyle = css("--grid"); g.lineWidth = 2; g.beginPath(); g.arc(cx, cy, R, 0, 2 * Math.PI); g.stroke();
    // the seam, at the top
    g.strokeStyle = css("--violet"); g.lineWidth = 3;
    g.beginPath(); g.moveTo(cx, cy - R - 9); g.lineTo(cx, cy - R + 9); g.stroke();
    label(g, "seam: keeps " + (r === 0.8 ? "4/5" : "1/2"), cx + 8, cy - R - 8, css("--violet"));
    // the galaxy, at d₀
    const a0 = -Math.PI / 2 + 0.35 * 2 * Math.PI, gx = cx + R * Math.cos(a0), gy = cy + R * Math.sin(a0);
    g.fillStyle = css("--ink2"); g.beginPath(); g.arc(gx, gy, 5, 0, 2 * Math.PI); g.fill();
    label(g, "galaxy", gx + 8, gy + 4, css("--ink2"), 11);
    // the light, with its trail
    const a = -Math.PI / 2 + phi;
    for (let k = 14; k >= 0; k--) {
      const b = a - k * 0.05;
      g.fillStyle = lineColour(n, Math.max(0.3, light(n)) * (1 - k / 15));
      g.beginPath(); g.arc(cx + R * Math.cos(b), cy + R * Math.sin(b), 6 - k * 0.3, 0, 2 * Math.PI); g.fill();
    }
    // what the light kept and what went dark, after n seams
    const bw = Math.min(w - 28, 2.4 * R), bx = cx - bw / 2, by = cy + R + 26, lw = bw * light(n);
    g.fillStyle = lineColour(n, 0.9); g.fillRect(bx, by, lw, 12);
    g.fillStyle = "#000"; g.fillRect(bx + lw, by, bw - lw, 12);
    g.strokeStyle = css("--grid"); g.lineWidth = 1; g.strokeRect(bx, by, bw, 12);
    label(g, `light ${(100 * light(n)).toFixed(1)}%`, bx, by + 27, css("--ink2"), 11);
    const dt = `dark ${(100 * (1 - light(n))).toFixed(1)}%`;
    g.font = "11px system-ui, sans-serif"; label(g, dt, bx + bw - g.measureText(dt).width, by + 27, css("--ink2"), 11);
    // the cover: the same axis again and again, one image of the galaxy per winding
    const m = 14, y = h * 0.78, N = Math.max(6, n + 2), seg = (w - 2 * m) / N;
    g.strokeStyle = css("--grid"); g.lineWidth = 1.5; g.beginPath(); g.moveTo(m, y); g.lineTo(w - m, y); g.stroke();
    for (let k = 0; k <= N; k++) {
      const x = m + k * seg;
      g.strokeStyle = css("--violet"); g.lineWidth = 2; g.globalAlpha = k === 0 ? 0.3 : 0.8;
      g.beginPath(); g.moveTo(x, y - 7); g.lineTo(x, y + 7); g.stroke(); g.globalAlpha = 1;
    }
    for (let k = 0; k < N; k++) {
      const x = m + (k + 0.35) * seg, rad = Math.max(2, Math.min(9, seg * 0.3));
      g.fillStyle = lineColour(k, Math.max(0.12, light(k)));
      g.beginPath(); g.arc(x, y, rad, 0, 2 * Math.PI); g.fill();
      if (k === n) { g.strokeStyle = css("--ink"); g.lineWidth = 1.5; g.beginPath(); g.arc(x, y, rad + 4, 0, 2 * Math.PI); g.stroke(); }
    }
    label(g, "the cover: d₀, d₀ + L, d₀ + 2L, …  (violet ticks: the seam)", m, y - 22, css("--ink2"), 11);
    const lam = LAMBDA0 * onePlusZ(n);
    label(g, `image n = ${n}: line at ${lam < 1e4 ? lam.toFixed(0) + " nm" : lam.toExponential(1) + " nm"}${lam > 750 ? " (infrared)" : ""}`, m, y + 28, css("--muted"), 11);
  }

  function drawPlot() {
    const [g, w, h] = setup($("zplot"));
    const L = 46, R = 14, T = 18, B = 40, YMAX = 4;
    const X = (k) => L + k / NMAX * (w - L - R), Y = (lz) => h - B - Math.min(lz, YMAX) / YMAX * (h - T - B);
    g.font = "11px system-ui, sans-serif";
    // axes and ticks: 1 + z on a log scale
    g.strokeStyle = css("--grid"); g.lineWidth = 1; g.fillStyle = css("--muted");
    for (let e = 0; e <= YMAX; e++) {
      g.beginPath(); g.moveTo(L, Y(e)); g.lineTo(w - R, Y(e)); g.stroke();
      g.fillText(e === 0 ? "1" : `10${"⁰¹²³⁴"[e]}`, 8, Y(e) + 4);
    }
    for (let k = 0; k <= NMAX; k += 5) { g.fillText(`${k}`, X(k) - 4, h - B + 15); }
    const lgy = HUBBLE_GLY * Math.log(1 / r);
    g.fillStyle = css("--ink2");
    g.fillText(`D − d₀ in windings L  (L = ${lgy.toFixed(1)} Gly)`, L, h - 8);
    // the CMB line, z = 1100
    const zc = Math.log10(1101);
    g.strokeStyle = css("--orange"); g.setLineDash([4, 4]); g.beginPath(); g.moveTo(L, Y(zc)); g.lineTo(w - R, Y(zc)); g.stroke(); g.setLineDash([]);
    const nc = Math.log(1101) / Math.log(1 / r);
    g.fillStyle = css("--orange"); g.fillText(`z = 1100 at ${nc.toFixed(1)} windings`, L + 6, Y(zc) - 5);
    // Hubble's law, 1 + κ(D − d₀), below the exact curve
    g.strokeStyle = css("--green"); g.lineWidth = 1.6; g.setLineDash([6, 4]); g.beginPath();
    for (let k = 0; k <= NMAX; k += 0.25) { const p = [X(k), Y(Math.log10(1 + k * Math.log(1 / r)))]; k ? g.lineTo(...p) : g.moveTo(...p); }
    g.stroke(); g.setLineDash([]);
    // the exact curve, a straight line on this scale, with one point per winding
    g.strokeStyle = css("--blue"); g.lineWidth = 2; g.beginPath();
    g.moveTo(X(0), Y(0)); const kEnd = Math.min(NMAX, YMAX / Math.log10(1 / r)); g.lineTo(X(kEnd), Y(kEnd * Math.log10(1 / r))); g.stroke();
    for (let k = 0; k <= Math.floor(kEnd); k++) {
      g.fillStyle = k === n ? css("--ink") : css("--blue");
      g.beginPath(); g.arc(X(k), Y(k * Math.log10(1 / r)), k === n ? 5.5 : 2.6, 0, 2 * Math.PI); g.fill();
    }
    // legend
    g.font = "12px system-ui, sans-serif";
    const l1 = `1 + z = (${r === 0.8 ? "5/4" : "2"})ⁿ = exp(κ (D − d₀))`, l2 = "Hubble: 1 + κ (D − d₀), a lower bound";
    const lx = w - R - 6 - Math.max(g.measureText(l1).width, g.measureText(l2).width);
    g.fillStyle = css("--blue"); g.fillText(l1, lx, h - B - 26);
    g.fillStyle = css("--green"); g.fillText(l2, lx, h - B - 10);
  }

  function badges() {
    const z1 = onePlusZ(n), big = (v) => (v < 1e4 ? v.toFixed(v < 10 ? 3 : 1) : v.toExponential(2));
    $("z-z").textContent = `(${r === 0.8 ? "5/4" : "2"})^${n} = ${big(z1)}`;
    $("z-ld").textContent = `${(100 * light(n)).toFixed(1)}% · ${(100 * (1 - light(n))).toFixed(1)}%`;
    $("z-d").textContent = `${(n * HUBBLE_GLY * Math.log(1 / r)).toFixed(1)} Gly`;
    $("z-t").textContent = `${big(z1)} × slower`;
    $("vzn").textContent = String(n);
  }

  $("zn").addEventListener("input", (e) => { n = +e.target.value; phi = 0; });
  $("zplay").addEventListener("click", (e) => {
    playing = !playing; e.target.setAttribute("aria-pressed", String(playing));
    e.target.textContent = playing ? "❚❚ Pause" : "▶ Wind";
  });
  document.querySelectorAll("#zcard [data-r]").forEach((b) => b.addEventListener("click", () => {
    r = +b.dataset.r;
    document.querySelectorAll("#zcard [data-r]").forEach((o) => o.setAttribute("aria-pressed", String(o === b)));
  }));
  const visible = (el) => { const b = el.getBoundingClientRect(); return b.bottom > 0 && b.top < innerHeight; };
  let last = 0;
  function frame(ts) {
    const dt = last ? Math.min(0.05, (ts - last) / 1000) : 0; last = ts;
    if (visible($("zcard"))) {
      if (playing) {
        phi += dt * 2.2;
        if (phi >= 2 * Math.PI) { phi -= 2 * Math.PI; n = n >= NMAX ? 0 : n + 1; $("zn").value = String(n); }
      }
      drawRing(); drawPlot(); badges();
    }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
})();

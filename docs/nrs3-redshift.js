// The open box has no windings: the light is reflected at the walls, 1 + z stays 1.
// Same card as t3-redshift.js, with the topology that changes it: no seam, no cover.
(() => {
  const $ = (id) => document.getElementById(id);
  const css = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
  const NMAX = 35;
  let n = 0, phi = 0, playing = false;
  function setup(c) {
    const b = c.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(b.width * dpr), h = Math.round(b.height * dpr);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    const g = c.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, b.width, b.height);
    return [g, b.width, b.height];
  }
  const label = (g, txt, x, y, col, size = 12) => { g.font = `${size}px system-ui, sans-serif`; g.fillStyle = col; g.fillText(txt, x, y); };
  function drawAxis() {
    const [g, w, h] = setup($("zring")), m = 24, y = h * 0.4, L = w - 2 * m;
    g.strokeStyle = css("--grid"); g.lineWidth = 2; g.beginPath(); g.moveTo(m, y); g.lineTo(w - m, y); g.stroke();
    g.strokeStyle = css("--red"); g.lineWidth = 4;
    for (const x of [m, w - m]) { g.beginPath(); g.moveTo(x, y - 16); g.lineTo(x, y + 16); g.stroke(); }
    label(g, "wall", m - 4, y - 22, css("--red"), 11); label(g, "wall", w - m - 12, y - 22, css("--red"), 11);
    const gx = m + 0.35 * L; g.fillStyle = css("--ink2"); g.beginPath(); g.arc(gx, y, 5, 0, 7); g.fill();
    label(g, "galaxy", gx + 8, y + 18, css("--ink2"), 11);
    const u = (phi / Math.PI) % 2, pos = u < 1 ? u : 2 - u;      // triangle wave: out and back
    for (let k = 12; k >= 0; k--) {
      const v = (((phi - k * 0.06) / Math.PI) % 2 + 2) % 2, q = v < 1 ? v : 2 - v;
      g.fillStyle = css("--blue"); g.globalAlpha = 1 - k / 13;
      g.beginPath(); g.arc(m + q * L, y, 6 - k * 0.3, 0, 7); g.fill();
    }
    g.globalAlpha = 1;
    // the cover: here only mirror images of the same box, never a new distance
    const my = h * 0.82, N = Math.max(6, n + 2), seg = (w - 2 * m) / N;
    g.strokeStyle = css("--grid"); g.lineWidth = 1.5; g.beginPath(); g.moveTo(m, my); g.lineTo(w - m, my); g.stroke();
    for (let k = 0; k <= N; k++) { const x = m + k * seg; g.strokeStyle = css("--red"); g.lineWidth = 2; g.globalAlpha = 0.6; g.beginPath(); g.moveTo(x, my - 7); g.lineTo(x, my + 7); g.stroke(); g.globalAlpha = 1; }
    for (let k = 0; k < N; k++) {
      const x = m + (k + (k % 2 ? 0.65 : 0.35)) * seg, rad = Math.max(2, Math.min(9, seg * 0.3));
      g.fillStyle = css("--ink2"); g.beginPath(); g.arc(x, my, rad, 0, 7); g.fill();
      if (k === n) { g.strokeStyle = css("--ink"); g.lineWidth = 1.5; g.beginPath(); g.arc(x, my, rad + 4, 0, 7); g.stroke(); }
    }
    label(g, "mirror images (red: walls); all the same colour, no redshift", m, my - 22, css("--ink2"), 11);
    label(g, `bounce n = ${n}: same colour, same light, same axis`, m, h * 0.6, css("--ink2"), 12);
    label(g, "no seam: the axis is not closed, nothing is kept or left at the wall", m, h * 0.6 + 20, css("--muted"), 11);
  }
  function drawPlot() {
    const [g, w, h] = setup($("zplot")), L = 46, R = 14, T = 18, B = 40, YMAX = 4;
    const X = (k) => L + k / NMAX * (w - L - R), Y = (lz) => h - B - lz / YMAX * (h - T - B);
    g.font = "11px system-ui, sans-serif"; g.strokeStyle = css("--grid"); g.lineWidth = 1; g.fillStyle = css("--muted");
    for (let e = 0; e <= YMAX; e++) { g.beginPath(); g.moveTo(L, Y(e)); g.lineTo(w - R, Y(e)); g.stroke(); g.fillText(e === 0 ? "1" : `10${"⁰¹²³⁴"[e]}`, 8, Y(e) + 4); }
    for (let k = 0; k <= NMAX; k += 5) g.fillText(`${k}`, X(k) - 4, h - B + 15);
    g.fillStyle = css("--ink2"); g.fillText("bounces n (no apparent distance beyond the box)", L, h - 8);
    g.strokeStyle = css("--blue"); g.lineWidth = 2; g.beginPath(); g.moveTo(X(0), Y(0)); g.lineTo(X(NMAX), Y(0)); g.stroke();
    g.fillStyle = css("--ink"); g.beginPath(); g.arc(X(n), Y(0), 5.5, 0, 7); g.fill();
    g.font = "12px system-ui, sans-serif"; g.fillStyle = css("--blue"); g.fillText("1 + z = 1 at every bounce", w - R - 190, Y(0) - 10);
    g.fillStyle = css("--violet"); g.fillText("torus: 1 + z = (5/4)ⁿ needs the seam", w - R - 230, Y(0) - 30);
  }
  function badges() {
    $("z-z").textContent = "1"; $("z-ld").textContent = "0 (open axis)";
    $("z-d").textContent = String(n); $("z-t").textContent = "1 × (not slowed)";
    $("vzn").textContent = String(n);
  }
  $("zn").addEventListener("input", (e) => { n = +e.target.value; phi = 0; });
  $("zplay").addEventListener("click", (e) => {
    playing = !playing; e.target.setAttribute("aria-pressed", String(playing));
    e.target.textContent = playing ? "❚❚ Pause" : "▶ Bounce";
  });
  const visible = (el) => { const b = el.getBoundingClientRect(); return b.bottom > 0 && b.top < innerHeight; };
  let last = 0;
  function frame(ts) {
    const dt = last ? Math.min(0.05, (ts - last) / 1000) : 0; last = ts;
    if (visible($("zcard"))) {
      if (playing) {
        phi += dt * 2.2;
        if (phi >= 2 * Math.PI) { phi -= 2 * Math.PI; n = n >= NMAX ? 0 : n + 1; $("zn").value = String(n); }
      }
      drawAxis(); drawPlot(); badges();
    }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
})();

// Drawing helpers for the NRS³ box explorer: the convex envelope of the star, and the band of
// the quantum θ_NRS(4) ≤ θ_NRS(d) < arccos(1/C_∞) (D37b angle_floor, D48 angleNRS_spectrum_bounds).
window.NRS3Draw = (() => {
  // θ_NRS(4) = arccos(1/√((99 − 42√5)/5)) (D37b angleNRS_four); C_∞ = √(π²/3 − 2) (D8)
  const TH4 = Math.acos(1 / Math.sqrt((99 - 42 * Math.sqrt(5)) / 5));
  const THINF = Math.acos(1 / Math.sqrt(Math.PI ** 2 / 3 - 2));
  const deg = (r) => r * 180 / Math.PI;

  // convex envelope of a few points: faces as ordered polygons, coplanar points merged
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
      const ang = (p) => Math.atan2(dot(sub(p, c), vv), dot(sub(p, c), uu));
      on.sort((p, q) => ang(p) - ang(q));
      faces.set(key, on);
    }
    return [...faces.values()];
  }

  // the band inside the star: in the plane of each axis, the half-angles θ/2 allowed at Ψ*
  function arcs(g, P, E3, R, ink) {
    for (let a = 0; a < 3; a++) {
      const e = E3[a], f = E3[(a + 1) % 3];
      for (const flip of [1, -1]) for (const side of [1, -1]) {
        const pt = (phi) => e.map((v, i) => flip * R * (Math.cos(phi) * v + side * Math.sin(phi) * f[i]));
        const O = P([0, 0, 0]);
        g.beginPath(); g.moveTo(O[0], O[1]);
        for (let k = 0; k <= 12; k++) { const q = P(pt(TH4 / 2 + (THINF - TH4) / 2 * k / 12)); g.lineTo(q[0], q[1]); }
        g.closePath(); g.fillStyle = ink; g.globalAlpha = 0.09; g.fill(); g.globalAlpha = 1;
        const c = P(pt(THINF / 2));
        g.strokeStyle = ink; g.globalAlpha = 0.45; g.lineWidth = 1; g.setLineDash([3, 3]);
        g.beginPath(); g.moveTo(O[0], O[1]); g.lineTo(c[0], c[1]); g.stroke(); g.setLineDash([]); g.globalAlpha = 1;
      }
    }
  }

  // the gauge: one ruler per axis, plus every θ_NRS(d) at Ψ*
  function gauge(canvas, rows, spectrum, css, t) {
    const r = canvas.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
    if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
    const g = canvas.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, r.width, r.height);
    const W0 = r.width, H0 = r.height, L = Math.min(150, W0 * 0.3), R = 14, T = 22, B = 24, MAX = 60;
    const X = (rad) => L + Math.min(deg(rad), MAX) / MAX * (W0 - L - R);
    const rowH = (H0 - T - B) / 4, Y = (k) => T + rowH * (k + 0.5);
    g.font = "12px system-ui, sans-serif";
    // band and ceiling
    g.fillStyle = css("--blue"); g.globalAlpha = 0.12; g.fillRect(X(TH4), T - 6, X(THINF) - X(TH4), H0 - T - B + 6); g.globalAlpha = 1;
    g.strokeStyle = css("--blue"); g.lineWidth = 1.2;
    g.beginPath(); g.moveTo(X(TH4), T - 6); g.lineTo(X(TH4), H0 - B); g.stroke();
    g.setLineDash([5, 4]); g.beginPath(); g.moveTo(X(THINF), T - 6); g.lineTo(X(THINF), H0 - B); g.stroke(); g.setLineDash([]);
    g.fillStyle = css("--blue");
    g.fillText(`floor θ_NRS(4) = ${deg(TH4).toFixed(2)}°`, X(TH4) - 4 - g.measureText("floor θ_NRS(4) = 7.43°").width, 13);
    g.fillText(`ceiling arccos(1/C∞) = ${deg(THINF).toFixed(2)}°, never reached`, X(THINF) + 4, 13);
    // angle ticks
    g.fillStyle = css("--muted"); g.strokeStyle = css("--grid");
    for (let a = 0; a <= MAX; a += 10) { const x = X(a * Math.PI / 180);
      g.beginPath(); g.moveTo(x, H0 - B); g.lineTo(x, H0 - B + 4); g.stroke(); g.fillText(`${a}°`, x - 8, H0 - 6); }
    // row 0: every box
    g.fillStyle = css("--ink2"); g.fillText("all boxes, at Ψ*", 6, Y(0) + 4);
    g.strokeStyle = css("--grid"); g.beginPath(); g.moveTo(X(0), Y(0)); g.lineTo(X(MAX * Math.PI / 180), Y(0)); g.stroke();
    for (const { d, th } of spectrum) {
      const x = X(th), hgt = d <= 3 ? 0 : 7 + 5 * Math.exp(-(d - 4) / 12);
      if (d <= 3) continue;
      g.strokeStyle = css("--blue"); g.globalAlpha = 0.35 + 0.65 * Math.exp(-(d - 4) / 20); g.lineWidth = 1.4;
      g.beginPath(); g.moveTo(x, Y(0) - hgt); g.lineTo(x, Y(0) + hgt); g.stroke(); g.globalAlpha = 1;
    }
    g.fillStyle = css("--orange"); g.font = "bold 13px system-ui, sans-serif"; g.fillText("×", X(0) - 4, Y(0) + 5);
    g.font = "11px system-ui, sans-serif"; g.fillStyle = css("--ink2");
    g.fillText("d = 2, 3: 0°", X(0) + 6, Y(0) + 16); g.fillText("d = 4", X(spectrum.find((s) => s.d === 4).th) - 12, Y(0) - 12);
    g.fillText(`d = ${spectrum[spectrum.length - 1].d} →`, X(spectrum[spectrum.length - 1].th) - 44, Y(0) - 12);
    // rows 1..3: the axes of this box
    rows.forEach((row, i) => {
      const y = Y(i + 1);
      g.font = "12.5px system-ui, sans-serif"; g.fillStyle = css("--ink");
      g.fillText(`${row.name}: ${row.d} sites`, 6, y - 2);
      const star = row.d <= 3 ? "Ψ*: erased (0°)" : "Ψ*: in the band";
      const inb = row.tht >= TH4 - 1e-9 && row.tht < THINF;
      const now = t > 0 ? (inb ? " · Ψ(t): inside" : " · Ψ(t): outside") : "";
      g.font = "11px system-ui, sans-serif"; g.fillStyle = row.d <= 3 ? css("--orange") : css("--muted");
      g.fillText(star + now, 6, y + 13);
      g.strokeStyle = css("--grid"); g.lineWidth = 1; g.beginPath(); g.moveTo(X(0), y); g.lineTo(X(MAX * Math.PI / 180), y); g.stroke();
      g.strokeStyle = row.col; g.lineWidth = 2; g.beginPath(); g.arc(X(row.th0), y, 7, 0, 2 * Math.PI); g.stroke();
      g.fillStyle = row.col; g.beginPath(); g.arc(X(row.tht), y, 4.5, 0, 2 * Math.PI); g.fill();
      if (deg(row.tht) > MAX) { g.font = "11px system-ui, sans-serif"; g.fillText(`▸ ${deg(row.tht).toFixed(0)}°`, X(MAX * Math.PI / 180) - 34, y - 8); }
    });
  }

  return { TH4, THINF, hull, arcs, gauge };
})();

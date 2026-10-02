"""Figure for the band of the NRS quantum on one axis (numpy, matplotlib).

Writes docs/figures/nrs_band.png.

(a) C_Nava(d) from 1 (d = 2, 3, saturation) to its limit C∞ = √(π²/3 − 2) ≈ 1.13572, never
reached; the excess C_Nava(d) − 1 over saturation grows to C∞ − 1 ≈ 0.13572.
(b) the angle θ_NRS(d) = arccos(1/C_Nava(d)): 0 at d = 2, 3, a jump to θ_NRS(4) ≈ 7.435°, then
strictly increasing towards arccos(1/C∞) ≈ 28.298°, never reached.
(c) the same angles as rays: every axis of every box with 4 or more sites opens inside the
wedge [7.435°, 28.298°).

Proved in Lean (base repository): θ_NRS(d) = arccos(1/C_Nava(d)) (D37b, angleNRS_eq); for
d ≥ 4, 0 < θ_NRS(4) ≤ θ_NRS(d) < arccos(1/C∞) (D37b, angle_floor); C_Nava → C∞ (D8) and
strictly increasing from d = 4 on (D9). The values plotted are evaluated from the closed form
of C_Nava² (D19, D20).

Run:  python3 docs/simulation/figures_nrs_band.py
"""

import matplotlib.pyplot as plt
import numpy as np

from figures_threshold_cone import GRID, INK, INK2, MUTED, OUT, SURFACE

BLUE, ORANGE, GREEN = "#2a78d6", "#eb6834", "#2f8f5b"
BAND = "#e3eefb"
C_INF = np.sqrt(np.pi ** 2 / 3 - 2)
TH_INF = np.degrees(np.arccos(1 / C_INF))


def c_nava(d):
    d = np.asarray(d, dtype=float)
    th = np.pi / (d + 1)
    s2 = np.sin(th) ** 2
    var_h = 4 * s2 * (d - 1) / (d + 1)
    var_x = ((d + 1) ** 2 + 2) / 12 - 1 / (2 * s2)
    return np.sqrt(np.maximum(var_h * var_x / np.cos(th) ** 2, 1.0))


def theta(d):
    return np.degrees(np.arccos(np.minimum(1.0, 1 / c_nava(d))))


def fig_band():
    fig = plt.figure(figsize=(14.5, 5.0), dpi=150)
    gs = fig.add_gridspec(1, 3, width_ratios=[1, 1, 1.25])
    ax = fig.add_subplot(gs[0])
    bx = fig.add_subplot(gs[1])
    cx = fig.add_subplot(gs[2], projection="polar")

    dl = np.unique(np.round(np.logspace(np.log10(4), 4, 400)).astype(int))
    dp = np.arange(2, 31)
    first = {4: ORANGE, 5: ORANGE, 6: ORANGE}

    c4 = float(c_nava(4))
    ax.axhspan(c4, C_INF, color=BAND, lw=0)
    ax.axhline(C_INF, color=INK2, lw=1.2, ls="--")
    ax.axhline(1, color=MUTED, lw=1)
    ax.plot(dl, c_nava(dl), color=BLUE, lw=1.8)
    ax.plot(dp, c_nava(dp), "o", color=BLUE, mec=SURFACE, mew=0.8, ms=4.5)
    ax.plot([2, 3], [1, 1], "o", color=GREEN, mec=SURFACE, mew=1, ms=7, label="d = 2, 3: saturation, C = 1")
    for d, col in first.items():
        ax.plot(d, c_nava(d), "o", color=col, mec=INK, mew=0.8, ms=7)
    ax.plot([], [], "o", color=ORANGE, mec=INK, mew=0.8, ms=7, label="d = 4, 5, 6: past the rupture")
    ax.text(10 ** 4, C_INF + 0.003, f"C∞ = √(π²/3 − 2) ≈ {C_INF:.5f}", ha="right", va="bottom",
            color=INK2, fontsize=9.5)
    ax.annotate("", xy=(6000, C_INF), xytext=(6000, 1), arrowprops=dict(arrowstyle="<->", color=INK2, lw=1))
    ax.text(5200, (1 + C_INF) / 2, f"excess\nC∞ − 1 ≈ {C_INF - 1:.5f}", ha="right", va="center",
            color=INK2, fontsize=9)
    ax.set_xscale("log")
    ax.set_xlim(1.8, 1.2e4)
    ax.set_ylim(0.99, 1.155)
    ax.set_xlabel("sites on the axis  d")
    ax.set_ylabel("C_Nava(d)")
    ax.legend(loc="center left", bbox_to_anchor=(0.0, 0.62), fontsize=8.5)
    ax.set_title("(a) C_Nava: from 1 to C∞, never reached", loc="left", fontsize=11)

    t4 = float(theta(4))
    bx.axhspan(t4, TH_INF, color=BAND, lw=0)
    bx.axhline(TH_INF, color=INK2, lw=1.2, ls="--")
    bx.axhline(t4, color=ORANGE, lw=1, ls=":")
    bx.plot(dl, theta(dl), color=BLUE, lw=1.8)
    bx.plot(dp, theta(dp), "o", color=BLUE, mec=SURFACE, mew=0.8, ms=4.5)
    bx.plot([2, 3], [0, 0], "o", color=GREEN, mec=SURFACE, mew=1, ms=7)
    for d, col in first.items():
        bx.plot(d, theta(d), "o", color=col, mec=INK, mew=0.8, ms=7)
        bx.text(d, theta(d) + 1.0, f"{theta(d):.2f}°", ha="center", fontsize=8, color=INK2)
    bx.text(10 ** 4, TH_INF + 0.6, f"arccos(1/C∞) ≈ {TH_INF:.3f}°", ha="right", color=INK2, fontsize=9.5)
    bx.text(10 ** 4, t4 - 2.2, f"θ_NRS(4) ≈ {t4:.3f}°", ha="right", color=ORANGE, fontsize=9.5)
    bx.text(2.5, 1.2, "0°", ha="center", color=GREEN, fontsize=9)
    bx.set_xscale("log")
    bx.set_xlim(1.8, 1.2e4)
    bx.set_ylim(-1.5, 31)
    bx.set_xlabel("sites on the axis  d")
    bx.set_ylabel("θ_NRS(d)  [degrees]")
    bx.set_title("(b) the angle: a jump at 4, then the band", loc="left", fontsize=11)

    r_inf, t_inf = 1.0, np.radians(TH_INF)
    cx.fill_between(np.radians(np.linspace(t4, TH_INF, 100)), 0, r_inf, color=BAND, lw=0)
    cx.plot([0, 0], [0, r_inf], color=GREEN, lw=2)
    for d in (4, 5, 6, 10, 20):
        col = ORANGE if d <= 6 else BLUE
        t = np.radians(float(theta(d)))
        cx.plot([t, t], [0, r_inf], color=col, lw=1.6 if d <= 6 else 1.2)
        cx.text(t, 1.04, f"d = {d}  ({theta(d):.2f}°)", ha="left", va="center", fontsize=8,
                color=col, rotation=np.degrees(t), rotation_mode="anchor")
    cx.plot([t_inf, t_inf], [0, r_inf], color=INK2, lw=1.4, ls="--")
    cx.text(t_inf, 1.04, f"d → ∞  ({TH_INF:.2f}°, never reached)", ha="left", va="center",
            fontsize=8, color=INK2, rotation=TH_INF, rotation_mode="anchor")
    cx.text(0, 1.04, "d = 2, 3  (0°, saturation)", ha="left", va="center", fontsize=8, color=GREEN)
    cx.set_thetamin(0)
    cx.set_thetamax(30)
    cx.set_rmax(1.0)
    cx.set_rticks([])
    cx.set_xticks([])
    cx.grid(color=GRID)
    cx.set_title("(c) every axis opens inside the wedge", loc="left", fontsize=11, pad=14)

    fig.suptitle("The NRS quantum on one axis: 7.43° ≤ θ_NRS(d) < 28.30°, 1 < C_Nava(d) < 1.13572  (d ≥ 4)",
                 x=0.01, ha="left", fontsize=12.5, color=INK)
    fig.text(0.01, 0.01, "Lean: angleNRS_eq, angle_floor (D37b); limit (D8) and strict monotonicity (D9). "
             "Values from the closed form of C_Nava² (D19, D20).", fontsize=8.5, color=MUTED)
    fig.tight_layout(rect=(0, 0.03, 1, 1))
    fig.savefig(OUT / "nrs_band.png", facecolor=SURFACE)
    plt.close(fig)


if __name__ == "__main__":
    fig_band()

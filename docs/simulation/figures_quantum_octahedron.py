"""Figure for the octahedron of the NRS quantum (numpy, matplotlib).

Writes docs/figures/nrs_quantum_octahedron.png.

Each axis with d positions carries the dimensional quantum δ(d) = C_Nava(d) − 1 (D25) and opens at
θ_NRS(d) = arccos(1/(1 + δ(d))) (D37b). The octahedron of a box dx × dy × dz has its vertices at
±δ(dx), ±δ(dy), ±δ(dz) on the three axes: its volume is (4/3)·δ(dx)δ(dy)δ(dz) = (4/3)·𝒱, the
volumetric quantum of D37e times 4/3.
(a) the octahedra of 4 × 4 × 4 (the smallest), 10 × 10 × 10, 4 × 10 × 10 and 4 × 7 × 10, inside
the unattained one of d → ∞ (δ_∞ = C∞ − 1 on every axis, dashed).
(b) the quantum and the angle of every axis of those boxes, between δ(4) and δ_∞.
(c) how the deformations group: the three families of D37i.

Proved in Lean (base repository): δ(d) = 0 iff d = 2, 3 (D25, dimQuantum_eq_zero_iff);
θ_NRS(d) = arccos(1/C_Nava(d)) (D37b, angleNRS_eq); δ(4)³ ≤ 𝒱 < δ_∞³, strictly increasing in
each axis (D37e, volQuantum_certificate); every box with 4 or more positions keeps its quantum, in
one of three families (D37i, quantum_never_erased, family_partition, card_orbit_*). Values are
evaluated from the closed form of C_Nava² (D19, D20); the factor 4/3 is the volume of the
octahedron |x|/a + |y|/b + |z|/c ≤ 1.

Run:  python3 docs/simulation/figures_quantum_octahedron.py
"""

import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

from figures_nrs_band import C_INF, c_nava, theta
from figures_threshold_cone import GRID, INK, INK2, MUTED, OUT, SURFACE

REGULAR, TWO, DISTINCT = "#2a78d6", "#eb6834", "#2f8f5b"
D_INF = C_INF - 1
BOXES = [((4, 4, 4), REGULAR, "4 × 4 × 4  (regular, the smallest)"),
         ((10, 10, 10), REGULAR, "10 × 10 × 10  (regular)"),
         ((4, 10, 10), TWO, "4 × 10 × 10  (two equal axes)"),
         ((4, 7, 10), DISTINCT, "4 × 7 × 10  (three different axes)")]


def delta(d):
    return float(c_nava(d)) - 1


def octa(a, b, c):
    v = {"x+": (a, 0, 0), "x-": (-a, 0, 0), "y+": (0, b, 0), "y-": (0, -b, 0),
         "z+": (0, 0, c), "z-": (0, 0, -c)}
    faces = []
    for sx in ("x+", "x-"):
        for sy in ("y+", "y-"):
            for sz in ("z+", "z-"):
                faces.append([v[sx], v[sy], v[sz]])
    return faces


def draw_octa(ax, box, col, title):
    s = 1 / D_INF
    for f in octa(1, 1, 1):
        ax.add_collection3d(Poly3DCollection([f], facecolor=(0, 0, 0, 0), edgecolor=MUTED,
                                             linestyle=(0, (3, 3)), linewidth=0.7))
    a, b, c = (delta(d) * s for d in box)
    ax.add_collection3d(Poly3DCollection(octa(a, b, c), facecolor=col, alpha=0.35,
                                         edgecolor=col, linewidth=1.2))
    for k, lab in enumerate(("x", "y", "z")):
        e = np.zeros(3)
        e[k] = 1.18
        ax.plot(*zip(-e, e), color=GRID, lw=0.8)
        ax.text(*(e * 1.05), f"{lab}={box[k]}", color=INK2, fontsize=8)
    lim = 1.0
    ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim); ax.set_zlim(-lim, lim)
    ax.set_box_aspect((1, 1, 1))
    ax.set_axis_off()
    ax.view_init(elev=20, azim=35)
    vol = np.prod([delta(d) for d in box]) / D_INF ** 3
    ax.set_title(title, fontsize=10, color=col, pad=0)
    ax.text2D(0.5, 0.02, "δ: " + ", ".join(f"{delta(d):.4f}" for d in box)
              + f"\nvolume = {100 * vol:.2g}% of the d → ∞ one", ha="center", fontsize=8,
              color=INK2, transform=ax.transAxes)


def fig_octahedron():
    fig = plt.figure(figsize=(15, 9.6), dpi=150)
    gs = fig.add_gridspec(2, 4, height_ratios=[1.05, 1], hspace=0.32)
    tops = [fig.add_subplot(gs[0, k], projection="3d") for k in range(4)]
    bx = fig.add_subplot(gs[1, :2])
    cx = fig.add_subplot(gs[1, 2:])

    # (a) one octahedron per box, inside the unattained one of d → ∞ (dashed)
    for axk, (box, col, lab) in zip(tops, BOXES):
        draw_octa(axk, box, col, lab.split("  ")[0] + "\n" + lab.split("  ")[1])
    fig.text(0.01, 0.925, "(a) vertices at ±δ(dx), ±δ(dy), ±δ(dz); dashed: d → ∞, δ_∞ on every axis "
             "(never reached)", fontsize=11, color=INK)

    # (b) per axis
    xs, labels = [], []
    for j, ((dx, dy, dz), col, _) in enumerate(BOXES):
        for k, d in enumerate((dx, dy, dz)):
            x = j * 4 + k
            bx.bar(x, delta(d), color=col, alpha=0.85, width=0.8)
            bx.text(x, delta(d) + 0.003, f"{theta(d):.1f}°", ha="center", fontsize=7.5, color=INK2)
            xs.append(x)
            labels.append(f"{'xyz'[k]}={d}")
    bx.axhline(delta(4), color=REGULAR, lw=1, ls=":")
    bx.axhline(D_INF, color=INK2, lw=1.2, ls="--")
    bx.text(14.4, D_INF + 0.003, "δ_∞ = C∞ − 1 ≈ 0.13572, θ → 28.30°", ha="right", fontsize=8.5,
            color=INK2)
    bx.text(-0.6, 0.118, "dotted: δ(4) ≈ 0.00848, θ = 7.43° (the floor, 4 × 4 × 4)", ha="left",
            fontsize=8.5, color=REGULAR)
    bx.set_xticks(xs)
    bx.set_xticklabels(labels, fontsize=7.5, rotation=0)
    bx.set_ylim(0, 0.155)
    bx.set_ylabel("δ(d) = C_Nava(d) − 1")
    bx.set_title("(b) every axis: its own quantum and angle, between δ(4) and δ_∞",
                 loc="left", fontsize=11)
    for j, ((dx, dy, dz), col, _) in enumerate(BOXES):
        bx.text(j * 4 + 1, -0.17, f"{dx}×{dy}×{dz}", ha="center", fontsize=8.5, color=col,
                transform=bx.get_xaxis_transform())

    # (c) families
    cx.set_axis_off()
    rows = [("family", "example", "symmetries", "boxes / figure", "first one"),
            ("regular", "4 × 4 × 4", "48  (O_h)", "1", "4 × 4 × 4"),
            ("two equal axes", "4 × 10 × 10", "16  (D_4h)", "3", "4 × 4 × 5, 5 × 5 × 4"),
            ("three different", "4 × 7 × 10", "8  (D_2h)", "6", "4 × 5 × 6")]
    cols = (INK, REGULAR, TWO, DISTINCT)
    xs_c = (0.0, 0.2, 0.38, 0.56, 0.77)
    for i, (r, col) in enumerate(zip(rows, cols)):
        y = 0.86 - i * 0.2
        for x, t in zip(xs_c, r):
            cx.text(x, y, t, fontsize=9.5 if i else 9, color=col,
                    fontweight="bold" if i == 0 else "normal", transform=cx.transAxes)
    cx.text(0.0, 0.05, "With 4 to 6 positions per axis: 3 + 6 + 1 = 10 figures from 27 boxes. "
            "Every box with 4 or more positions\nis in exactly one family, and its quantum lies in "
            "δ(4)³ ≤ V < δ_∞³ (never erased).", fontsize=8.5, color=INK2, transform=cx.transAxes)
    cx.set_title("(c) how many deformations, and how they group (D37i)", loc="left", fontsize=11)

    fig.suptitle("The octahedron of the NRS quantum: the same excess δ = C_Nava − 1 on every axis",
                 x=0.01, ha="left", fontsize=13, color=INK)
    fig.text(0.01, 0.01, "Lean: dimQuantum (D25), deltaInf (D8), angleNRS_eq (D37b), "
             "volQuantum_certificate (D37e), quantum_never_erased, family_partition, card_orbit_* "
             "(D37i). Values from the closed form of C_Nava² (D19, D20).",
             fontsize=8.5, color=MUTED)
    fig.tight_layout(rect=(0, 0.03, 1, 0.92))
    fig.savefig(OUT / "nrs_quantum_octahedron.png", facecolor=SURFACE)
    plt.close(fig)


if __name__ == "__main__":
    fig_octahedron()

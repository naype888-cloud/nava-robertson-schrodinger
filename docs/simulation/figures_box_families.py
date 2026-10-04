"""Figures for D37i, the three families of boxes (numpy, matplotlib).

Writes to docs/figures/:
  d37i_box_families.png   (a) the boxes with 4 to 12 positions per axis, by family, and two orbits;
                          (b) the star of each box, a deformation of the regular 4 × 4 × 4;
                          (c) how many different figures each family has up to N positions
  d37i_families_table.png the three families: condition, symmetries, orbit, count, Lean

Proved in Lean (D37h, D37i): the partition into three families (family_partition), the
symmetries 48, 16, 8 (card_keepsAngles_family), the orbits 1, 3, 6 (card_orbit_*), orbit ×
stabilizer = 6, and the count at N = 10: 7 + 42 + 35 = 84 figures (count_ten). The general
counts m, m(m − 1), C(m, 3) with m = N − 3 are elementary combinatorics, checked in Lean at
N = 10. The angles θ_NRS(d) and the lengths σ_T, σ_P of the stars are evaluated numerically
from the matrices of D3 at ψ*; each star is drawn schematically, one axis per direction.

Run:  python3 docs/simulation/figures_box_families.py
"""

from itertools import permutations, product
from math import comb

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyBboxPatch, Polygon, Wedge

from figures_threshold_cone import GRID, INK, INK2, MUTED, OUT, SURFACE, ops

REGULAR, TWO, DISTINCT = "#2a78d6", "#eb6834", "#2f8f5b"
FAMILY_COLOR = {"regular": REGULAR, "two": TWO, "distinct": DISTINCT}
FAMILY_NAME = {"regular": "regular", "two": "two equal axes", "distinct": "three different axes"}
LIGHT = {"regular": "#e3eefb", "two": "#fde9e0", "distinct": "#e2f1e8"}


def family(b):
    k = len(set(b))
    return "regular" if k == 1 else ("two" if k == 2 else "distinct")


def psi_star(d):
    j = np.arange(d)
    v = (-1j) ** j * np.sin((j + 1) * np.pi / (d + 1))
    return v / np.linalg.norm(v)


def axis_stats(d):
    """σ_T, σ_P and the NRS angle (degrees) of the pair (T_d, P_d) at ψ*."""
    t, p = ops(d)
    z = psi_star(d)
    m = lambda a: np.vdot(z, a @ z).real
    x, y = t @ z - m(t) * z, p @ z - m(p) * z
    st, sp = np.linalg.norm(x), np.linalg.norm(y)
    ang = np.degrees(np.arccos(min(abs(np.vdot(x, y)) / (st * sp), 1.0)))
    return st, sp, ang


STATS = {}


def stats(d):
    if d not in STATS:
        STATS[d] = axis_stats(d)
    return STATS[d]


# ---------------------------------------------------------------------------------------------
# (a) the space of boxes
# ---------------------------------------------------------------------------------------------

def panel_space(ax, lo=4, hi=12):
    boxes = list(product(range(lo, hi + 1), repeat=3))
    for fam, size, alpha in [("distinct", 7, 0.22), ("two", 16, 0.55), ("regular", 60, 1.0)]:
        pts = np.array([b for b in boxes if family(b) == fam])
        ax.scatter(pts[:, 0], pts[:, 1], pts[:, 2], s=size, color=FAMILY_COLOR[fam],
                   alpha=alpha, depthshade=False, edgecolors="none",
                   label=f"{FAMILY_NAME[fam]} ({len(pts)})")
    diag = np.array([[lo] * 3, [hi] * 3])
    ax.plot(diag[:, 0], diag[:, 1], diag[:, 2], color=REGULAR, lw=1.6, alpha=0.8)
    # the chamber lo ≤ a ≤ b ≤ c ≤ hi: one box of every orbit
    v = np.array([[lo, lo, lo], [lo, lo, hi], [lo, hi, hi], [hi, hi, hi]])
    for i in range(4):
        for j in range(i + 1, 4):
            ax.plot(*zip(v[i], v[j]), color=INK2, lw=0.9, ls="--", alpha=0.7)
    for base, fam in [((4, 10, 10), "two"), ((4, 7, 10), "distinct")]:
        orbit = sorted({tuple(base[s] for s in sig) for sig in permutations(range(3))})
        order = [orbit[0]]
        rest = orbit[1:]
        while rest:  # a closed polygon through the orbit, nearest neighbour first
            nxt = min(rest, key=lambda q: np.linalg.norm(np.subtract(q, order[-1])))
            order.append(nxt)
            rest.remove(nxt)
        loop = np.array(order + [order[0]])
        ax.plot(loop[:, 0], loop[:, 1], loop[:, 2], color=FAMILY_COLOR[fam], lw=2.2)
        o = np.array(orbit)
        ax.scatter(o[:, 0], o[:, 1], o[:, 2], s=70, color=FAMILY_COLOR[fam], edgecolors=INK,
                   linewidths=1.1, depthshade=False, zorder=5)
    ax.text(12.3, 12.3, 12.6, "12 × 12 × 12", color=REGULAR, fontsize=9)
    ax.text(3.2, 3.2, 3.2, "4 × 4 × 4", color=REGULAR, fontsize=9)
    ax.set_xlabel("positions on x", color=INK2, labelpad=4)
    ax.set_ylabel("positions on y", color=INK2, labelpad=4)
    ax.set_zlabel("positions on z", color=INK2, labelpad=4)
    ticks = [4, 6, 8, 10, 12]
    ax.set_xticks(ticks)
    ax.set_yticks(ticks)
    ax.set_zticks(ticks)
    ax.tick_params(colors=MUTED, labelsize=8, pad=1)
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_facecolor(SURFACE)
        axis.pane.set_edgecolor(GRID)
        axis._axinfo["grid"]["color"] = GRID
    ax.view_init(elev=20, azim=-52)
    ax.set_box_aspect((1, 1, 1), zoom=0.92)
    ax.legend(loc="upper left", fontsize=9.5, bbox_to_anchor=(0.0, 0.97), markerscale=1.2)
    ax.set_title("(a) the boxes with 4 to 12 positions per axis, by family", loc="left", pad=2)
    for k, (txt, col) in enumerate([
            ("orbit of 4 × 10 × 10: 3 boxes, one figure (triangle)", TWO),
            ("orbit of 4 × 7 × 10: 6 boxes, one figure (hexagon)", DISTINCT),
            ("dashed: a ≤ b ≤ c, one box of every orbit", INK2)]):
        ax.text2D(0.035, 0.815 - 0.036 * k, txt, transform=ax.transAxes, fontsize=9.3,
                  color=col, bbox=dict(fc=SURFACE, ec="none", alpha=0.9, pad=1.2))


# ---------------------------------------------------------------------------------------------
# (b) the stars: deformations of the regular 4 × 4 × 4
# ---------------------------------------------------------------------------------------------

AXIS_DIR = {0: np.radians(210), 1: np.radians(330), 2: np.radians(90)}
AXIS_LABEL = {0: "x", 1: "y", 2: "z"}


def draw_star(ax, box, scale):
    fam = family(box)
    col = FAMILY_COLOR[fam]
    tips = []
    for i in range(3):
        st, sp, ang = stats(box[i])
        base = AXIS_DIR[i]
        half = np.radians(ang) / 2
        for length, rot in [(st, base + half), (sp, base - half)]:
            for sgn in (1, -1):
                tip = sgn * scale * length * np.array([np.cos(rot), np.sin(rot)])
                tips.append(tip)
                ax.plot([0, tip[0]], [0, tip[1]], color=col, lw=1.6 if sgn > 0 else 0.8,
                        alpha=1.0 if sgn > 0 else 0.45, solid_capstyle="round")
        r = 0.8 * scale * min(st, sp)
        ax.add_patch(Wedge((0, 0), r, np.degrees(base - half), np.degrees(base + half),
                           fc=col, ec="none", alpha=0.55, zorder=2))
        lab = 0.98 * scale * max(st, sp) * np.array([np.cos(base), np.sin(base)])
        off = {0: (-0.16, -0.05), 1: (0.16, -0.05), 2: (0.0, 0.1)}[i]
        ax.text(lab[0] + off[0], lab[1] + off[1],
                f"{AXIS_LABEL[i]}: {box[i]} positions\n{ang:.2f}°", ha="center", va="center",
                fontsize=8.5, color=INK2)
    tips = np.array(tips)
    order = np.argsort(np.arctan2(tips[:, 1], tips[:, 0]))
    ax.add_patch(Polygon(tips[order], closed=True, fc=LIGHT[fam], ec=col, lw=1.0, alpha=0.9,
                         zorder=0))
    ax.set_aspect("equal")
    ax.set_xlim(-1.35, 1.35)
    ax.set_ylim(-1.2, 1.35)
    ax.set_axis_off()
    ax.set_title(" × ".join(map(str, box)), color=col, fontsize=12.5, fontweight="bold", pad=1)
    ax.text(0, -1.18, FAMILY_NAME[fam], ha="center", color=col, fontsize=9.5)


# ---------------------------------------------------------------------------------------------
# (c) how many figures up to N
# ---------------------------------------------------------------------------------------------

def counts(n_max):
    m = n_max - 3
    return m, m * (m - 1), comb(m, 3)


def panel_counts(ax):
    ns = np.arange(4, 41)
    reg, two, dist = np.array([counts(n) for n in ns]).T
    total = reg + two + dist
    ax.plot(ns, total, color=INK, lw=2.2, label="all figures  C(m + 2, 3)")
    ax.plot(ns, dist, color=DISTINCT, lw=2, label="three different axes  C(m, 3)")
    ax.plot(ns, two, color=TWO, lw=2, label="two equal axes  m(m − 1)")
    ax.plot(ns, reg, color=REGULAR, lw=2, label="regular  m")
    for v, c in [(84, INK), (35, DISTINCT), (42, TWO), (7, REGULAR)]:
        ax.scatter([10], [v], s=46, color=c, edgecolors=INK, linewidths=0.8, zorder=5)
    ax.annotate("N = 10 (Lean, count_ten):\n7 + 42 + 35 = 84 figures\nfrom 343 boxes", (10, 84),
                xytext=(4.8, 1500), fontsize=9.5, color=INK2,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.9))
    ax.set_yscale("log")
    ax.set_xlim(4, 40)
    ax.set_ylim(0.8, 2e4)
    ax.set_xlabel("N: at most N positions on each axis (m = N − 3 choices per axis)")
    ax.set_ylabel("different figures (orbits)")
    ax.legend(loc="lower right", fontsize=9)
    ax.set_title("(c) how many different figures, up to N positions per axis", loc="left")


def fig_families():
    fig = plt.figure(figsize=(19, 12.6), dpi=150)
    gs = fig.add_gridspec(2, 1, height_ratios=[1.25, 0.85], hspace=0.12)
    top = gs[0].subgridspec(1, 2, width_ratios=[1.2, 1], wspace=0.12)
    ax3 = fig.add_subplot(top[0, 0], projection="3d")
    panel_space(ax3)
    axc = fig.add_subplot(top[0, 1])
    panel_counts(axc)
    boxes = [(4, 4, 4), (10, 10, 10), (4, 10, 10), (4, 7, 10)]
    scale = 1.0 / max(max(stats(d)[0], stats(d)[1]) for b in boxes for d in b)
    bottom = gs[1].subgridspec(1, 4, wspace=0.05)
    star_axes = [fig.add_subplot(bottom[0, k]) for k in range(4)]
    for ax, b in zip(star_axes, boxes):
        draw_star(ax, b, scale)
    star_axes[0].text(-1.35, 1.75, "(b) the star of each box: a deformation of the regular "
                      "4 × 4 × 4", fontsize=13, color=INK, ha="left")
    fig.suptitle("D37i — the three families of boxes", x=0.01, ha="left", fontsize=15,
                 color=INK, y=0.93)
    fig.text(0.01, 0.075, "Stars: the fluctuation vectors of T (upper ray) and P (lower ray) "
             "of each axis at ψ*, true angle θ_NRS and true lengths σ_T, σ_P, drawn one axis per "
             "direction; faint rays are their opposites. Every axis with 4 or more positions opens; "
             "equal axes open equally.", fontsize=9, color=MUTED)
    fig.savefig(OUT / "d37i_box_families.png", bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------------------------------------
# the table
# ---------------------------------------------------------------------------------------------

def fig_table():
    rows = [
        ("regular", "dx = dy = dz", "4 × 4 × 4\n10 × 10 × 10", "one angle,\nthe same on all axes",
         "48", r"$O_h$", "6 of 6", "1", "m", "7"),
        ("two", "exactly two\naxes equal", "4 × 10 × 10\n100 × 100 × 4", "two angles:\n"
         "the equal axes share one", "16", r"$D_{4h}$", "2 of 6", "3", "m(m − 1)", "42"),
        ("distinct", "dx, dy, dz\nall different", "4 × 7 × 10\n67 × 25 × 1600",
         "three different\nangles", "8", r"$D_{2h}$", "1 of 6", "6", "C(m, 3)", "35"),
    ]
    heads = ["family", "condition", "examples", "NRS angles at Ψ*", "symmetries", "group",
             "axis orders\nkept", "orbit\n(same figure)", "figures up to N\n(m = N − 3)*",
             "N = 10"]
    widths = [1.9, 1.45, 1.7, 1.95, 1.1, 0.8, 1.05, 1.1, 1.45, 0.75]
    lean = ["IsRegular", "IsTwoEqual", "IsDistinct"]
    lean_stab = ["card_axisStab_regular", "card_axisStab_twoEqual", "card_axisStab_distinct"]
    lean_orb = ["card_orbit_regular", "card_orbit_twoEqual", "card_orbit_distinct"]
    total_w = sum(widths)
    fig, ax = plt.subplots(figsize=(19, 7.4), dpi=150)
    ax.set_xlim(0, total_w)
    ax.set_ylim(0, 7.2)
    ax.set_axis_off()
    xs = np.concatenate([[0], np.cumsum(widths)])
    top = 6.35
    ax.add_patch(FancyBboxPatch((0.02, top), total_w - 0.04, 0.78,
                                boxstyle="round,pad=0,rounding_size=0.08", fc="#1d1d1b",
                                ec="none"))
    for k, h in enumerate(heads):
        ax.text((xs[k] + xs[k + 1]) / 2, top + 0.39, h, ha="center", va="center",
                color="white", fontsize=10.5, fontweight="bold", linespacing=1.05)
    row_h = 1.72
    for r, row in enumerate(rows):
        fam = row[0]
        y0 = top - (r + 1) * row_h - 0.06
        ax.add_patch(FancyBboxPatch((0.02, y0), total_w - 0.04, row_h - 0.1,
                                    boxstyle="round,pad=0,rounding_size=0.08", fc=LIGHT[fam],
                                    ec="none"))
        ax.add_patch(FancyBboxPatch((0.02, y0), 0.09, row_h - 0.1,
                                    boxstyle="round,pad=0,rounding_size=0.04",
                                    fc=FAMILY_COLOR[fam], ec="none"))
        yc = y0 + (row_h - 0.1) / 2
        cells = [FAMILY_NAME[fam]] + list(row[1:])
        for k, text in enumerate(cells):
            xc = (xs[k] + xs[k + 1]) / 2
            if k == 0:
                ax.text(xc + 0.05, yc + 0.18, text, ha="center", va="center", fontsize=11.5,
                        fontweight="bold", color=FAMILY_COLOR[fam])
                ax.text(xc + 0.05, yc - 0.32, lean[r], ha="center", va="center", fontsize=8.5,
                        color=INK2, family="monospace")
            elif k in (4, 7):
                ax.text(xc, yc + 0.12, text, ha="center", va="center", fontsize=22,
                        fontweight="bold", color=FAMILY_COLOR[fam])
                sub_txt = lean_stab[r] if k == 4 else lean_orb[r]
                ax.text(xc, yc - 0.45, sub_txt, ha="center", va="center", fontsize=6.6,
                        color=INK2, family="monospace")
            elif k == 5:
                ax.text(xc, yc, text, ha="center", va="center", fontsize=15, color=INK)
            elif k == 9:
                ax.text(xc, yc, text, ha="center", va="center", fontsize=15, fontweight="bold",
                        color=INK)
            else:
                ax.text(xc, yc, text, ha="center", va="center", fontsize=10.5, color=INK,
                        linespacing=1.25)
    yb = top - 3 * row_h - 0.55
    ax.text(0.1, yb, "Every box with 4 or more positions per axis is in exactly one family "
            "(family_partition). Orbit × axis orders kept = 3! = 6 (card_orbit_mul_card_stab); "
            "symmetries = 8 reflections × axis orders kept (card_keepsAngles_family).",
            fontsize=10, color=INK2)
    ax.text(0.1, yb - 0.38, "N = 10: 7 regular + 126 with two equal axes + 210 with three "
            "different = 343 boxes, that is 7 + 42 + 35 = 84 different figures (count_ten). "
            "Proved in Lean 4 (D37h, D37i): families, symmetries, orbits and the count at N = 10;",
            fontsize=10, color=INK2)
    ax.text(0.1, yb - 0.76, "axioms propext, Classical.choice, Quot.sound.   * The formulas in m "
            "are elementary combinatorics, checked in Lean at N = 10 only.", fontsize=10,
            color=INK2)
    ax.set_title("The three families of boxes: deformations of the regular 4 × 4 × 4",
                 loc="left", fontsize=15, color=INK, pad=4)
    fig.savefig(OUT / "d37i_families_table.png", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    fig_families()
    fig_table()
    for d in (4, 7, 10):
        st, sp, ang = stats(d)
        print(f"d = {d}: σ_T = {st:.4f}, σ_P = {sp:.4f}, θ_NRS = {ang:.3f}°")
    print("wrote", OUT / "d37i_box_families.png", OUT / "d37i_families_table.png")

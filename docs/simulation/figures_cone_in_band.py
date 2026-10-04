"""Figure for D46: the cone lies in every band (numpy, scipy, matplotlib).

Writes docs/figures/d46_cone_in_band.png.

Left: the band Ϙ(d) = (v*(d), 1] for each d. It narrows as d grows, but the cone |v| = 1 stays
inside for every d ≥ 4 (Lean, D46): every unit state at the cone speed carries a
Robertson–Schrödinger surplus. At d = 2, 3, ψ* saturates at the cone and the band is empty.
Right: the width ϙ(d) = 1 − v*(d) on a log scale. The cone needs only ϙ(d) > 0.

Exact (Lean): ϙ(2) = ϙ(3) = 0, ϙ(4) = (7 − 3√5)/4, ϙ(d) > 0 for d ≥ 4. The values of v*(d)
for d ≥ 5 are numerical (D44 figures).

Run:  python3 docs/simulation/figures_cone_in_band.py
"""

import os
from multiprocessing import Pool

import matplotlib.pyplot as plt
import numpy as np

from figures_threshold_cone import BLUE, INK2, ORANGE, OUT, SURFACE, VSTAR4
from figures_velocity_band import vstar_imag


def fig_cone_in_band():
    ds = np.array(list(range(5, 61)) + list(range(61, 121, 3)) + list(range(125, 302, 5)))
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    with Pool(os.cpu_count()) as pool:
        vs = np.array(pool.map(vstar_imag, ds, chunksize=1))
    koppa = 1 - vs

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(11.6, 4.8), dpi=150,
                                 gridspec_kw={"width_ratios": [1.1, 1]})

    # left: the bands
    near = ds <= 30
    ax.vlines(ds[near], vs[near], 1, color=BLUE, lw=5, alpha=0.35)
    ax.vlines([4], [VSTAR4], 1, color=ORANGE, lw=5, alpha=0.6)
    ax.plot(ds[near], vs[near], "o", ms=5, color=BLUE, mec=SURFACE, mew=1.2,
            label="v*(d), numerical")
    ax.plot([4], [VSTAR4], "o", ms=8, color=ORANGE, mec=SURFACE, mew=1.5,
            label="v*(4) = 3(√5 − 1)/4, exact (D43)")
    ax.plot([2, 3], [1, 1], "o", ms=8, color=INK2, mec=SURFACE, mew=1.5, zorder=5,
            label="d = 2, 3: ψ* saturates at the cone, no band")
    ax.axhline(1, color=INK2, lw=1.4)
    ax.text(30.5, 1.003, "cone |v| = 1: inside Ϙ(d) for every d ≥ 4 (Lean, D46)",
            color=INK2, fontsize=9.5, ha="right", va="bottom")
    ax.set_xlim(1, 31)
    ax.set_ylim(0.918, 1.012)
    ax.set_axisbelow(True)
    ax.set_xlabel("positions per axis  d")
    ax.set_ylabel("speed  |v|  (units of the cone)")
    ax.legend(loc="lower right", fontsize=9)
    ax.set_title("The band Ϙ(d) = (v*(d), 1] and the cone", loc="left", fontsize=11.5)

    # right: the width, log scale
    bx.plot(ds, koppa, "o", ms=4, color=BLUE, mec=SURFACE, mew=0.8, label="ϙ(d), numerical")
    bx.plot([4], [1 - VSTAR4], "o", ms=8, color=ORANGE, mec=SURFACE, mew=1.5,
            label="ϙ(4) = (7 − 3√5)/4, exact")
    bx.text(0.03, 0.04, "the cone only needs ϙ(d) > 0:\nevery d ≥ 4 (Lean, D44/D46)",
            color=INK2, fontsize=9.5, ha="left", transform=bx.transAxes)
    bx.set_xscale("log")
    bx.set_yscale("log")
    bx.set_xticks([4, 10, 30, 100, 300])
    bx.set_xticklabels(["4", "10", "30", "100", "300"])
    bx.set_axisbelow(True)
    bx.set_xlabel("positions per axis  d  (log scale)")
    bx.set_ylabel("width  ϙ(d) = 1 − v*(d)")
    bx.legend(loc="upper right", fontsize=9)
    bx.set_title("Its width: narrower, never zero", loc="left", fontsize=11.5)

    fig.suptitle("D46: everything transported at the cone speed carries a forced defect, "
                 "for every d ≥ 4", x=0.01, ha="left", fontsize=12.5)
    fig.tight_layout()
    fig.savefig(OUT / "d46_cone_in_band.png")
    plt.close(fig)


if __name__ == "__main__":
    fig_cone_in_band()

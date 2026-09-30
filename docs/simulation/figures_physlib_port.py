"""Figures for the Physlib port of NRS and NRS³ (numpy, scipy, matplotlib).

Writes to docs/figures/:
  physlib_port_ladder.png          the pull requests of the port, their status and dependencies
  physlib_band_time_reversal.png   why the velocity band is open from four sites on (PR 20)

The port states NRS on physlib's open tight binding chain: Hamiltonian H (hopping t), position X
(spacing a), current J = i(HX − XH). The ladder records the status on 2026-09-30. In the second
figure the currents, the phases and the defects are exact closed forms evaluated numerically; the
thresholds v*(N) for N ≥ 5 are numerical (D44 figures), v*(4) = 3(√5 − 1)/4 is exact (D43).

Run:  python3 docs/simulation/figures_physlib_port.py
"""

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
from matplotlib.path import Path

from figures_threshold_cone import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, SURFACE, VSTAR4
from figures_velocity_band import vstar_imag

GREEN, LIGHT, PALE = "#2f8f5b", "#e8f1fc", "#f3f2ef"

# ---------------------------------------------------------------------------------------------
# 1. The ladder of pull requests
# ---------------------------------------------------------------------------------------------

# name: (column, row, label, status)   status: merged, open, local, planned
# columns 0-1: merged; column 2 + k: submission wave k (docs/PHYSLIB_PORT.md)
TOP, MID, LOW, BOT, LANE = 5.6, 4.1, 2.7, 1.3, 4.85
NODES = {
    "1649": (0, 5.6, "#1649\nequality in\nuncertainty", "merged"),
    "1650": (0, 4.35, "#1650\nnormalized\nvariance bounds", "merged"),
    "1660": (0, 3.1, "#1660\nvector states:\nvariance, defect", "merged"),
    "1676": (0, 1.85, "#1676\nRS for\ndensity states", "merged"),
    "1689": (1, TOP, "#1689\nopen tight\nbinding chain", "merged"),
    "1690": (1, MID, "#1690\nenergy–position\nuncertainty", "merged"),
    "1696": (2, TOP, "#1696\ncurrent\nJ = i[H, X]", "open"),
    "1695": (2, LOW, "#1695\nSelfAdjoint-\nDecompose on H[d]", "open"),
    "1699": (2, BOT, "#1699\noperators on one\ncoordinate", "open"),
    "8": (3, TOP, "8\ncurrent\neigenstates", "local"),
    "9": (3, MID, "9\nuncertainty on\nits own space", "local"),
    "14": (3, BOT, "14\nproduct\nstates", "local"),
    "10": (4, TOP, "10\nmaximal\ncurrent state", "local"),
    "16": (4, MID, "16\nMandelstam–Tamm,\nCramér–Rao", "local"),
    "11": (5, TOP, "11\nsaturation\niff N = 2, 3", "local"),
    "18": (5, MID, "18\nspeed limit\n|<J>| ≤ maxCurrent", "local"),
    "12": (6, TOP, "12\nNRS: C_Nava ≥ 1,\n= 1 iff N = 2, 3", "local"),
    "19": (6, MID, "19\nvelocity band Ϙ,\nforced defect", "local"),
    "15": (7, TOP, "15\nNRS³: the cube,\naxis by axis", "local"),
    "20": (7, MID, "20\nϘ open for N ≥ 4\n(time reversal)", "local"),
    "21": (7, LOW, "21\nVar H, Var X,\nC_Nava² closed", "local"),
    "17": (8, LANE, "17\nMT/CR ratio\n= 1/C_Nava²", "local"),
    "22": (8, LOW, "22\nlimit\nC_Nava → C∞", "local"),
    "23": (9, LOW, "23\nC_Nava strictly\nincreasing, < C∞", "local"),
}

EDGES = [
    ("1649", "1690"), ("1650", "1690"), ("1660", "1690"), ("1676", "1690"), ("1689", "1690"),
    ("1689", "1696"), ("1690", "9"), ("1695", "9"), ("1695", "14"), ("1699", "14"),
    ("1696", "8"), ("1696", "16"), ("9", "16"), ("8", "10"), ("9", "10"), ("10", "11"),
    ("11", "12"), ("12", "15"), ("14", "15"), ("15", "17"), ("16", "17"), ("18", "17"),
    ("10", "18"), ("16", "18"), ("11", "19"), ("18", "19"), ("19", "20"), ("1699", "20"),
    ("12", "21"), ("21", "22"), ("22", "23"),
]

STYLE = {
    "merged": dict(fc=BLUE, ec=BLUE, tc=SURFACE, ls="-"),
    "open": dict(fc=LIGHT, ec=BLUE, tc=INK, ls="-"),
    "local": dict(fc=SURFACE, ec=INK2, tc=INK, ls="-"),
    "planned": dict(fc=PALE, ec=MUTED, tc=INK2, ls="--"),
}

W, H, DX = 1.34, 0.98, 1.78
WAVES = ["in review", "", "", "", "NRS", "NRS³", "", "seal"]


def centre(name):
    c, r, _, _ = NODES[name]
    return c * DX, r


def left(name, dy=0.0):
    x, y = centre(name)
    return x - W / 2, y + dy


def right(name, dy=0.0):
    x, y = centre(name)
    return x + W / 2, y + dy


def route(a, b):
    """Waypoints of the edge a → b; long edges run in the free lanes between the rows."""
    g = lambda c: c * DX - W / 2 - 0.13  # the gap just left of column c
    special = {
        ("1696", "16"): [right("1696", -0.25), (g(3), LANE), (g(4), LANE), left("16", 0.2)],
        ("16", "17"): [right("16", 0.2), (4 * DX + W / 2 + 0.13, LANE), left("17")],
        ("18", "17"): [right("18", 0.2), (5 * DX + W / 2 + 0.13, LANE)],
        ("14", "15"): [right("14"), (g(7), BOT), (g(7), TOP - 0.25), left("15", -0.25)],
        ("1699", "20"): [(2 * DX, BOT - H / 2), (2 * DX, 0.5), (g(7) - 0.16, 0.5),
                         (g(7) - 0.16, MID - 0.2), left("20", -0.2)],
        ("1689", "1690"): [(DX, TOP - H / 2), (DX, MID + H / 2)],
    }
    return special.get((a, b), [right(a), left(b)])


def fig_ladder():
    fig, ax = plt.subplots(figsize=(18.5, 7.8), dpi=150)
    ax.set_axis_off()
    ax.add_patch(plt.Rectangle((-DX / 2, 0.2), 2 * DX, 6.35, fc=LIGHT, ec="none", alpha=0.45,
                               zorder=0))
    ax.text(DX / 2, 6.7, "merged\nalgebraic RS and the open chain", ha="center", va="bottom",
            fontsize=9.5, color=INK2)
    for k in range(8):
        x = (2 + k) * DX
        ax.add_patch(plt.Rectangle((x - DX / 2, 0.2), DX, 6.35, fc=PALE if k % 2 else SURFACE,
                                   ec="none", zorder=0))
        ax.text(x, 6.7, f"wave {k}" + (f"\n{WAVES[k]}" if WAVES[k] else "\n"), ha="center",
                va="bottom", fontsize=9.5, color=INK2, fontweight="bold" if k == 0 else None)
    for a, b in EDGES:
        pts = route(a, b)
        arrow = (a, b) != ("18", "17")  # joins the lane of 16 → 17, which carries the head
        codes = [Path.MOVETO] + [Path.LINETO] * (len(pts) - 1)
        ax.add_patch(FancyArrowPatch(path=Path(pts, codes), lw=0.9, color=MUTED, alpha=0.85,
                                     arrowstyle="-|>" if arrow else "-", mutation_scale=9,
                                     zorder=1, joinstyle="round"))
    for name, (c, r, label, status) in NODES.items():
        s = STYLE[status]
        ax.add_patch(FancyBboxPatch(
            (c * DX - W / 2, r - H / 2), W, H, boxstyle="round,pad=0.02,rounding_size=0.08",
            fc=s["fc"], ec=s["ec"], lw=1.3, ls=s["ls"], zorder=2))
        head, *rest = label.split("\n")
        ax.text(c * DX, r + 0.27, head, ha="center", va="center", fontsize=10.5,
                fontweight="bold", color=s["tc"], zorder=3)
        ax.text(c * DX, r - 0.1, "\n".join(rest), ha="center", va="center", fontsize=7.6,
                color=s["tc"], linespacing=1.15, zorder=3)
    for x, status, t in [(0.0, "merged", "merged"), (2.4, "open", "open, in review"),
                         (5.2, "local", "ready, not yet submitted")]:
        s = STYLE[status]
        ax.add_patch(FancyBboxPatch((x, -0.45), 0.34, 0.26, boxstyle="round,pad=0.01,"
                     "rounding_size=0.05", fc=s["fc"], ec=s["ec"], ls=s["ls"], lw=1.2))
        ax.text(x + 0.45, -0.32, t, va="center", fontsize=9.5, color=INK2)
    ax.text(9 * DX + DX / 2, -0.32, "at most three open at a time; each wave goes up when the "
            "previous one is merged", ha="right", va="center", fontsize=9.5, color=INK2)
    ax.set_xlim(-DX / 2 - 0.1, 9 * DX + DX / 2 + 0.1)
    ax.set_ylim(-0.6, 7.35)
    ax.set_title("The Physlib port of NRS and NRS³: pull requests, dependencies and submission "
                 "waves (30 Sep 2026)", loc="left", fontsize=13.5, color=INK)
    fig.text(0.012, 0.012, "All on physlib's open tight binding chain (PhyslibAlpha): H, X and "
             "the current J = i(HX − XH). Round C (21–23; D8, D9, D19, D20) is the seal: C_Nava "
             "strictly increasing, below C∞.", fontsize=8.5, color=MUTED)
    fig.savefig(OUT / "physlib_port_ladder.png", bbox_inches="tight", facecolor=SURFACE)
    plt.close(fig)


# ---------------------------------------------------------------------------------------------
# 2. The band is open from four sites on
# ---------------------------------------------------------------------------------------------

def chain(n, a=1.0, t=1.0):
    """H (E0 = 0), X and J = i(HX − XH) of the open chain with n sites."""
    hop = np.diag(np.ones(n - 1), 1)
    h = -t * (hop + hop.T)
    x = np.diag(a * np.arange(n))
    return h.astype(complex), x.astype(complex), 1j * (h @ x - x @ h)


def eigenstate(n, k):
    """ψ_k = Σ iʲ sin((j + 1) k π / (n + 1)) |j⟩, normalized."""
    j = np.arange(n)
    v = (1j ** j) * np.sin((j + 1) * k * np.pi / (n + 1))
    return v / np.linalg.norm(v)


def defect(n, psi):
    """Centered Gram defect of H and X, over the squared bracket ⟨J⟩²/4: C_Nava² − 1."""
    h, x, jc = chain(n)
    m = lambda op: (psi.conj() @ op @ psi).real
    u, w = h @ psi - m(h) * psi, x @ psi - m(x) * psi
    g = np.vdot(u, u).real * np.vdot(w, w).real - abs(np.vdot(u, w)) ** 2
    return g / (m(jc) / 2) ** 2


def fig_band():
    fig, axs = plt.subplots(1, 4, figsize=(17, 4.6), dpi=150,
                            gridspec_kw={"width_ratios": [1.05, 1.0, 1.0, 1.05]})
    ax, bx, cx, dx = axs

    # (a) currents 2at cos(kπ/(N+1)): the extremes are simple
    for n in range(2, 13):
        ks = np.arange(1, n + 1)
        cur = 2 * np.cos(ks * np.pi / (n + 1))
        ax.plot(np.full(n - 2, n), cur[1:-1], "_", ms=11, mew=1.6, color=MUTED)
        ax.plot([n], [cur[0]], "o", ms=6, color=ORANGE, mec=SURFACE, mew=1)
        ax.plot([n], [cur[-1]], "o", ms=6, color=BLUE, mec=SURFACE, mew=1)
    nn = np.linspace(2, 12, 200)
    ax.plot(nn, 2 * np.cos(np.pi / (nn + 1)), color=ORANGE, lw=1, alpha=0.5)
    ax.plot(nn, -2 * np.cos(np.pi / (nn + 1)), color=BLUE, lw=1, alpha=0.5)
    ax.axhline(0, color=GRID, lw=1)
    ax.set_xlabel("sites  N")
    ax.set_ylabel("current  (units of a t)")
    ax.set_title("(a) Currents 2at cos(kπ/(N+1)):\nthe extremes ±maxCurrent are simple",
                 loc="left", fontsize=11)
    ax.text(12.3, 1.93, "ψ₁", color=ORANGE, fontsize=11, va="center")
    ax.text(12.3, -1.93, "ψ_N", color=BLUE, fontsize=11, va="center")
    ax.set_xlim(1.5, 13)

    # (b) time reversal: Θψ₁ = ψ_N, conjugate phases
    n = 6
    p1, pn = eigenstate(n, 1), eigenstate(n, n)
    j = np.arange(n)
    for y0, v, col in [(1.0, p1, ORANGE), (-1.0, pn, BLUE)]:
        bx.quiver(j, np.full(n, y0), v.real, v.imag, angles="xy", scale_units="xy",
                  scale=0.62, color=col, width=0.013, pivot="mid")
        bx.plot(j, np.full(n, y0), "o", ms=3, color=col, alpha=0.5)
    bx.text(-0.7, 1.0, "ψ₁", color=ORANGE, fontsize=12, ha="right", va="center")
    bx.text(-0.7, -1.0, "Θψ₁\n= ψ_N", color=BLUE, fontsize=11, ha="right", va="center")
    bx.set_aspect("equal")
    bx.set_xlim(-2.1, n - 0.3)
    bx.set_ylim(-1.9, 1.9)
    bx.set_yticks([])
    bx.set_xticks(j)
    bx.set_xlabel("site  j   (N = 6)")
    bx.set_title("(b) Time reversal conjugates the\nphases iʲ → (−i)ʲ and reverses J",
                 loc="left", fontsize=11)
    bx.grid(False)

    # (c) the defect at both extremes
    ns = np.arange(2, 21)
    d1 = np.array([defect(k, eigenstate(k, 1)) for k in ns])
    dn = np.array([defect(k, eigenstate(k, k)) for k in ns])
    cinf = np.pi ** 2 / 3 - 2 - 1
    cx.axhline(cinf, color=MUTED, lw=1, ls="--")
    cx.text(20.4, cinf, "C∞² − 1", color=MUTED, fontsize=9, va="bottom", ha="right")
    cx.plot(ns, d1, "o-", ms=6, lw=1.3, color=ORANGE, mec=SURFACE, mew=1, label="at ψ₁")
    cx.plot(ns, dn, "x", ms=7, mew=1.6, color=BLUE, label="at ψ_N = Θψ₁")
    cx.plot([2, 3], d1[:2], "o", ms=9, color=INK2, mec=SURFACE, mew=1.5, zorder=5)
    cx.set_xlabel("sites  N")
    cx.set_ylabel("defect / ⟨⁅H, X⁆⟩²  =  C_Nava² − 1")
    cx.set_title("(c) Same defect at both extremes:\nzero only at N = 2, 3 (PR 11)",
                 loc="left", fontsize=11)
    cx.legend(loc="lower right", fontsize=9)

    # (d) the threshold v* lies strictly below the cone from N = 4
    ds = np.arange(5, 31)
    vs = np.array([vstar_imag(d) for d in ds])
    dx.vlines(ds, vs, 1, color=BLUE, lw=4, alpha=0.3)
    dx.vlines([4], [VSTAR4], 1, color=ORANGE, lw=4, alpha=0.55)
    dx.plot(ds, vs, "o", ms=5, color=BLUE, mec=SURFACE, mew=1, label="v*(N), numerical")
    dx.plot([4], [VSTAR4], "o", ms=8, color=ORANGE, mec=SURFACE, mew=1.3,
            label="v*(4) = 3(√5 − 1)/4 (D43)")
    dx.plot([2, 3], [1, 1], "o", ms=8, color=INK2, mec=SURFACE, mew=1.3,
            label="N = 2, 3: Ϙ = ∅ (PR 19)")
    dx.axhline(1, color=INK2, lw=1.3)
    dx.set_ylim(0.915, 1.012)
    dx.set_xlim(1, 31)
    dx.set_xlabel("sites  N")
    dx.set_ylabel("speed / maxCurrent")
    dx.set_title("(d) v* is attained, so v* < maxCurrent:\nϘ = (v*, maxCurrent] ≠ ∅ for N ≥ 4",
                 loc="left", fontsize=11)
    dx.legend(loc="lower right", fontsize=8.5)

    fig.suptitle("PR 20: the velocity band is open from four sites on — time reversal, simple "
                 "extremes and compactness, without an explicit width", x=0.01, ha="left",
                 fontsize=13, color=INK)
    fig.text(0.01, -0.01, "Lean (PR 18–20): |⟨J⟩| ≤ maxCurrent in every state; a unit vector at "
             "the speed limit is a phase times ψ₁ or ψ_N; Θ keeps the defect; v* is attained. "
             "Plotted values are the closed forms; v*(N ≥ 5) numerical.",
             fontsize=8.5, color=MUTED)
    fig.tight_layout()
    fig.savefig(OUT / "physlib_band_time_reversal.png", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    fig_ladder()
    fig_band()
    print("wrote", OUT / "physlib_port_ladder.png", OUT / "physlib_band_time_reversal.png")

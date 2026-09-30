"""Figures for the Solvay certificates: Poincaré 1911/1912 and Dirac 1928 (numpy, matplotlib).

Writes:
  poincare1911_planck_vs_rj.png      Planck against the classical oscillator
  poincare1912_discreteness.png      Planck's law forces the levels: smeared levels fail
  dirac1928_minimal_dimension.png    16 independent monomials need n² ≥ 16; the 4 × 4 matrices

Exact (Lean): ε/(e^{βε} − 1) < 1/β for every β, ε > 0 (Poincare1911); a weight with Planck's
mean energy is c · ∑ δ_{nε} (Poincare1912.planck_forces_levels); 4 is the least dimension of
the gamma matrices (Dirac1928.isLeast_dim). The smeared-level curves use the exact Gaussian
formula U = U_Planck − βσ²; they illustrate the theorem and are not part of the proofs.

Run:  python3 docs/simulation/figures_solvay.py
"""

import matplotlib.pyplot as plt
import numpy as np

from figures_threshold_cone import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, SURFACE


def planck(x):
    return x / np.expm1(x)


def fig_poincare1911():
    x = np.linspace(1e-3, 8, 800)
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(11.6, 4.6), dpi=150)

    ax.axhline(1, color=INK2, lw=1.6, label="classical (continuous):  1/β")
    ax.plot(x, planck(x), color=BLUE, lw=2.2, label="Planck (quantized):  ε/(e^(βε) − 1)")
    ax.fill_between(x, planck(x), 1, color=BLUE, alpha=0.10)
    ax.text(3.6, 0.45, "strict gap for every βε > 0\n(Lean: planck_lt_rayleigh_jeans)",
            color=INK2, fontsize=9.5)
    ax.set_xlabel("βε  =  hν / kT")
    ax.set_ylabel("mean energy  ×  β")
    ax.set_ylim(0, 1.12)
    ax.legend(loc="center right", fontsize=9, bbox_to_anchor=(1.0, 0.75))
    ax.set_title("Mean energy of one oscillator", loc="left", fontsize=11.5)

    bx.plot(x, x ** 2, color=INK2, lw=1.6, label="Rayleigh–Jeans  ∝ x²")
    bx.plot(x, x ** 3 / np.expm1(x), color=BLUE, lw=2.2, label="Planck  ∝ x³/(eˣ − 1)")
    xm = 2.8214393721220787
    bx.plot([xm], [xm ** 3 / np.expm1(xm)], "o", color=ORANGE, mec=SURFACE, mew=1.3, ms=7)
    bx.text(xm + 0.2, xm ** 3 / np.expm1(xm) + 0.12, "Wien peak  x ≈ 2.821", color=INK2,
            fontsize=9.5)
    bx.set_ylim(0, 3.2)
    bx.set_xlabel("x  =  hν / kT")
    bx.set_ylabel("spectral energy density (arb. units)")
    bx.legend(loc="upper right", fontsize=9)
    bx.set_title("The ultraviolet catastrophe is avoided", loc="left", fontsize=11.5)

    fig.suptitle("Poincaré 1911 — the continuum cannot give Planck's law", x=0.01, ha="left",
                 fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "poincare1911_planck_vs_rj.png", facecolor=SURFACE)
    plt.close(fig)


def smeared_mean(beta, sigma):
    """Mean energy (units of ε) of the levels nε smeared by Gaussians of width σ on ℝ.

    The smearing multiplies Z by e^{β²σ²/2}, so U = U_Planck − βσ² exactly.
    """
    return 1 / np.expm1(beta) - beta * sigma ** 2


def fig_poincare1912():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(11.6, 4.6), dpi=150,
                                 gridspec_kw={"width_ratios": [1, 1.15]})

    e = np.linspace(0, 5.5, 2000)
    sigmas = [(0.25, ORANGE), (0.08, MUTED)]
    for s, c in sigmas:
        w = sum(np.exp(-0.5 * ((e - n) / s) ** 2) / (s * np.sqrt(2 * np.pi)) for n in range(7))
        ax.plot(e, w * 0.25, color=c, lw=1.5, label=f"smeared levels, σ = {s}ε")
    ns = np.arange(6)
    ax.vlines(ns, 0, 1, color=BLUE, lw=2.6)
    ax.plot(ns, np.ones_like(ns), "^", color=BLUE, ms=8, label="the only solution: c · ∑ δ(E − nε)")
    ax.axhline(0.18, color=INK2, lw=1.2, ls="--", label="continuous density (classical)")
    ax.set_xlabel("energy  E / ε")
    ax.set_ylabel("weight  w(E)  (arb. units)")
    ax.set_ylim(0, 1.55)
    ax.legend(loc="upper center", fontsize=8.8, bbox_to_anchor=(0.5, 1.0), ncol=2,
              framealpha=0.95)
    ax.set_xlim(-0.3, 5.5)
    ax.set_title("Candidate densities of states", loc="left", fontsize=11.5)

    betas = np.geomspace(0.05, 6, 300)
    for s, c in sigmas + [(0.03, BLUE)]:
        rel = np.abs(smeared_mean(betas, s) * np.expm1(betas) - 1)
        bx.plot(betas, rel, color=c, lw=1.8, label=f"σ = {s} ε")
    bx.plot(betas, np.abs(1 / planck(betas) - 1), color=INK2, lw=1.4, ls="--",
            label="continuous (classical)")
    bx.set_xscale("log")
    bx.set_yscale("log")
    bx.set_ylim(1e-6, 1e2)
    bx.set_xlabel("βε")
    bx.set_ylabel("|U / U_Planck − 1|")
    bx.text(0.36, 0.04, "smeared levels:  U = U_Planck − βσ²  (exact)\nevery σ > 0 misses Planck; "
            "only σ = 0 reproduces it\n(Lean: planck_forces_levels)", transform=bx.transAxes,
            color=INK2, fontsize=9.5)
    bx.legend(loc="upper left", fontsize=9)
    bx.set_title("Deviation from Planck's mean energy", loc="left", fontsize=11.5)

    fig.suptitle("Poincaré 1912 — Planck's law forces discrete levels", x=0.01, ha="left",
                 fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "poincare1912_discreteness.png", facecolor=SURFACE)
    plt.close(fig)


def dirac_gammas():
    i = 1j
    return [np.diag([1, 1, -1, -1]).astype(complex),
            np.array([[0, 0, 0, 1], [0, 0, 1, 0], [0, -1, 0, 0], [-1, 0, 0, 0]], complex),
            np.array([[0, 0, 0, -i], [0, 0, i, 0], [0, i, 0, 0], [-i, 0, 0, 0]]),
            np.array([[0, 0, 1, 0], [0, 0, 0, -1], [-1, 0, 0, 0], [0, 1, 0, 0]], complex)]


def fig_dirac():
    g = dirac_gammas()
    fig = plt.figure(figsize=(12.4, 4.8), dpi=150)
    gs = fig.add_gridspec(2, 6, width_ratios=[2.2, 0.15, 1, 1, 1, 1], hspace=0.45, wspace=0.35)

    ax = fig.add_subplot(gs[:, 0])
    ns = np.arange(1, 7)
    cols = [MUTED if n < 4 else (ORANGE if n == 4 else BLUE) for n in ns]
    ax.bar(ns, ns ** 2, color=cols, width=0.62, zorder=3)
    ax.axhline(16, color=INK2, lw=1.4, ls="--", zorder=4)
    ax.text(0.6, 16.8, "16 independent monomials", color=INK2, fontsize=9.5)
    ax.text(2, 2.8 ** 2 + 1, "n² < 16:\nimpossible", ha="center", color=INK2, fontsize=9.5)
    ax.text(4, 22.5, "attained\n(Dirac)", ha="center", color=ORANGE, fontsize=9.5)
    ax.set_xticks(ns)
    ax.set_xlabel("matrix size  n")
    ax.set_ylabel("dim Matₙ(ℂ) = n²")
    ax.set_ylim(0, 40)
    ax.grid(axis="y", color=GRID, zorder=0)
    ax.set_title("Minimal dimension = 4  (Lean: isLeast_dim)", loc="left", fontsize=11.5)

    for mu in range(4):
        for row, (part, name) in enumerate([(np.real, "Re"), (np.imag, "Im")]):
            cx = fig.add_subplot(gs[row, 2 + mu])
            cx.imshow(part(g[mu]), cmap="RdBu_r", vmin=-1, vmax=1)
            cx.set_xticks([])
            cx.set_yticks([])
            cx.set_title(f"{name} γ{'⁰¹²³'[mu]}", fontsize=10)
            for (r, c), v in np.ndenumerate(part(g[mu])):
                if v != 0:
                    cx.text(c, r, f"{v:+.0f}", ha="center", va="center", fontsize=7.5,
                            color=SURFACE)

    anti = np.array([[np.allclose(g[m] @ g[n] + g[n] @ g[m],
                                  2 * (m == n) * (1 if m == 0 else -1) * np.eye(4))
                      for n in range(4)] for m in range(4)])
    assert anti.all()
    fig.text(0.5, -0.04, "{γ^μ, γ^ν} = 2η^μν · 1,  η = diag(1, −1, −1, −1):  all 16 relations "
             "hold (Lean: diracGamma_clifford, by decide over ℤ[i])", ha="center", color=INK2,
             fontsize=9.5)
    fig.suptitle("Dirac 1928 — no 2 × 2 gamma matrices; the minimum is 4 × 4", x=0.01,
                 ha="left", fontsize=13, color=INK)
    fig.savefig(OUT / "dirac1928_minimal_dimension.png", facecolor=SURFACE, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    fig_poincare1911()
    fig_poincare1912()
    fig_dirac()

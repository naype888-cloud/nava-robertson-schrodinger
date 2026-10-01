"""Figure for Penrose1996: the time–energy relation is a bound, not a lifetime (numpy, matplotlib).

Writes docs/figures/penrose1996_speed_limit.png.

Left: survival amplitudes |A(t)| = |∑ p_k e^{−i E_k t}| against ΔE·t (ħ = 1): two equal branches
(|cos ΔE t|, exact) and random finite spectra (numerical), above the Lean bound 1 − (ΔE t)²/2.
At Penrose's time ΔE·t = 1 every curve is at least 1/2; none reaches 0 before √2.
Right: unitary dynamics revives (period π/ΔE, Lean) while a Diósi–Penrose collapse at rate ΔE/ħ
would decay; the decay curve is the model's prediction, not a consequence of unitary dynamics.

Exact (Lean, Penrose1996): the bound, ‖A‖ ≥ 1/2 at ΔE·t ≤ 1, two-branch orthogonality at π/2,
period π. The Mandelstam–Tamm curve cos(ΔE t) is shown for reference; it is not formalized here.

Run:  python3 docs/simulation/figures_penrose.py
"""

import matplotlib.pyplot as plt
import numpy as np

from figures_threshold_cone import BLUE, INK, INK2, MUTED, ORANGE, OUT, SURFACE


def survival(p, e, s):
    """|A| at ΔE·t = s for weights p on energies e."""
    sigma = np.sqrt(p @ (e - p @ e) ** 2)
    t = s / sigma
    return np.abs(np.exp(-1j * np.outer(t, e)) @ p)


def fig_penrose():
    rng = np.random.default_rng(1996)
    s = np.linspace(0, 3.2, 700)
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(11.8, 4.7), dpi=150,
                                 gridspec_kw={"width_ratios": [1.15, 1]})

    for i in range(14):
        n = rng.integers(3, 25)
        p = rng.dirichlet(np.ones(n))
        e = rng.normal(size=n) * rng.uniform(0.5, 3)
        ax.plot(s, survival(p, e, s), color=MUTED, lw=0.8, alpha=0.55,
                label="random spectra (numerical)" if i == 0 else None)
    ax.plot(s, np.abs(np.cos(s)), color=BLUE, lw=2.2, label="two equal branches: |cos ΔE t|")
    m = s <= np.pi / 2
    ax.plot(s[m], np.cos(s[m]), color=INK, lw=1.1, ls=":",
            label="Mandelstam–Tamm cos ΔE t (reference)")
    b = s <= np.sqrt(2)
    ax.plot(s[b], 1 - s[b] ** 2 / 2, color=ORANGE, lw=2, ls="--",
            label="Lean bound 1 − (ΔE t)²/2")
    ax.fill_between([0, 1], 0.5, 1.0, color=ORANGE, alpha=0.08)
    ax.axvline(1, color=ORANGE, lw=1)
    ax.plot([1], [0.5], "o", color=ORANGE, mec=SURFACE, mew=1.3, ms=7, zorder=5)
    ax.text(0.03, 0.3, "shaded: until Penrose's\ntime ħ/ΔE, ‖A‖ ≥ 1/2", color=INK2,
            fontsize=9.5, va="bottom")
    ax.axvline(np.sqrt(2), color=MUTED, lw=0.9, ls=":")
    ax.axvline(np.pi / 2, color=BLUE, lw=0.9, ls=":")
    ax.text(np.sqrt(2) - 0.03, 0.02, "√2", ha="right", color=INK2, fontsize=9.5)
    ax.text(np.pi / 2 + 0.07, 0.02, "π/2", color=BLUE, fontsize=9.5)
    ax.set_xlim(0, 3.2)
    ax.set_ylim(0, 1.3)
    ax.set_xlabel("ΔE · t / ħ")
    ax.set_ylabel("survival amplitude  ‖A(t)‖")
    ax.legend(loc="upper right", fontsize=8.6, framealpha=0.95, ncol=2)
    ax.set_title("The speed limit: no orthogonality before √2 ħ/ΔE", loc="left", fontsize=11.5)

    t = np.linspace(0, 4 * np.pi, 1200)
    bx.plot(t, np.cos(t) ** 2, color=BLUE, lw=2, label="unitary, two branches: revives (Lean)")
    bx.plot(t, np.exp(-t), color=ORANGE, lw=2, ls="--",
            label="collapse at rate ΔE/ħ (Diósi–Penrose model)")
    for k in range(1, 5):
        bx.axvline(k * np.pi, color=MUTED, lw=0.8, ls=":")
    bx.annotate("", (2 * np.pi, 1.06), (np.pi, 1.06),
                arrowprops=dict(arrowstyle="<->", color=INK2, lw=0.9))
    bx.text(1.5 * np.pi, 1.08, "period πħ/ΔE", color=INK2, fontsize=9.5, ha="center",
            va="bottom")
    bx.set_xlim(0, 4 * np.pi)
    bx.set_ylim(0, 1.45)
    bx.set_xlabel("ΔE · t / ħ")
    bx.set_ylabel("survival probability  ‖A(t)‖²")
    bx.legend(loc="upper right", fontsize=8.8, framealpha=0.95, ncol=1,
              bbox_to_anchor=(1.0, 1.0))
    bx.set_title("Unitary evolution never decays", loc="left", fontsize=11.5)

    fig.suptitle("Penrose 1996 — the time–energy relation is a bound, not a lifetime", x=0.01,
                 ha="left", fontsize=13, color=INK)
    fig.tight_layout()
    fig.savefig(OUT / "penrose1996_speed_limit.png", facecolor=SURFACE)
    plt.close(fig)


if __name__ == "__main__":
    fig_penrose()

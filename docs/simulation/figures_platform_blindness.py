"""Figures for D47 (platform blindness), d = 4 (numpy, matplotlib).

Writes to docs/figures/:
  d47_platform_blindness.png   tension vs Gram defect (the Robertson-Schrodinger gap):
                               what a single-guide-excitation platform can and cannot see

Exact values used: tension of psi* is 2/(d-1); the Gram defect of (e_1+e_2)/sqrt(2) is
1/(18 rho_4^2) (D47, gram-defect counterexample with zero tension). Everything else on the
curves is a direct numerical evaluation of the definitions in
NavaRobertsonIndependent/Mathematics/D21/D23 (variance, covariance, imPart, gramDefectAt).
"""

from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

from figures_threshold_cone import BLUE, INK2, MUTED, ORANGE, OUT, SURFACE, ops

plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
    "axes.edgecolor": "#e4e3df", "axes.labelcolor": INK2, "axes.titlecolor": "#0b0b0b",
    "xtick.color": MUTED, "ytick.color": MUTED, "grid.color": "#e4e3df", "axes.grid": True,
    "axes.spines.top": False, "axes.spines.right": False, "font.size": 11,
    "axes.titlesize": 12, "legend.frameon": False,
})

D = 4
T, P = ops(D)


def state_stats(z):
    """(tension, gramDefect) of a unit state, per D21/D23 definitions."""
    z = z / np.linalg.norm(z)
    mt = z.conj() @ T @ z
    mp = z.conj() @ P @ z
    ct, cp = T @ z - mt * z, P @ z - mp * z
    var_t, var_p = np.vdot(ct, ct).real, np.vdot(cp, cp).real
    inner = np.vdot(ct, cp)
    tension = -2 * inner.imag  # <i[T,P]> = -2 Im <T psi~, P psi~>
    defect = var_t * var_p - abs(inner) ** 2
    return tension, defect


def max_current_state(d):
    j = np.arange(d)
    return ((-1j) ** j) * np.sin((j + 1) * np.pi / (d + 1))


def main():
    e1, e2 = np.zeros(D, complex), np.zeros(D, complex)
    e1[0], e2[1] = 1, 1

    # sanity: the D47 counterexample, (e1 + e2)/sqrt(2), zero tension, positive defect
    rho4 = 2 * np.cos(np.pi / 5)
    t0, d0 = state_stats(e1 + e2)
    assert abs(t0) < 1e-12 and abs(d0 - 1 / (18 * rho4 ** 2)) < 1e-12, (t0, d0)

    phi = np.linspace(0, 2 * np.pi, 1201)
    curve = np.array([state_stats(e1 + np.exp(1j * a) * e2) for a in phi])

    th = np.linspace(0, np.pi / 2, 601)
    real_curve = np.array([state_stats(np.cos(a) * e1 + np.sin(a) * e2) for a in th])
    assert np.max(np.abs(real_curve[:, 0])) < 1e-12  # real states carry no tension

    ts, ds = state_stats(max_current_state(D))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.5, 4.8))

    ax1.plot(curve[:, 0], curve[:, 1], color=BLUE, lw=2,
             label=r"$\psi(\varphi)=(e_1+e^{i\varphi}e_2)/\sqrt{2}$")
    ax1.plot(real_curve[:, 0], real_curve[:, 1], color=ORANGE, lw=2, ls="--",
             label=r"$\psi(\theta)=\cos\theta\,e_1+\sin\theta\,e_2$ (real)")
    ax1.scatter([0], [0], zorder=5, color="#0b0b0b", s=42,
                label="position eigenstates (single-guide input): 0 = 0")
    ax1.scatter([t0], [d0], zorder=5, color=ORANGE, s=55, marker="s",
                label=r"$(e_1+e_2)/\sqrt{2}$: defect, no tension (D47)")
    ax1.scatter([ts], [ds], zorder=6, color="#b03a48", s=110, marker="*",
                label=r"$\psi^{*}$: maximal tension $2/(d-1)$")
    ax1.set_xlabel(r"tension  $\langle i[T_d,P_d]\rangle$")
    ax1.set_ylabel(r"Gram defect  $\mathrm{Var}\,T\cdot\mathrm{Var}\,P-|\langle\tilde T,\tilde P\rangle|^2$")
    ax1.set_title("D47, d = 4: the defect does not require tension")
    ax1.legend(loc="upper left", fontsize=9)

    ax2.plot(th / (np.pi / 2), real_curve[:, 1], color=ORANGE, lw=2)
    ax2.scatter([0, 1], [0, 0], color="#0b0b0b", zorder=5, s=42,
                label="position eigenstates: defect 0")
    ax2.scatter([0.5], [d0], color=ORANGE, marker="s", zorder=5, s=55,
                label=r"$(e_1+e_2)/\sqrt{2}$")
    ax2.set_xlabel(r"mixing $\theta$ ($\pi/2$ = equal amplitudes)")
    ax2.set_ylabel("Gram defect (tension is identically 0)")
    ax2.set_title("Real superpositions: a whole arc of unseen defect")
    ax2.legend(loc="upper right", fontsize=9)

    fig.tight_layout()
    fig.savefig(OUT / "d47_platform_blindness.png", dpi=200)
    print("wrote", OUT / "d47_platform_blindness.png")
    print(f"psi*: tension={ts:.6f} (2/(d-1)={2/(D-1)}), defect={ds:.6e}")
    print(f"(e1+e2)/sqrt(2): defect={d0:.12f}, 1/(18 rho^2)={1/(18*rho4**2):.12f}")


if __name__ == "__main__":
    main()

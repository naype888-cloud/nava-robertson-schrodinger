"""Figure for D44: the velocity band ϙ(d) and the defect at the cone (numpy, scipy, matplotlib).

Writes docs/figures/d44_velocity_band.png and d44_velocity_band_tail.png.

A state saturates Robertson–Schrödinger iff (T − ⟨T⟩)ψ = λ (P − ⟨P⟩)ψ for some complex λ
(D23), that is iff ψ is an eigenvector of T_d − λ P_d. So v*(d) is the largest speed among the
eigenvectors of T_d − λ P_d over λ ∈ ℂ: a grid over λ = e^r e^{iφ}, refined by Nelder–Mead.
At d = 4 this reproduces v*(4) = 3(√5 − 1)/4 of D43 to 1e-15.

Exact values (Lean): ϙ(2) = ϙ(3) = 0, ϙ(4) = (7 − 3√5)/4, ϙ(d) > 0 for d ≥ 4 (D44);
θ_NRS(4) = arccos (1/√((99 − 42√5)/5)), θ_NRS strictly increasing below arccos (1/C_∞) (D37b).
The values of ϙ(d) for d ≥ 5 are numerical.

Tail. For every d ≥ 5 the optimal λ is purely imaginary, λ = iμ (checked against the full
search for d ≤ 60), so the tail uses a one-dimensional search over μ, in parallel.
The fits of d² ϙ(d) = a ln d + b + c/d, one per parity, are numerical.

Run:  python3 docs/simulation/figures_velocity_band.py [band] [tail]
"""

import os
from multiprocessing import Pool

import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import minimize, minimize_scalar

from figures_threshold_cone import BLUE, INK2, MUTED, ORANGE, OUT, SURFACE, VSTAR4, ops, stats

DS = list(range(2, 21)) + [24, 30, 40]
C_INF = np.sqrt(np.pi ** 2 / 3 - 2)
THETA_INF = np.degrees(np.arccos(1 / C_INF))


def speed(d, t_op, p_op, lam):
    """Largest speed among the eigenvectors of T_d − λ P_d."""
    _, vecs = np.linalg.eig(t_op - lam * p_op)
    return max(abs(stats(t_op, p_op, vecs[:, k])[0]) for k in range(d)) * (d - 1) / 2


def vstar(d):
    """Fastest minimum-uncertainty speed v*(d)."""
    t_op, p_op = ops(d)
    f = lambda x: -speed(d, t_op, p_op, np.exp(x[0] + 1j * x[1]))
    grid = [(r, a) for r in np.linspace(-6, 6, 121) for a in np.linspace(-np.pi, np.pi, 181)]
    vals = np.array([f(g) for g in grid])
    best = -vals.min()
    for i in np.argsort(vals)[:12]:
        r = minimize(f, grid[i], method="Nelder-Mead",
                     options={"xatol": 1e-13, "fatol": 1e-15, "maxiter": 20000})
        best = max(best, -r.fun)
    return best


def vstar_imag(d):
    """v*(d) along λ = iμ, the optimal direction for d ≥ 5."""
    t_op, p_op = ops(d)
    g = lambda r: -speed(d, t_op, p_op, 1j * np.exp(r))
    rs = np.linspace(-6, 3, 91)
    i = int(np.argmin([g(r) for r in rs]))
    return -minimize_scalar(g, bracket=(rs[i - 1], rs[i], rs[i + 1]), tol=1e-12).fun


def cone_angle(d):
    """θ_NRS(d) in degrees, at the maximal current state."""
    t_op, p_op = ops(d)
    _, vecs = np.linalg.eigh(1j * (t_op @ p_op - p_op @ t_op))
    _, vt, vp, c = stats(t_op, p_op, vecs[:, -1])
    return np.degrees(np.arccos(min(1.0, np.sqrt(c / (vt * vp)))))


def dots(ax, ds, ys, exact):
    """Numerical points in blue; d = 2, 3 and d = 4 (Lean) highlighted."""
    ax.plot(ds, ys, color=BLUE, lw=1.6, alpha=0.55)
    ax.plot(ds[3:], ys[3:], "o", ms=6, color=BLUE, mec=SURFACE, mew=1.5)
    ax.plot(ds[:2], ys[:2], "o", ms=8, color=INK2, mec=SURFACE, mew=2, zorder=5)
    ax.plot([4], [exact], "o", ms=9, color=ORANGE, mec=SURFACE, mew=2, zorder=5)


def fig_velocity_band():
    koppa = np.array([1 - vstar(d) if d >= 4 else 0.0 for d in DS])
    theta = np.array([cone_angle(d) if d >= 4 else 0.0 for d in DS])
    print("d  ϙ(d)  θ_NRS(d)")
    for d, k, t in zip(DS, koppa, theta):
        print(f"{d:>2}  {k:.7f}  {t:.4f}°")
    assert abs(koppa[2] - (1 - VSTAR4)) < 1e-9

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(8.2, 8.4), dpi=150, sharex=True)

    dots(ax1, DS, koppa, 1 - VSTAR4)
    ax1.axhline(0, color=MUTED, lw=1)
    ax1.annotate("d = 4: ϙ(4) = (7 − 3√5)/4 ≈ 0.0729  (exact, D44)", xy=(4, 1 - VSTAR4),
                 xytext=(8, 0.071), color=INK2, fontsize=10.5,
                 arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax1.annotate("d = 2, 3: ϙ = 0, no band (D44)", xy=(3, 0), xytext=(5, -0.009),
                 color=INK2, fontsize=10.5, arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax1.text(19, 0.036, "d ≥ 5: numerical; odd d narrower.\nLean: ϙ(d) > 0 for every d ≥ 4, "
             "never 0.", color=INK2, fontsize=10.5)
    ax1.set_ylabel("ϙ(d) = 1 − v*(d)")
    ax1.set_ylim(-0.013, 0.08)
    ax1.set_title("(a) Width of the band where the defect is forced", loc="left", fontsize=12)

    dots(ax2, DS, theta, theta[2])
    ax2.axhline(THETA_INF, color=ORANGE, lw=1.2, ls="--")
    ax2.text(40, THETA_INF + 0.6, f"arccos (1/C∞) ≈ {THETA_INF:.2f}°, never reached (D37b)",
             color=INK2, fontsize=10.5, ha="right", va="bottom")
    ax2.annotate(f"d = 4: θ_NRS(4) ≈ {theta[2]:.2f}°  (exact, D37b)", xy=(4, theta[2]),
                 xytext=(8, 4.5), color=INK2, fontsize=10.5,
                 arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax2.set_xlabel("positions per axis  d")
    ax2.set_ylabel("θ_NRS(d)  [degrees]")
    ax2.set_ylim(-1.5, 31)
    ax2.set_title("(b) Defect at the cone v = 1: grows with d", loc="left", fontsize=12)

    fig.suptitle("The velocity band ϙ(d) and the defect at the cone", x=0.02, ha="left",
                 fontsize=13)
    fig.tight_layout()
    fig.savefig(OUT / "d44_velocity_band.png")
    plt.close(fig)


def fig_tail():
    ds = np.array(list(range(5, 61)) + list(range(62, 121, 2)) + list(range(125, 302, 5)))
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    with Pool(os.cpu_count()) as pool:
        y = ds ** 2 * (1 - np.array(pool.map(vstar_imag, ds, chunksize=1)))

    fig, ax = plt.subplots(figsize=(8.2, 4.8), dpi=150)
    xs = np.geomspace(20, 301, 200)
    for parity, color, name in ((0, BLUE, "even d"), (1, ORANGE, "odd d")):
        m = ds % 2 == parity
        ax.plot(ds[m], y[m], "o", ms=5, color=color, mec=SURFACE, mew=1.2, label=name)
        f = m & (ds >= 19)
        a, b, c = np.linalg.lstsq(np.c_[np.log(ds[f]), np.ones(f.sum()), 1 / ds[f]], y[f],
                                  rcond=None)[0]
        print(f"{name}: d² ϙ ≈ {a:.3f} ln d {b:+.3f} {c:+.2f}/d")
        ax.plot(xs, a * np.log(xs) + b + c / xs, color=color, lw=1.2, ls="--")
        label = f"  {name}: {a:.2f} ln d − {-b:.2f} + {c:.1f}/d"
        ax.text(302, a * np.log(301) + b + c / 301, label, color=INK2, fontsize=10, va="center")
    ax.set_xscale("log")
    ax.set_xlim(4.5, 1100)
    ax.set_xticks([5, 10, 20, 50, 100, 200, 300])
    ax.set_xticklabels(["5", "10", "20", "50", "100", "200", "300"])
    ax.set_xlabel("positions per axis  d  (log scale)")
    ax.set_ylabel("d² · ϙ(d)")
    ax.legend(loc="upper left")
    ax.set_title("Tail of the band: ϙ(d) ≈ (2 ln d + b)/d², positive for every d (numerical)",
                 loc="left", fontsize=12)
    fig.tight_layout()
    fig.savefig(OUT / "d44_velocity_band_tail.png")
    plt.close(fig)


if __name__ == "__main__":
    import sys
    todo = sys.argv[1:] or ["band", "tail"]
    if "band" in todo:
        fig_velocity_band()
    if "tail" in todo:
        fig_tail()

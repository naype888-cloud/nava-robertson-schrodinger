"""Figures for D42/D43 and the light cone (numpy, scipy, matplotlib).

Writes to docs/figures/:
  d43_velocity_threshold.png     minimum Robertson–Schrödinger angle against velocity, d = 4
  d43_threshold_by_dimension.png velocity threshold v*(d) of minimum uncertainty
  nrs3_light_cone.png            cone in steps (D37f), Lieb–Robinson (D37g), two axes

Exact values (Lean): v*(4) = 3(√5 − 1)/4, θ_NRS(4), v*(2) = v*(3) = 1.
Everything else is numerical and labelled as such.
"""

from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap, LogNorm
from math import factorial
from scipy.linalg import expm
from scipy.optimize import minimize

OUT = Path(__file__).resolve().parent.parent / "figures"

SURFACE, INK, INK2, MUTED, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#8a8985", "#e4e3df"
BLUE, ORANGE = "#2a78d6", "#eb6834"
SEQ = LinearSegmentedColormap.from_list(
    "blue", ["#cde2fb", "#86b6ef", "#3987e5", "#1c5cab", "#0d366b"])
SEQ.set_bad(SURFACE)
SEQ0 = LinearSegmentedColormap.from_list(
    "blue0", [SURFACE, "#cde2fb", "#86b6ef", "#3987e5", "#1c5cab", "#0d366b"])

plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
    "axes.edgecolor": GRID, "axes.labelcolor": INK2, "axes.titlecolor": INK,
    "xtick.color": MUTED, "ytick.color": MUTED, "grid.color": GRID, "axes.grid": True,
    "axes.spines.top": False, "axes.spines.right": False, "font.size": 11,
    "axes.titlesize": 13, "legend.frameon": False,
})

PHI = (1 + 5 ** 0.5) / 2
VSTAR4 = 3 * (5 ** 0.5 - 1) / 4


def ops(d):
    a = np.diag(np.ones(d - 1), 1)
    a = a + a.T
    rho = 2 * np.cos(np.pi / (d + 1))
    p = np.diag([(2 * (j + 1) - (d + 1)) / (d - 1) for j in range(d)])
    return (a / rho).astype(complex), p.astype(complex)


def stats(t_op, p_op, z):
    z = z / np.linalg.norm(z)
    k_op = 1j * (t_op @ p_op - p_op @ t_op)
    m = lambda x: z.conj() @ x @ z
    x_t, x_p = t_op @ z - m(t_op) * z, p_op @ z - m(p_op) * z
    vt, vp = np.vdot(x_t, x_t).real, np.vdot(x_p, x_p).real
    return m(k_op).real, vt, vp, abs(np.vdot(x_t, x_p)) ** 2


def min_angle(d, v, rng, tries=30, state=False):
    """Smallest Robertson–Schrödinger angle among unit states of velocity v."""
    t_op, p_op = ops(d)
    target = v * 2 / (d - 1)
    unpack = lambda x: x[:d] + 1j * x[d:]

    def sin2(x):
        _, vt, vp, c = stats(t_op, p_op, unpack(x))
        return 1 - c / (vt * vp)

    cons = [{"type": "eq", "fun": lambda x: stats(t_op, p_op, unpack(x))[0] - target}]
    best, arg = 1.0, None
    for _ in range(tries):
        r = minimize(sin2, rng.normal(size=2 * d), method="SLSQP", constraints=cons,
                     options={"ftol": 1e-14, "maxiter": 500})
        if r.success and abs(stats(t_op, p_op, unpack(r.x))[0] - target) < 1e-9:
            if r.fun < best:
                best, arg = r.fun, unpack(r.x)
    angle = np.degrees(np.arcsin(np.sqrt(max(best, 0.0))))
    if not state:
        return angle
    z = arg / np.linalg.norm(arg)
    return angle, z * np.exp(-1j * np.angle(z[0]))


def tilted_angle(d, theta):
    """Angle of the tilted beam e^{-ijθ} sin((j+1)π/(d+1)) and its velocity."""
    t_op, p_op = ops(d)
    j = np.arange(d)
    z = np.exp(-1j * theta * j) * np.sin((j + 1) * np.pi / (d + 1))
    t, vt, vp, c = stats(t_op, p_op, z)
    return t * (d - 1) / 2, np.degrees(np.arcsin(np.sqrt(max(1 - c / (vt * vp), 0.0))))


def vstar(d, rng, tries=40):
    """Largest velocity of a Robertson–Schrödinger-saturating state (eigenvectors of T − cP)."""
    t_op, p_op = ops(d)

    def f(x):
        _, v = np.linalg.eig(t_op - (x[0] + 1j * x[1]) * p_op)
        return -max(stats(t_op, p_op, v[:, k])[0] for k in range(d))

    best = max(-minimize(f, rng.normal(0, 2, 2), method="Nelder-Mead",
                         options={"xatol": 1e-12, "fatol": 1e-14, "maxiter": 4000}).fun
               for _ in range(tries))
    return best * (d - 1) / 2


def fig_threshold():
    rng = np.random.default_rng(0)
    v_lo = np.linspace(0.0, 0.92, 24)
    v_hi = np.concatenate([np.linspace(VSTAR4, 0.99, 22), [0.995, 0.999, 1.0]])
    vs = np.concatenate([v_lo, v_hi])
    ang = np.array([min_angle(4, v, rng) for v in vs])
    thetas = np.linspace(0.02, np.pi / 2, 60)
    tb = np.array([tilted_angle(4, th) for th in thetas])
    theta4 = ang[-1]

    fig, ax = plt.subplots(figsize=(8.2, 5.0), dpi=150)
    ax.axvspan(VSTAR4, 1.0, color=ORANGE, alpha=0.07, lw=0)
    ax.plot(tb[:, 0], tb[:, 1], color=ORANGE, lw=2, ls=(0, (5, 3)))
    ax.plot(vs, ang, color=BLUE, lw=2.2)
    ax.plot([VSTAR4], [0], "o", ms=8, color=BLUE, mec=SURFACE, mew=2, zorder=5)
    ax.plot([1.0], [theta4], "o", ms=8, color=BLUE, mec=SURFACE, mew=2, zorder=5)
    ax.axvline(VSTAR4, color=MUTED, lw=1)

    ax.text(0.30, 0.45, "optimal state at each velocity:\nminimum uncertainty possible",
            color=INK2, fontsize=10.5)
    ax.text(0.30, theta4 + 0.35, "tilted beam  v = sin θ:  7.43° at every tilt",
            color=INK2, fontsize=10.5)
    ax.annotate("v*(4) = 3(√5 − 1)/4 ≈ 0.927\n(exact, Lean D43)", xy=(VSTAR4, 0.05),
                xytext=(0.58, 2.3), color=INK2, fontsize=10.5,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax.annotate("$\\theta_{NRS}(4)$ ≈ 7.43° at the cone\n(exact, Lean D37b)", xy=(1.0, theta4),
                xytext=(0.62, 5.0), color=INK2, fontsize=10.5,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax.text(0.30, theta4 - 1.0, "shaded: v > v*(4), the defect is forced", color=ORANGE,
            fontsize=10.5)

    ax.set_xlim(0, 1.03)
    ax.set_ylim(-0.3, 8.6)
    ax.set_xlabel("velocity  v  (fraction of the cone, D38)")
    ax.set_ylabel("smallest Robertson–Schrödinger angle  (degrees)")
    ax.set_title("The velocity threshold of minimum uncertainty on 4 sites (D43)", loc="left")
    fig.text(0.01, 0.01, "Curves: numerical minimum over states (SLSQP) and the tilted-beam "
             "family. Points: exact values proved in Lean.", color=MUTED, fontsize=8.5)
    fig.tight_layout(rect=(0, 0.03, 1, 1))
    fig.savefig(OUT / "d43_velocity_threshold.png")
    plt.close(fig)


def fig_by_dimension():
    rng = np.random.default_rng(1)
    ds = list(range(2, 21)) + [24, 30, 40]
    vv = np.array([vstar(d, rng) for d in ds])

    fig, ax = plt.subplots(figsize=(8.2, 4.8), dpi=150)
    ax.axhline(1.0, color=MUTED, lw=1)
    ax.plot(ds, vv, color=BLUE, lw=1.6, alpha=0.55)
    ax.plot(ds, vv, "o", ms=6, color=BLUE, mec=SURFACE, mew=1.5)
    ax.plot([2, 3], [1, 1], "o", ms=8, color=INK2, mec=SURFACE, mew=2, zorder=5)
    ax.plot([4], [VSTAR4], "o", ms=9, color=ORANGE, mec=SURFACE, mew=2, zorder=5)
    ax.annotate("d = 2, 3: minimum uncertainty at the cone (D21)", xy=(3, 1.0),
                xytext=(6.5, 1.004), color=INK2, fontsize=10.5,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax.annotate("d = 4: v* = 3(√5 − 1)/4 ≈ 0.927 (exact, D43)\nthe widest forbidden band",
                xy=(4, VSTAR4), xytext=(8, 0.935), color=INK2, fontsize=10.5,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=1))
    ax.text(20, 0.955, "d ≥ 5: numerical; the band [v*, 1] narrows\nbut the defect at the cone "
            "grows (D37b)", color=INK2, fontsize=10.5)
    ax.set_xlabel("sites per axis  d")
    ax.set_ylabel("threshold  v*(d)")
    ax.set_ylim(0.915, 1.012)
    ax.set_title("Fastest minimum-uncertainty velocity by dimension", loc="left")
    fig.tight_layout()
    fig.savefig(OUT / "d43_threshold_by_dimension.png")
    plt.close(fig)


def fig_light_cone():
    n = 41
    c = n // 2
    t1, _ = ops(n)
    fig, axs = plt.subplots(2, 2, figsize=(11, 9.4), dpi=150)

    # (a) steps on the path
    ax = axs[0, 0]
    kmax = 15
    rows, m = [], np.eye(n, dtype=complex)
    for _ in range(kmax + 1):
        rows.append(np.abs(m[c]))
        m = m @ t1
    img = np.ma.masked_less(np.array(rows), 1e-14)
    ax.imshow(img, origin="lower", cmap=SEQ, norm=LogNorm(1e-5, 1), aspect="auto",
              extent=(-c - 0.5, c + 0.5, -0.5, kmax + 0.5))
    ax.plot([0, -kmax], [0, kmax], color=ORANGE, lw=1.5, ls="--")
    ax.plot([0, kmax], [0, kmax], color=ORANGE, lw=1.5, ls="--")
    ax.set_xlim(-20, 20)
    ax.grid(False)
    ax.set_title("(a) Steps: exactly zero outside |i − j| ≤ k  (D37f)", loc="left", fontsize=12)
    ax.set_xlabel("site  i − j")
    ax.set_ylabel("steps  k")

    # (b) continuous time and the Lieb–Robinson bound
    ax = axs[0, 1]
    t = 5.0
    u = np.abs(expm(-1j * t * t1)[c, c:])
    r = np.arange(len(u))
    bound = np.array([t ** k / factorial(k) * np.exp(t) for k in r])
    ax.semilogy(r, bound, color=ORANGE, lw=2, ls=(0, (5, 3)))
    ax.semilogy(r, u, "o-", color=BLUE, lw=1.6, ms=4.5, mec=SURFACE, mew=1)
    ax.text(12.3, 6, "bound  tʳ/r! · eᵗ  (D37g)", color=INK2, fontsize=10.5)
    ax.text(3, 1e-9, "|U(t)ᵢⱼ| at t = 5", color=INK2, fontsize=10.5)
    ax.set_xlim(0, 20)
    ax.set_ylim(1e-12, 1e4)
    ax.set_title("(b) Continuous time: superexponential tail", loc="left", fontsize=12)
    ax.set_xlabel("distance  r = |i − j|")
    ax.set_ylabel("amplitude")

    # two axes: 31 × 31
    n2 = 31
    c2 = n2 // 2
    t2, _ = ops(n2)
    rho2 = 2 * np.cos(np.pi / (n2 + 1))
    k = 8
    tx =np.kron(t2, np.eye(n2)) + np.kron(np.eye(n2), t2)
    e0 = np.zeros(n2 * n2)
    e0[c2 * n2 + c2] = 1
    s2 = np.abs(np.linalg.matrix_power(tx, k) @ e0).reshape(n2, n2)
    s2 = np.ma.masked_less(s2 / s2.max(), 1e-14)
    ext = (-c2 - 0.5, c2 + 0.5, -c2 - 0.5, c2 + 0.5)
    diamond = np.array([[k, 0], [0, k], [-k, 0], [0, -k], [k, 0]])

    ax = axs[1, 0]
    ax.imshow(s2, origin="lower", cmap=SEQ, norm=LogNorm(1e-6, 1), extent=ext)
    ax.plot(diamond[:, 0], diamond[:, 1], color=ORANGE, lw=1.5, ls="--")
    ax.grid(False)
    ax.set_title(f"(c) Two axes, {k} steps: the rhombus |Δx| + |Δy| ≤ k", loc="left",
                 fontsize=12)
    ax.set_xlabel("Δx")
    ax.set_ylabel("Δy")

    ax = axs[1, 1]
    tc = k * rho2 / 2
    u2 = expm(-1j * tc * t2)[:, c2]
    inten = np.abs(np.outer(u2, u2)) ** 2
    ax.imshow(inten / inten.max(), origin="lower", cmap=SEQ0, vmin=0, vmax=1, extent=ext)
    front = 2 * tc / rho2
    sq = np.array([[front, front], [-front, front], [-front, -front], [front, -front],
                   [front, front]])
    ax.plot(diamond[:, 0], diamond[:, 1], color=ORANGE, lw=1.5, ls="--")
    ax.plot(sq[:, 0], sq[:, 1], color=INK, lw=1.4, ls=":")
    ax.grid(False)
    ax.set_title("(d) Continuous time: a square, bright corners", loc="left",
                 fontsize=12)
    ax.set_xlabel("Δx")
    ax.set_ylabel("Δy")
    ax.text(-c2 + 0.5, -c2 + 1.0, "dotted: |Δx|, |Δy| ≤ front of each axis (D38)\n"
            "dashed: the rhombus of (c)", color=INK2, fontsize=9.5)

    fig.suptitle("The light cone of transport: steps, continuous time and two axes",
                 x=0.01, ha="left", color=INK, fontsize=14)
    fig.text(0.01, 0.005, "Colour: amplitude, log scale, in (a) and (c); intensity, linear, in (d) "
             "(what a camera records); normalized to the maximum. Paths of 41 sites, square lattice 31 × 31.",
             color=MUTED, fontsize=8.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.97))
    fig.savefig(OUT / "nrs3_light_cone.png")
    plt.close(fig)


def table_states():
    """Optimal input states of N = 4 at chosen velocities (amplitudes and phases per guide)."""
    rng = np.random.default_rng(2)
    print("| v | angle | R | amplitudes |ψ_j| | phases (deg) |")
    print("|---|---|---|---|---|")
    for v in [0.5, 0.9, VSTAR4, 0.95, 0.97, 0.99, 1.0]:
        ang, z = min_angle(4, v, rng, state=True)
        amp = ", ".join(f"{a:.3f}" for a in np.abs(z))
        ph = ", ".join(f"{p:.1f}" for p in np.degrees(np.angle(z)))
        print(f"| {v:.4f} | {ang:.2f}° | {1 / np.cos(np.radians(ang)):.5f} | {amp} | {ph} |")


if __name__ == "__main__":
    import sys
    todo = sys.argv[1:] or ["threshold", "dimension", "cone"]
    if "states" in todo:
        table_states()
    if "threshold" in todo:
        fig_threshold()
    if "dimension" in todo:
        fig_by_dimension()
    if "cone" in todo:
        fig_light_cone()

"""Figure for D37h, the octahedral symmetry of the cube (numpy, matplotlib).

Writes to docs/figures/:
  d37h_octahedral_symmetry.png   the 48 signed permutations of the axes and the NRS angles

(a) A random unit state on the 4 × 4 × 4 cube: after each of the 48 signed permutations (σ, s),
    the three axis angles are the same three numbers, permuted (angleAxis_cubeSym).
(b) The same at Ψ* = ψ* ⊗ ψ* ⊗ ψ*: all three angles are θ_NRS(4) for every element
    (octahedral_symmetry).
(c) Cubes with unequal axes: each axis keeps its own angle θ_NRS(d) (closed form of D8, D37b);
    only the reflections and the exchanges of axes of equal length preserve the triple.

Panels (a) and (b) are computed from the matrices of D3 on the 64 sites; the check
angle(σ i, g Ψ) = angle(i, Ψ) is printed. Panel (c) evaluates the closed form numerically.

Run:  python3 docs/simulation/figures_octahedral_symmetry.py
"""

from itertools import permutations, product

import matplotlib.pyplot as plt
import numpy as np

from figures_threshold_cone import BLUE, GRID, INK, INK2, MUTED, ORANGE, OUT, ops

GREEN = "#2f8f5b"
AXIS_COLOR = [BLUE, ORANGE, GREEN]
AXIS_NAME = ["x", "y", "z"]


def psi_star(d):
    j = np.arange(d)
    v = (-1j) ** j * np.sin((j + 1) * np.pi / (d + 1))
    return v / np.linalg.norm(v)


def axis_ops(d):
    """(T, P) of each axis of the cube d × d × d, sites (a0, a1, a2) ↦ a0 d² + a1 d + a2."""
    t, p = ops(d)
    one = np.eye(d)
    out = []
    for i in range(3):
        mats = [one, one, one]
        mats[i] = t
        big_t = np.kron(np.kron(mats[0], mats[1]), mats[2])
        mats[i] = p
        big_p = np.kron(np.kron(mats[0], mats[1]), mats[2])
        out.append((big_t, big_p))
    return out


def angle(t_op, p_op, z):
    m = lambda a: np.vdot(z, a @ z).real
    x = t_op @ z - m(t_op) * z
    y = p_op @ z - m(p_op) * z
    c = abs(np.vdot(x, y)) / (np.linalg.norm(x) * np.linalg.norm(y))
    return np.degrees(np.arccos(min(c, 1.0)))


def signed_perms():
    """The 48 elements (σ, s): σ a permutation of the axes, s a reflection flag per axis."""
    return [(sigma, s) for sigma in permutations(range(3)) for s in product((0, 1), repeat=3)]


def act(sigma, s, d, z):
    """(g Ψ)(q) = Ψ(g⁻¹ q), with (g p)_j = flip_{s_j}(p_{σ⁻¹ j})."""
    inv = [sigma.index(j) for j in range(3)]
    out = np.zeros_like(z)
    for a in product(range(d), repeat=3):
        q = [a[inv[j]] for j in range(3)]
        q = [d - 1 - q[j] if s[j] else q[j] for j in range(3)]
        out[(q[0] * d + q[1]) * d + q[2]] = z[(a[0] * d + a[1]) * d + a[2]]
    return out


def theta_nrs(d):
    """θ_NRS(d) = arccos(1/C_Nava(d)) from the closed form of C_Nava² (D8)."""
    if d <= 3:
        return 0.0
    n, th = d + 1, np.pi / (d + 1)
    c2 = 2 * (d - 1) / (n * np.cos(th) ** 2) * ((n * n + 2) / 6 * np.sin(th) ** 2 - 1)
    return np.degrees(np.arccos(1 / np.sqrt(c2)))


def symmetry_count(dims):
    """Reflections (8) times the permutations of axes of equal length."""
    return 8 * sum(1 for sig in permutations(range(3))
                   if all(dims[sig[i]] == dims[i] for i in range(3)))


def panel_angles(ax, d, z, elements, title):
    axes = axis_ops(d)
    before = [angle(*axes[i], z) for i in range(3)]
    err = 0.0
    for k, (sigma, s) in enumerate(elements):
        gz = act(sigma, s, d, z)
        after = [angle(*axes[j], gz) for j in range(3)]
        for i in range(3):
            err = max(err, abs(after[sigma[i]] - before[i]))
        for j in range(3):
            ax.scatter(k + (j - 1) * 0.27, after[j], s=13, color=AXIS_COLOR[j], zorder=3,
                       label=f"axis {AXIS_NAME[j]}" if k == 0 else None)
    for v in sorted(set(np.round(before, 6))):
        ax.axhline(v, color=GRID, lw=1.2, zorder=1)
    for k in range(8, 48, 8):
        ax.axvline(k - 0.5, color=GRID, lw=0.8, ls=":", zorder=1)
    ax.set_xlim(-1, 48)
    ax.set_xticks([4 + 8 * m for m in range(6)])
    ax.set_xticklabels(["".join(AXIS_NAME[i] for i in sig) for sig, _ in elements[::8]],
                       fontsize=9)
    ax.set_xlabel("the 48 elements (σ, s): six axis orders × eight reflections", color=INK2)
    ax.set_ylabel("NRS angle of the axis (°)")
    ax.set_title(title, loc="left")
    ax.grid(False)
    return err


def fig_octahedral():
    d = 4
    elements = signed_perms()
    rng = np.random.default_rng(7)
    z = rng.normal(size=d ** 3) + 1j * rng.normal(size=d ** 3)
    z /= np.linalg.norm(z)
    star = np.kron(np.kron(psi_star(d), psi_star(d)), psi_star(d))

    fig, axs = plt.subplots(1, 3, figsize=(18, 5.6), dpi=150,
                            gridspec_kw={"width_ratios": [1.15, 1.15, 1]})
    err_a = panel_angles(axs[0], d, z, elements,
                         "(a) any state: the angle follows the axis")
    axs[0].legend(loc="center right", bbox_to_anchor=(1.0, 0.42), fontsize=9, markerscale=1.6)
    err_b = panel_angles(axs[1], d, star, elements,
                         "(b) at Ψ*: all three angles are θ_NRS(4)")
    axs[1].set_ylim(theta_nrs(4) - 1, theta_nrs(4) + 1)
    axs[1].text(24, theta_nrs(4) + 0.35, f"θ_NRS(4) = {theta_nrs(4):.2f}° on every axis, for all 48",
                ha="center", color=INK2, fontsize=10)
    axs[1].legend(loc="lower right", fontsize=9, markerscale=1.6)

    ax = axs[2]
    cubes = [(4, 4, 4), (100, 100, 4), (67, 25, 1600)]
    width = 0.26
    for c, dims in enumerate(cubes):
        for i in range(3):
            v = theta_nrs(dims[i])
            ax.bar(c + (i - 1) * width, v, width * 0.92, color=AXIS_COLOR[i], zorder=2,
                   label=f"axis {AXIS_NAME[i]}" if c == 0 else None)
            ax.text(c + (i - 1) * width, v - 0.5, f"{dims[i]}\n{v:.1f}°", ha="center",
                    va="top", fontsize=8, color="white", fontweight="bold")
    lim = np.degrees(np.arccos(1 / np.sqrt(np.pi ** 2 / 3 - 2)))
    ax.axhline(lim, color=MUTED, ls="--", lw=1)
    ax.text(-0.42, lim + 0.4, "arccos(1/C∞) ≈ 28.30°, never reached", ha="left", fontsize=9,
            color=MUTED)
    ax.set_xticks(range(len(cubes)))
    ax.set_xticklabels([" × ".join(map(str, c)) + f"\n{symmetry_count(c)} symmetries"
                        for c in cubes])
    ax.set_ylim(0, 36)
    ax.set_ylabel("NRS angle at Ψ* (°)")
    ax.set_title("(c) unequal axes: each keeps its own angle", loc="left")
    ax.legend(loc="upper left", fontsize=9, ncol=3)
    ax.grid(axis="x")

    fig.suptitle("D37h — the octahedral symmetry O_h of the cube d × d × d", x=0.01,
                 ha="left", fontsize=14, color=INK)
    fig.text(0.01, -0.02, "(a), (b): the 64-site cube 4 × 4 × 4 with T and P of D3 on each axis; "
             "a signed permutation sends (T, P) of axis i to (T, ±P) of axis σ i. "
             "(c): closed form of C_Nava (D8); the defect is there on every axis with d ≥ 4, "
             "its symmetry depends on which axes have equal length.",
             fontsize=8.5, color=MUTED)
    fig.tight_layout()
    fig.savefig(OUT / "d37h_octahedral_symmetry.png", bbox_inches="tight")
    plt.close(fig)
    return err_a, err_b


if __name__ == "__main__":
    err_a, err_b = fig_octahedral()
    print(f"max |angle(σ i, gΨ) − angle(i, Ψ)|: random state {err_a:.2e}°, Ψ* {err_b:.2e}°")
    print("wrote", OUT / "d37h_octahedral_symmetry.png")

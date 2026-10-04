"""Figures for D45: Stark packets and the widest band at d = 4 (numpy, mpmath, matplotlib).

Writes docs/figures/d45_widest_band.png and d45_stark_packet.png.

A Stark packet (D45) is ψⱼ = (−i)ʲ φⱼ with φⱼ₊₁ = φⱼ₋₁ + (2(c₀ − j)/z) φⱼ, φ₋₁ = φ_d = 0: the left
half is solved from position 0, the right half from position d − 1, glued at g = ⌊(d − 1)/2⌋ where the
Casoratian vanishes. The packets below use the parameters of the Lean certificates of D45d
(z and the window of the glue offset δ = c₀ − g); δ is located by bisection. Every such packet
is an exact eigenvector of T_d − iλ P_d, saturates Robertson–Schrödinger and moves at
v = 4 Σ (j − c₀)² φⱼ² / (ρ_d z Σ φⱼ²).

Lean (D45d): v ≥ κ = 0.9272 > v*(4) for every d ≥ 5, so ϙ(d) ≤ 0.0728 < ϙ(4).
The values of v*(d) for d ≥ 5 are numerical (D44 figures).

Run:  python3 docs/simulation/figures_widest_band.py
"""

import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf

from figures_threshold_cone import BLUE, INK2, MUTED, ORANGE, OUT, SURFACE, VSTAR4, ops, stats
from figures_velocity_band import vstar_imag

mp.dps = 60
KAPPA = 0.9272

# (z, lower and upper end of u = δ + 1) of the exact certificates, d = 5 … 27 (D45d)
CERTS = {
    5: (7 / 4, 255 / 256, 257 / 256), 6: (2, 145 / 128, 146 / 128),
    7: (2, 255 / 256, 257 / 256), 8: (9 / 4, 245 / 256, 247 / 256),
    9: (5 / 2, 255 / 256, 257 / 256), 10: (5 / 2, 512 / 512, 516 / 512),
    11: (11 / 4, 255 / 256, 257 / 256), 12: (11 / 4, 510 / 512, 514 / 512),
    13: (3, 255 / 256, 257 / 256), 14: (3, 255 / 256, 257 / 256),
    15: (3, 510 / 512, 514 / 512), 16: (13 / 4, 255 / 256, 257 / 256),
    17: (13 / 4, 255 / 256, 257 / 256), 18: (13 / 4, 510 / 512, 514 / 512),
    19: (13 / 4, 510 / 512, 514 / 512), 20: (13 / 4, 510 / 512, 514 / 512),
    21: (13 / 4, 1020 / 1024, 1028 / 1024), 22: (7 / 2, 255 / 256, 257 / 256),
    23: (7 / 2, 255 / 256, 257 / 256), 24: (7 / 2, 255 / 256, 257 / 256),
    25: (7 / 2, 255 / 256, 257 / 256), 26: (7 / 2, 510 / 512, 514 / 512),
    27: (7 / 2, 510 / 512, 514 / 512),
}
TRUNC = (8, 60 / 64, 68 / 64)  # every d ≥ 28


def halves(d, z, c0):
    """The two halves: left from position 0, right from position d − 1 (as in D45)."""
    left, prev = [mpf(1)], mpf(0)
    for j in range(d - 1):
        left.append(prev + 2 * (c0 - j) / z * left[j])
        prev = left[j]
    right = [mpf(0)] * (d + 1)
    right[d - 1] = mpf(1)
    for j in range(d - 1, 0, -1):
        right[j - 1] = right[j + 1] + 2 * (j - c0) / z * right[j]
    return left, right


def packet(d, cert):
    """The certified Stark packet: glue offset by bisection, then φ normalized."""
    z, ulo, uhi = (mpf(x) for x in cert)
    g = (d - 1) // 2

    def cas(delta):
        left, right = halves(d, z, g + delta)
        return left[g] * right[g + 1] - left[g + 1] * right[g]

    a, b = ulo - 1, uhi - 1
    fa = cas(a)
    for _ in range(200):
        m = (a + b) / 2
        if cas(m) * fa > 0:
            a, fa = m, cas(m)
        else:
            b = m
    c0 = g + (a + b) / 2
    left, right = halves(d, z, c0)
    phi = np.array([float(left[j] * right[g] if j <= g else right[j] * left[g])
                    for j in range(d)])
    return phi / np.linalg.norm(phi), float(c0), float(z), g


def speed(d, phi):
    t_op, p_op = ops(d)
    psi = phi * (-1j) ** np.arange(d)
    k, vt, vp, c = stats(t_op, p_op, psi)
    return k * (d - 1) / 2, c / (vt * vp)


def fig_widest_band():
    ds = np.arange(5, 61)
    cert = []
    for d in ds:
        phi, _, _, _ = packet(d, CERTS.get(d, TRUNC))
        v, cos2 = speed(d, phi)
        assert abs(cos2 - 1) < 1e-10 and v >= KAPPA
        cert.append(v)
    num = [vstar_imag(d) for d in ds]
    print("d  certified packet  v*(d)")
    for d, v, w in zip(ds, cert, num):
        print(f"{d:>2}  {v:.5f}  {w:.5f}")

    fig, ax = plt.subplots(figsize=(8.2, 5.0), dpi=150)
    ax.axhspan(VSTAR4, KAPPA, color=ORANGE, alpha=0.12, lw=0)
    ax.axhline(VSTAR4, color=ORANGE, lw=1.4)
    ax.axhline(KAPPA, color=INK2, lw=1.1, ls="--")
    ax.plot(ds, num, "o", ms=5, color=BLUE, mec=SURFACE, mew=1.2,
            label="v*(d), fastest minimum-uncertainty speed (numerical)")
    ax.plot(ds, cert, "o", ms=6, mfc="none", mec=INK2, mew=1.2,
            label="the certified Stark packet of D45d (Lean: ≥ κ)")
    ax.plot([4], [VSTAR4], "o", ms=9, color=ORANGE, mec=SURFACE, mew=2, zorder=5,
            label="v*(4), the widest band (exact, D43)")
    ax.text(60.5, VSTAR4 - 0.0022, "v*(4) = 3(√5 − 1)/4 ≈ 0.9271  (exact, D43)",
            color=INK2, fontsize=10, ha="right", va="top")
    ax.text(60.5, KAPPA + 0.0022, "κ = 0.9272: every d ≥ 5 reaches it (Lean, D45d)",
            color=INK2, fontsize=10, ha="right", va="bottom")
    ax.axvline(27.5, color=MUTED, lw=0.8, ls=":")
    ax.text(16, 1.0035, "exact check, d = 5 … 27", color=MUTED, fontsize=9.5, ha="center")
    ax.text(44, 1.0035, "one truncated check, every d ≥ 28", color=MUTED, fontsize=9.5,
            ha="center")
    ax.set_xlim(3, 61)
    ax.set_ylim(0.914, 1.008)
    ax.set_axisbelow(True)
    ax.set_xlabel("positions per axis  d")
    ax.set_ylabel("speed of a minimum-uncertainty state")
    ax.legend(loc="center right", bbox_to_anchor=(1.0, 0.42), fontsize=9.5)
    ax.set_title("d = 4 has the widest band: ϙ(d) ≤ 1 − κ = 0.0728 < ϙ(4) for every d ≥ 5",
                 loc="left", fontsize=12)
    fig.tight_layout()
    fig.savefig(OUT / "d45_widest_band.png")
    plt.close(fig)


def fig_stark_packet():
    fig, axes = plt.subplots(1, 2, figsize=(10.4, 4.2), dpi=150)
    for ax, d in zip(axes, (8, 41)):
        phi, c0, z, g = packet(d, CERTS.get(d, TRUNC))
        v, _ = speed(d, phi)
        j = np.arange(d)
        colors = [BLUE if k <= g else ORANGE for k in j]
        ax.set_axisbelow(True)
        ax.bar(j, phi ** 2, color=colors, width=0.8)
        ax.axvline(c0, color=INK2, lw=1, ls="--")
        ax.text(c0 + 0.3, max(phi ** 2) * 1.02, f"c₀ = {c0:.4f}", color=INK2, fontsize=9.5)
        ax.set_xlabel("position  j")
        ax.set_title(f"d = {d}, z = {z:g}: v = {v:.4f}", loc="left", fontsize=11.5)
    axes[0].set_ylabel("|ψⱼ|²")
    axes[0].text(0.98, 0.84, "left half (from position 0)", color=BLUE, transform=axes[0].transAxes,
                 fontsize=9.5, va="top", ha="right")
    axes[0].text(0.98, 0.76, "right half (from position d − 1)", color=ORANGE,
                 transform=axes[0].transAxes, fontsize=9.5, va="top", ha="right")
    fig.suptitle("Stark packets: phase −90° per position, width √z, glued where the Casoratian "
                 "vanishes", x=0.02, ha="left", fontsize=12.5)
    fig.tight_layout()
    fig.savefig(OUT / "d45_stark_packet.png")
    plt.close(fig)


if __name__ == "__main__":
    fig_widest_band()
    fig_stark_packet()

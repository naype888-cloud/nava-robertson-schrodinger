"""Monte Carlo error budget for the waveguide test of NRS (docs/EXPERIMENT.md, section 5).

Requires only numpy. Prints Markdown tables: for each array size N and each noise scenario,
the mean and standard deviation over 2000 realizations of

* the Robertson ratio          R_rob = σ_T σ_P / (½ |⟨[T, P]⟩|),
* the Robertson–Schrödinger ratio R_RS = σ_T σ_P / |⟨x, y⟩|,  x = (T − ⟨T⟩)ψ, y = (P − ⟨P⟩)ψ,

the second being `ratioG` of D39. Both equal C_Nava(N) at the ideal ψ*. Noise that creates a
spurious covariance raises R_rob but not R_RS.

Run:  python3 docs/simulation/error_budget.py
"""

import numpy as np

NS = [2, 3, 4, 5, 6, 8, 10]
SAMPLES = 2000

# name: (coupling disorder, SLM phase [deg], SLM amplitude, holography SNR [dB], photons)
SCENARIOS = {
    "coupling 1 %": (0.01, 0.0, 0.0, None, None),
    "coupling 3 %": (0.03, 0.0, 0.0, None, None),
    "phase 2°": (0.0, 2.0, 0.0, None, None),
    "phase 5°": (0.0, 5.0, 0.0, None, None),
    "amplitude 2 %": (0.0, 0.0, 0.02, None, None),
    "holography 30 dB": (0.0, 0.0, 0.0, 30.0, None),
    "10⁴ photons": (0.0, 0.0, 0.0, None, 1e4),
    "realistic": (0.01, 2.0, 0.02, 35.0, 5e4),
    "stressed": (0.03, 5.0, 0.05, 25.0, 1e4),
}


def path_operators(n):
    """T_N = A_N / ρ_N, P_N = diag(−1, …, 1) and ψ*."""
    adj = np.diag(np.ones(n - 1), 1) + np.diag(np.ones(n - 1), -1)
    rho = 2 * np.cos(np.pi / (n + 1))
    j = np.arange(n)
    psi = (-1j) ** j * np.sin((j + 1) * np.pi / (n + 1))
    return adj, rho, np.diag(np.linspace(-1, 1, n)), psi / np.linalg.norm(psi)


def ratios(t, p, psi):
    """(R_rob, R_RS) at the unit state psi."""
    def mean(op):
        return np.vdot(psi, op @ psi).real
    x = t @ psi - mean(t) * psi
    y = p @ psi - mean(p) * psi
    spread = np.linalg.norm(x) * np.linalg.norm(y)
    comm = abs(np.vdot(psi, (t @ p - p @ t) @ psi)) / 2
    return spread / comm, spread / abs(np.vdot(x, y))


def realization(n, rng, coupling, phase, amplitude, snr, photons):
    """One fabricated array, one prepared state, one measured field."""
    adj, rho, p, psi = path_operators(n)
    bonds = 1 + rng.normal(0, coupling, n - 1)
    t = (np.diag(bonds, 1) + np.diag(bonds, -1)) * adj / rho
    psi = psi * np.exp(1j * np.deg2rad(rng.normal(0, phase, n)))
    psi = psi * np.clip(1 + rng.normal(0, amplitude, n), 0.05, None)
    psi /= np.linalg.norm(psi)
    if snr is not None:
        sigma = np.sqrt(np.mean(abs(psi) ** 2) / 10 ** (snr / 10) / 2)
        psi = psi + sigma * (rng.normal(size=n) + 1j * rng.normal(size=n))
        psi /= np.linalg.norm(psi)
    if photons is not None:
        counts = rng.poisson(photons * abs(psi) ** 2)
        jitter = rng.normal(0, 0.5 / np.sqrt(np.maximum(counts, 1)))
        psi = np.sqrt(counts / counts.sum()) * np.exp(1j * (np.angle(psi) + jitter))
    return ratios(t, p, psi)


def main():
    header = "| `N` | ideal | " + " | ".join(SCENARIOS) + " |"
    rule = "|---" * (len(SCENARIOS) + 2) + "|"
    tables = {0: [header, rule], 1: [header, rule]}
    for n in NS:
        adj, rho, p, psi = path_operators(n)
        ideal = ratios(adj / rho, p, psi)[0]
        cells = {0: [], 1: []}
        for k, params in enumerate(SCENARIOS.values()):
            rng = np.random.default_rng(1000 * n + k)
            r = np.array([realization(n, rng, *params) for _ in range(SAMPLES)])
            for i in (0, 1):
                cells[i].append(f"{r[:, i].mean():.4f} ± {r[:, i].std(ddof=1):.4f}")
        for i in (0, 1):
            tables[i].append(f"| {n} | {ideal:.4f} | " + " | ".join(cells[i]) + " |")
    for i, name in ((1, "Robertson–Schrödinger ratio `R_RS`"), (0, "Robertson ratio `R_rob`")):
        print(f"\n{name}\n")
        print("\n".join(tables[i]))


if __name__ == "__main__":
    main()

# Kimura–Mayumi–Ohno–Lee–Chruściński (npj QI 2026) against NRS and det|NRS³|

Paper: *Beyond Robertson–Schrödinger*, arXiv:2504.20404 (v4), npj Quantum Inf. 21 Sep 2026.
Its reference list (98 entries) contains no tight-binding, path-graph, lattice-transport or
Nava–Robertson work; their constant is the Böttcher–Wenzel `2`, not a function of `d`.

## Their relation

For `ρ > 0` with smallest eigenvalues `λ₁ ≤ λ₂`:

`V(A) V(B) ≥ ¼ |⟨[A,B]⟩|² + Cov(A,B)² + λ₁λ₂/(λ₁+λ₂) · ‖[A,B]‖²_ρ`,

an equality for `d = 2` and a plain inequality for `d ≥ 3`.

## Pure states: the new term is zero

A pure state has `λ₁ = 0`, so the new term vanishes and their bound is Robertson–Schrödinger.
NRS and NRS³ live on pure states (the maximal current state of the cube). Nothing in the paper
changes the angle `θ_NRS(d)`, the band `[θ_NRS(4), arccos(1/C∞))`, or saturation only at `d = 2, 3`.

## Qubit: their term is a minor of the Klein factor

`ρ = (1 + w·σ)/2`, `r = |w|`, `A = a·σ`, `B = b·σ` (unit `a`, `b`), `α = a·w`, `β = b·w`, `c = a·b`.
By hand (not in Lean):

- `V(A) V(B) − Cov² = 1 − c² − α² − β² + 2cαβ`
- `¼ |⟨[A,B]⟩|² = ((a × b)·w)² = r²(1 − c²) − α² − β² + 2cαβ`
- difference `= (1 − r²) |a × b|²`, which is `λ₁λ₂/(λ₁+λ₂) · ‖[A,B]‖²` with `λ₁λ₂ = (1 − r²)/4`.

So their equality for qubits is Robertson–Schrödinger plus `(1 − r²)|a × b|²`. The factor
`1 − r² = 4 det ρ` is the one in `det Cov_ρ(σx, σy, σz) = (1 − r²)²` (Klein volume density,
`Physlib/ProbabilisticTheory/Qubit/BlochVolume.lean`, local branch `feat-qubit-pauli-diagonal`):
their term is the pair `(a, b)` projection of that same factor. The real `3 × 3` covariance
`I − w wᵀ` has determinant `1 − r²`; the complex Gram matrix has `(1 − r²)²`.

## What it does not touch

- Not a statement about `T_d : P_d`, transport, or the cube.
- No `d ≥ 3` tightness (the NRS family is the exact pure-state `d ≥ 3` picture).
- Open, not claimed: whether the `λ₁λ₂/(λ₁+λ₂)` term has a det|NRS³| analogue for mixed states on the cube.

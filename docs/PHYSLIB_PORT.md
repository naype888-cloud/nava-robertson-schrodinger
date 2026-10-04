# The Physlib port of NRS and NRS³

This repository proves NRS and NRS³ over Mathlib. In parallel, the results are being contributed
to [physlib](https://github.com/leanprover-community/physlib) (`PhyslibAlpha`), restated on
physlib's own **open tight binding chain**: Hamiltonian `H` (hopping `t`), position `X`
(spacing `a`) and current `J = i(HX − XH)`, the velocity `d⟨X⟩/dt`. The pair `(T_d, P_d)` of
this repository is that chain with `E0 = 0`, `t = −1/ρ_d`, `a = 2/(d − 1)` and `P_d = X − 1`, so each port states
a result of the corpus in the vocabulary of a mainstream physical model.

Every file is Mathlib, Physlib and PhyslibAlpha only, at most 300 lines, lines of at most 100
characters, no `sorry`, only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
and passes every PhyslibAlpha linter. Status on 3 October 2026.

![The Physlib port](figures/physlib_port_ladder.png)

## Pull requests

| PR | File (`PhyslibAlpha/…`; `…/` abbreviates the folder, now `ProbabilisticTheory` for the first four) | Lines | Main results | Corpus | Status |
|---|---|---|---|---|---|
| #1649 | `…/CStarAlgebra/Uncertainty` | +60 | equality in Robertson–Schrödinger iff the Gram defect vanishes | `D1`, `D2` | merged |
| #1650 | `…/CStarAlgebra/Uncertainty` | +20 | normalized variance bounds for algebraic states | `D2` | merged |
| #1660 | `…/HilbertSpace/State/VectorUncertainty` | 69 | variance and Gram defect of vector states | `D21` | merged |
| #1676 | `…/HilbertSpace/State/DensityUncertainty` | 107 | Robertson–Schrödinger for density states | `D2` | merged |
| #1689 | `CondensedMatter/TightBindingChain/OpenBoundary` | 145 | open chain, position, `⟨m|[A, X]|n⟩ = a(n − m)⟨m|A|n⟩` | `D3` | merged |
| #1690 | `…/TightBindingChain/Uncertainty` | 95 | energy–position uncertainty, `⁅H, X⁆` moves one site | `D3`, `D21` | merged |
| #1695 | `QuantumMechanics/HilbertSpaces/FiniteTarget/Operators` | 47 | `SelfAdjointDecompose` on operators of `𝓗[d]` | — | merged |
| #1696 | `…/TightBindingChain/Current` | 112 | current `J`, stationary and localized states carry none | `D38` | merged |
| #1699 | `…/FiniteTarget/Product` | 176 | operators on one coordinate of `𝓗[α × β]` commute across coordinates | `D37` | merged |
| #1708 | `…/TightBindingChain/CurrentEigenstates` | 180 | `J ψ_k = 2at cos(kπ/(N+1)) ψ_k`, `‖ψ_k‖² = (N+1)/2` | `D5`, `D6` | merged |
| #1709 | `…/TightBindingChain/Uncertainty` | 93 (refactor) | the uncertainty relation on the chain's own Hilbert space | — | merged |
| #1716 | `…/TightBindingChain/MaxCurrentState` | 298 | maximal current state; `⟨H⟩ = E0`, `⟨X⟩ = a(N−1)/2`, `⟨⁅H, X⁆⟩ = −at cos(π/(N+1))` | `D5`, `D21` | merged |
| #1718 | `…/TightBindingChain/Saturation` | 216 | Robertson–Schrödinger is an equality iff `N = 2, 3`, strict for `N ≥ 4` | `D23` | merged |
| #1723 | `…/TightBindingChain/ElementalUncertainty` | 144 | `Cov = 0`; `Var H · Var X = (at cos)² + defect`; `CNava ≥ 1`, `= 1` iff `N = 2, 3`; `nava_robertson_schrodinger_elemental_dimensional_uncertainty_inequality` | `D21`, `D22` | open |
| #1717 | `…/FiniteTarget/ProductState` | 236 | product states: one-coordinate statistics are the factor's | `D37` | merged |
| #1725 | `…/TightBindingChain/Cube` | 265 | the open cube; axes commute; `C_Nava` per axis; `nava_robertson_schrodinger_cube` | `D37` | open |
| #1711 | `…/TightBindingChain/MandelstamTamm` | 139 | `|⟨J⟩| ≤ 2 ΔH ΔX` (Mandelstam–Tamm), `⟨J⟩²/Var X ≤ 4 Var H` (Cramér–Rao) | `D41` | merged |
| 17 | `…/TightBindingChain/MandelstamTammMaxCurrent` | 126 | the ratio is `1/C_Nava²`, `= 1` iff `N = 2, 3`; per axis of the cube | `D41` | ready |
| #1724 | `…/TightBindingChain/SpeedLimit` | 218 | orthonormal basis of current eigenstates; `⟨J⟩ = 2at cos(π/(N+1))` in the maximal current state; `|⟨J⟩| ≤ 2|at| cos(π/(N+1))` in every state | `D38`, `D40` | open |
| 19 | `…/TightBindingChain/VelocityBand` | 172 | minimum-uncertainty vectors are compact; the threshold `v*` is attained; forced defect in `Ϙ` | `D44` | ready |
| 20 | `…/TightBindingChain/VelocityBandWidth` | 266 | time reversal; `v* < maxCurrent` and `Ϙ ≠ ∅` for `N ≥ 4` | `D44`, `D46` | ready |
| 21 | `…/TightBindingChain/MaxCurrentVariances` | 249 | `Var H = 4t² sin²θ (N−1)/(N+1)`, `Var X = a²(((N+1)²+2)/12 − 1/(2 sin²θ))`, `θ = π/(N+1)`; `C_Nava²` in closed form (`CNava_sq_eq`) | `D19`, `D20` | ready |
| 22 | `…/TightBindingChain/LongChainLimit` | 108 | `C_Nava → √(π²/3 − 2)` along any family of chains with `N → ∞` (`tendsto_CNava`); the limit is `> 1` | `D8` | ready |
| 23 | `…/TightBindingChain/LongChainMonotonicity` | 297 | `C_Nava` strictly increasing in `N` from four sites on (`CNava_lt_CNava`); `C_Nava < √(π²/3 − 2)` | `D9` | ready |
| 24 | `ProbabilisticTheory/CStarAlgebra/Uncertainty` | +217 | Robertson 1934 for several observables: `Σ + iΩ` is a Gram matrix (`gram_centeredGNSVector`), `\|det Ω\| ≤ det Σ` for every state on a C*-algebra (`robertson_det`) | `D49` | ready |
| 25 | `…/TightBindingChain/Cube` (E–F) | +319 | the six observables `(H, X)` of the cube: `Ω` block diagonal in every state, `(⟨⁅H,X⁆⟩_x ⟨⁅H,X⁆⟩_y ⟨⁅H,X⁆⟩_z)² ≤ det Σ` (`robertson_det_cube`); at the maximal current state `det Σ = (C_Nava(x) C_Nava(y) C_Nava(z))² \|det Ω\|`, strict from `4 × 4 × 4` (`robertson_det_maxCurrentCubeState_strict`) | `D49b`, `D49c` | ready |

## Order of submission

At most three pull requests are open at a time; each wave goes up when the previous one is
merged. The dependencies are those of the `import` lines.

| Wave | Pull requests | Depends on |
|---|---|---|
| 0 | #1695, #1696, #1699 | merged work |
| 1 | 8, 9, 14 | #1696; #1695; #1699 |
| 2 | 10, 16 | 8, 9; #1696, 9 |
| 3 | 11, 18 | 10; 10, 16 |
| 4 | 12 (NRS), 19 | 11; 11, 18 |
| 5 | 15 (NRS³), 20, 21 | 12, 14; 19, #1699; 12 |
| 6 | 17 (Mandelstam–Tamm, Cramér–Rao), 22 | 15, 16, 18; 21 |
| 7 | 23 (monotonicity) | 22 |
| any | 24 (Robertson 1934) | master |
| after 15 | 25 (det\|NRS³ on the cube) | 15, 24 |

## det|NRS³ (PR 24 and after)

PR 24 brings Robertson's 1934 relation for several observables to the algebraic states of
`PhyslibAlpha`, in the file of Robertson–Schrödinger. In this repository the same bound is
`D49`, and its instances on the cube are `D49b`–`D49d`: the three conjugate pairs give
`det Σ ≥ (t_x t_y t_z / 8)²` for every state, the ratio is `C_Nava(dx)² C_Nava(dy)² C_Nava(dz)²` at
`Ψ*`, and the bound is strict for product states in the band `Ϙ`. PR 25 ports `D49b` and the
`Ψ*` part of `D49c` to the open cube (branch `feat-physlibalpha-tight-binding-cube-determinant`,
two commits of 138 and 181 lines on #1725 and PR 24). The band part (`D49d`) waits for PRs 19
and 20.

## Round C: shorter than the corpus (PRs 21–23)

The corpus reaches `C_Nava < C_∞` through `D19` and `D20` (the closed form, 1142 lines) and `D8`,
`D9` (limit and monotonicity, 1248 lines). The port needs 654 lines in three files, for two
reasons.

* **One sum at a root of unity.** The position variance of the maximal current state rests on
  `∑ j < n, (j − n/2)² cos(2jθ) = n/(2 sin²θ)` with `n = N + 1`, `θ = π/n`. Summation by parts
  against the powers of `z = e^{2iθ}`, a root of unity of order `n`, gives
  `∑ j < n, (j − n/2)² zʲ = −2nz/(z − 1)²`, which is real and equal to `n/(2 sin²θ)`. The
  weighted root, period and angle sums of the earlier series are not needed.
* **A certificate in one variable.** `D9` bounds the remainder of the derivative of `C_Nava²` by a
  Bernstein certificate in two variables `(x/π, π)` of degree `(12, 12)`: 169 terms and
  `maxHeartbeats 4000000`. Written in `x = π/(N + 1)` the remainder has degree three in `π`;
  with `3.141592 < π < 3.141593` each power of `π` is bounded by the sign of its coefficient, and
  what is left is one polynomial of degree twelve in `x ∈ [0, 1571/2500]` whose thirteen
  Bernstein coefficients are negative (the largest is `≈ −1169`). The file builds with the
  default heartbeats. The positivity `C_Nava > 1` for `N ≥ 4` (the Taylor half of `D8`) is not
  ported: it is the Gram defect of PRs 11 and 12.

## A new proof that the band is open (PR 20)

`D44` shows `ϙ(d) > 0` for `d ≥ 4` through the explicit width of `D23b`–`D23d`. PR 20 proves
`Ϙ ≠ ∅` without it: time reversal `Θ` (complex conjugation) commutes with `H` and `X`, reverses
`J` and keeps the defect; the extremes `±maxCurrent` of the current are simple, with eigenvectors
the maximal current state `ψ₁` and `ψ_N = Θψ₁`; a unit vector at the speed limit is a phase times
one of them, so it carries the defect of `ψ₁`, positive from four sites on; the threshold `v*` is
attained (compactness), hence `v* < maxCurrent`. The explicit width stays in `D23d`.

![The band is open from four sites on](figures/physlib_band_time_reversal.png)

Script for both figures: `docs/simulation/figures_physlib_port.py`.

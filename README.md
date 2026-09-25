# Nava–Robertson–Schrödinger Elemental Dimensional Uncertainty Inequality

Independent Lean 4 verification package prepared by Eduardo Nava Hernández for
external academic review. The package is self-contained at the project level:
Lake fetches the exact Mathlib and physlib revisions recorded in
`lake-manifest.json`; it does not depend on the BACQM source tree.

## License

[NRS Noncommercial License 1.0.0](LICENSE) — free for noncommercial,
academic, humanitarian and public-institution use, and free to reuse as a
contribution to any open source formal-verification project (Mathlib,
Physlib, Lean 4, or any other). Incorporating this software or its output
into a proprietary/commercial product requires a separate commercial
license — see [LICENSE](LICENSE) §4.

The package is a single layer: the theorem, over Mathlib, no constant,
no unit, no physical input. `PhyslibBridge` additionally imports physlib's
algebraic uncertainty framework to show that the inequality at `ψ*` is
physlib's `robertson_schrodinger`, instantiated. Nothing in it depends on a choice of physical
interpretation.

| Layer | Build target | What it is | Status |
|---|---|---|---|
| **Mathematics** | `NavaRobertsonIndependent.Mathematics` | The theorem, over Mathlib (plus physlib in `PhyslibBridge`). No constant, no unit, no physical input. | Lean theorems. |

This is checked, not just stated: `Verification/Layer1_Mathematics.lean`
computes the import closure of the package and fails if it contains a
module outside `NavaRobertsonIndependent.Mathematics`.

## Reproduce the verification

Requirements: Git, Elan, and network access for the first dependency download.

```bash
lake update
lake exe cache get   # downloads prebuilt Mathlib; without it Mathlib is compiled from source
lake build           # the whole package
lake build NavaRobertsonIndependent.Mathematics   # same target, explicit
lake env lean Verification/Layer1_Mathematics.lean    # boundary + axioms
```

The pinned toolchain is Lean `v4.34.0`; Mathlib is pinned to tag `v4.34.0` and
physlib to commit `1c81053a2ec6542f0de013c163e5db5091cf5b3c`. All headline theorems depend only
on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`;
the package has no `sorry`.

### Separate target: `NavaRobertsonCertificados`

Not built by `lake build`. It contains `D23g`: every minimum-uncertainty state of `H₄`
(Robertson–Schrödinger saturated) carries tension at most `1/φ = (√5 − 1)/2`
(`CotaMinimaIncertidumbreCuatro.tension_le_of_satura`). With `D23f`, which exhibits a state
attaining it, `1/φ` is the maximum: `3(√5 − 1)/4 ≈ 92.7 %` of the maximal tension `2/3`.
The proof reduces the claim to an inequality on the densities `|ψⱼ|²` (link currents plus
Cauchy–Schwarz) and closes it with two exact rational Positivstellensatz certificates
(`CotaCasoA`: 207 weighted squares, `CotaCasoB`: 229), found by semidefinite programming,
rounded to exact rationals and checked by `ring`. `CotaCasoA` is a 1 MB polynomial identity,
so this target takes about 20–30 minutes:

```bash
lake build NavaRobertsonCertificados
lake env lean Verification/Certificados.lean          # axioms
```

## The theorem

The Nava–Robertson–Schrödinger Elemental Dimensional Uncertainty Inequality for
the pair `(T_d, P_d)` on the path graph with `d` vertices, on `H_d = ℂ^d`. At the
state of maximal tension `ψ*`, the Robertson–Schrödinger gap is
`(c/2)² δ_geom (2 + δ_geom)` with `δ_geom(d) = C_Nava(d) − 1`; it vanishes
exactly for `d ∈ {2, 3}` and is strictly positive for `d ≥ 4`. For `d ≥ 4`,
`δ_geom` is strictly increasing, with global minimum `δ_geom(4)` and strict upper
bound `δ_∞ = C_∞ − 1`, where `C_∞² = π²/3 − 2`.

- `D0`–`D14`: Hilbert-space setup, Cauchy–Gram and Robertson inequalities,
  finite-path operators, Fiedler/Niven obstruction, Szegő limit, monotonicity,
  and certificates.
- `D16_TransporteSuperficieCerrada`: finite-sum transport to a closed
  orientable surface, including `Ω(Σ_g) = 2g · δ∞` and its radical form. The
  per-cycle defect `δ∞` and `b₁ = 2g` are inputs of the definition, not theorems.
- `D25_CuantoDimensional`: the quantum is dimensional. `cuantoDim d = δ_geom(d)`
  is zero exactly for `d ∈ {2, 3}` (`sin_cuanto_en_d3`), positive and strictly
  increasing from `d = 4`, below `δ∞` and converging to it (`cuanto_dimensional`).
- `D26a_OmegaDesdePi`: `omegaPi = (1 − 1/C∞)·e^{−1/C∞} = 0.04954367888809…`, a
  function of `π` only, with `0.049543679` certified as its 9-digit rounding
  from both sides (`decimal_desde_pi`).
- `SumInvSinSq`: the finite cosecant-square identity
  `Σ csc²(kπ/N) = (N²−1)/3` through Chebyshev roots, with the cotangent
  corollaries (v14: the former duplicate `D15` was removed).
- `D17_DefectoIntrinsecoTransporte`: observer-free algebraic interface for any
  position–transport dynamics realizing `(T_d, P_d)`; for `d ≥ 4`, its
  Robertson–Schrödinger defect is strictly positive.
- `D19_VarianzaPosicionFiedler`, `D20_EscalonGramCNava`: closed-form variances
  of `T_d` and `P_d` at the extremal state `ψ*` (the explicit Fiedler mode with
  phase `(−i)^j`) and the Gram step `(d−1)² ‖T_d ψ*‖² ‖P_d ψ*‖² = C_Nava(d)²`,
  with Gram defect `(C_Nava(d)² − 1)/(d−1)²`, equal to zero exactly for
  `d ∈ {2, 3}`.
- `D21_ElementalNRSInequality`: the inequality for the concrete operators
  `(T_d, P_d)`. At `ψ*`: `cov = 0`, `Var T · Var P = (c/2)² (1 + δ_geom)²` with
  `c = −2/(d−1)`, and the Robertson–Schrödinger gap equals
  `(c/2)² δ_geom (2 + δ_geom)`. The top eigenvalue `2/(d−1)` of
  `K_d = i[T_d, P_d]` is simple, so every unit state with `⟨K_d⟩ = 2/(d−1)` is a
  phase of `ψ*` and the strict inequality holds at every such state.
- `D22_InstanciaPosicionTransporteTdPd`: the interface `PosicionTransporte d` of
  `D17` instantiated with the concrete operators `(T_d, P_d)`; its saturation
  field is a theorem, and the intrinsic defect equals the Gram defect of `D20`.
- `D23_SaturacionAutovectores`: Robertson–Schrödinger is an inequality and equality
  is allowed. On vectors of `Hd d`, the Gram defect vanishes iff `Var B = 0` or
  `Ãψ = c • B̃ψ`; every unit eigenvector of `A − iλB` (`λ` real, `A`, `B` symmetric)
  has `cov = 0` and `Var A · Var B = Im²`. For `d ≥ 4`, no unit eigenvector of
  `T_d − iλP_d` is a maximal-tension state (`⟨K_d⟩ = 2/(d−1)`), the states where
  `D21` gives the strict inequality. In every state with transport, `⟨K_d⟩ ≠ 0`,
  the uncertainty is strictly positive (`Var T · Var P ≥ ⟨K_d⟩²/4 > 0`); the only
  vectors with zero product are those with `⟨K_d⟩ = 0`, such as the canonical basis
  vectors, although `T_d` and `P_d` do not commute. Mathlib-only port of the Physlib
  module `UncertaintySaturation` to vector states.
- `D24_BrechaCuatroAsintota`: the pure gap `Δ = C_∞ − C_Nava(4) = δ_∞ − δ_geom(4)`
  between the first open dimension and the Szegő limit. It is positive, strictly
  below `δ_∞`, strictly bounds the rise of the defect from `d = 4`
  (`δ_geom(d) − δ_geom(4) < Δ`), and is the exact limit of that rise
  (`C_Nava(d) − C_Nava(4) → Δ`). A corollary of `D8` and `D9`; it depends only on
  `π`.

- `D28_CurvaturaBakryEmery`: the discrete Bakry-Émery curvature of the
  interior of the path graph satisfies `CD(0,2)`, sharp, via an exact
  polynomial identity (the discrete Bochner-Weitzenböck formula,
  `gamma2_eq_bochner`). Neither the curvature lower bound `0` nor the
  effective dimension `2` can be improved: both are witnessed by explicit
  counterexamples (`kappa_cero_no_mejorable`, `n_dos_no_mejorable`). Ties back
  to `D3`'s actual graph edges via `adj_im1`/`adj_ip1`, not an unconnected toy.
- `D28b_CurvaturaOllivier`: the same conclusion, `κ = 0` on the interior,
  from the independent Ollivier-Ricci notion, computed via the
  Kantorovich–Rubinstein dual characterization worked out directly (upper
  bound from the Lipschitz property, lower bound from an explicit witness;
  no Mathlib optimal-transport machinery invoked, to keep the module
  self-contained). `convergencia_bakry_emery_ollivier` records that the two
  independent discrete-curvature notions agree exactly on a real edge of
  `GrafoTP d`.

  Together, `D28`/`D28b` are a negative result, not a bridge: the interior of
  the path graph that the whole package is built on (`D3.CanalPreFuerza`, the
  only graph compatible with locality and completeness) carries no curvature
  to extract, by either standard discrete notion. Any hypothesis coupling a
  physical stretching factor to a curvature measured on `T_d:P_d` gets
  nothing from the graph itself; no such hypothesis is part of this package.

The word "quantum" in `D11_CuantoMinimoArea` means the algebraic quantum
`δ_geom(4)²`, a pure number. This package attaches no physical scale, no SI
unit and no constant to it.

## Scope of the formal claims

The finite-path, non-saturation, monotonicity, asymptotic, cosecant and
closed-surface statements are formal mathematical theorems in Lean, with no
input beyond Mathlib. The Cauchy–Gram and Robertson–Schrödinger inequalities
are proved in `D1_CauchyGram` and `D2_Robertson` (including the bridge from
any two vectors of a complex Hilbert space, `evaluacionSchrodingerDeGram`).

`T_d:P_d` is not one graph picked among others: `D3.CanalPreFuerza` proves
that any channel satisfying ordered locality (no step skips a neighbor) and
completeness (no minimal step is missing) is forced to be exactly
`SimpleGraph.pathGraph d`. `pathGraph` is the Mathlib name for that unique
object, not a diagram chosen for illustration.

Physical, cosmological and observer/measurement readings of this theorem are
out of scope for this repository; only the mathematics is claimed here.

The root module `NavaRobertsonIndependent.lean` imports
`NavaRobertsonIndependent.Mathematics` and is the single verification target
for the complete package.

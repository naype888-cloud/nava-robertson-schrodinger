# Nava–Robertson–Schrödinger Elemental Dimensional Uncertainty Inequality

Independent Lean 4 verification package prepared by Eduardo Nava Hernández for
external academic review. The package is self-contained at the project level:
Lake fetches the exact Mathlib revision recorded in `lake-manifest.json`; it does
not depend on PhyslibAlpha or on the BACQM source tree.

## License

[NRS Noncommercial License 1.0.0](LICENSE) — free for noncommercial,
academic, humanitarian and public-institution use, and free to reuse as a
contribution to any open source formal-verification project (Mathlib,
Physlib, Lean 4, or any other). Incorporating this software or its output
into a proprietary/commercial product requires a separate commercial
license — see [LICENSE](LICENSE) §4.

The package is organised in layers that do not mix. Each layer says what it
proves and what it assumes.

| Layer | Build target | What it is | Status |
|---|---|---|---|
| **1. Mathematics** | `NavaRobertsonIndependent.Mathematics` | The theorem, over Mathlib only. No constant, no unit, no physical input. | Lean theorems. |
| **2. Physics: registration floors and quanta** | `NavaRobertsonIndependent.Physics` | The physical reading of Layer 1. Depends on Layer 1. | Lean theorems anchored in the SI/CODATA constants (`c`, `h`, `k_B`, `l_P`); hypotheses stated in the signatures where used. |
| **3. Cosmology** | `NavaRobertsonIndependent.Cosmology` | A cosmological reading (`Ω_b`). Depends on Layers 1–2. | Lean theorems (inequalities and a certified numerical enclosure); the cosmological identification is the claim of this layer. |
| **4. Ontology** | `NavaRobertsonIndependent.Ontology` | Observer, measurement, measurable existence. Depends on Layer 1 only. | Declared postulates (structures in the signatures) and theorems conditional on them. |

No lower layer imports a higher one, and Layer 4 does not import Layers 2–3.
This is checked, not just stated: each file `Verification/LayerN_*.lean` computes
the import closure of its layer and fails if it contains a forbidden module.

## Reproduce the verification

Requirements: Git, Elan, and network access for the first dependency download.

```bash
lake update
lake exe cache get   # downloads prebuilt Mathlib; without it Mathlib is compiled from source
lake build           # the whole package
lake build NavaRobertsonIndependent.Mathematics   # Layer 1 alone
lake env lean Verification/Layer1_Mathematics.lean    # Layer 1 boundary + axioms
lake env lean Verification/Layer2_Physics.lean # Layer 2 boundary + hypotheses + axioms
lake env lean Verification/Layer3_Cosmology.lean     # Layer 3 boundary + axioms
lake env lean Verification/Layer4_Ontology.lean      # Layer 4 boundary + postulates + axioms
```

The pinned toolchain is Lean `v4.33.0`, and Mathlib is pinned to commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. All headline theorems depend only
on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`;
the package has no `sorry`.

## Layer 1 — Mathematics

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
- `ForMathlib/SumInvSinSq`: the finite cosecant-square identity
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
`δ_geom(4)²`, a pure number. The physical scale attached to it lives in Layer 2.

## Layer 2 — Physics: registration floors and quanta

Build target `NavaRobertsonIndependent.Physics`. It reads Layer 1 in
physical units. The spectral network `T_d:P_d` is space itself, the finest
structure the algebra allows; this layer gives its step and its tick in SI units.

Anchored in the SI/CODATA constants used by all of physics:

- the exact SI values of `c`, `h` and `k_B`, and the Planck length `l_P`
  (CODATA 2022);
- `Ω_b = 0.049543679`, which is not a fitted input: `D26a` (Layer 1) proves it is
  `g_s·e^{−1/C∞}`, a function of `π` only, rounded to 9 digits
  (`LimiteSubPlanckiano.Omega_b_desde_pi`, enclosure `< 2.3×10⁻⁹` relative).

Hypotheses stated in the signatures of the theorems that use them:

- H1, the spectral ceiling `ΔH ≤ E_P/(2y)` (`DispersionAdmisible`);
- for the gravitational identities, `G > 0` and `RelacionPlanckNewton`;
- for the time-dilation mechanism, `HCurvaturaConteo` (`D32`).

**2.1 Registration floors**

- `Physics/SubPlanckianLimit`: `Lsbpk`, `Asbpk`, `Vsbpk`, `Tausbpk`,
  `ySbpk`, and `Omega_b_desde_pi`.
- `Physics/SchwarzschildCollapse`: SI constants, Planck energy, collapse-energy
  identity under the Planck–Newton relation.
- `Physics/TimeEnergyRegistrationClosure`: the tick `n·τ_sbpk`, the energy
  scales `y²E_P < (y/2)E_P < E_P < E_P/y`, the Mandelstam–Tamm floor under H1,
  and the operational-reach theorem.
- `Physics/MaximumSpeed`: `k` admissible cell steps cost `≥ k` ticks; the
  mean velocity is `≤ c` and the maximal process attains it.
- `Physics/ElementalCellStep`: the elementary step has length
  `√Ω_b · l_P · δ(d)`; at `d = 4` it is `Lsbpk`, and for every `d ≥ 4` it lies in
  `[Lsbpk, longitudPasoInf)`.

**2.2 The quantum is dimensional, in units**

- `Physics/PhysicalDimensionalQuantum`: each `H_d` has its step and its tick
  `tickDim d = longitudPaso d / c`; `τ_sbpk` is the minimum over every open
  dimension (`Tausbpk_le_tickDim`), and the traversal speed is exactly `c` in
  every dimension (`velocidad_recorrido`).
- `Physics/DimensionalMassGap`: the Robertson gap `δ(d)` in mass units.
  `saltoMasaSbpk` equals the Schwarzschild mass on `Lsbpk` and
  `(1/2)·δ(4)·√Ω_b·M_P`; for every `d ≥ 4` the mass jump is positive, has floor
  at `d = 4`, stays below its ceiling and does not collapse in the limit
  (`salto_masa_no_colapsa_OK`). No Yang–Mills theory is formalized; the
  "mass gap" reading is interpretation.

**2.3 Time: more cells, not a bigger cell**

- `Physics/MoreCellsMoreTime`: a path of more minimal cells is longer and
  takes strictly more minimal time, at the same speed `c`.
- `Physics/D32_WhyTimeGrows`: why time grows where space curves. The
  cell does not curve; curvature adds cells (`HCurvaturaConteo`), and each cell
  costs a tick. Every admissible process along the curve takes strictly longer
  (`curva_tarda_mas`), and at maximal speed the time ratio is exactly `k₁/k₀`
  (`tiempo_proporcional_al_conteo`, `por_que_crece_el_tiempo`). Gravity and
  Einstein's equations are not derived; given the counting hypothesis, the
  theorem gives why and how much.

**2.4 Physical support**

- `Physics/PhysicalSupportR4`: the physical support is a bounded, discrete,
  finite subset of `ℝ⁴` (`soporte N = {k·Lsbpk : |k| ≤ N}⁴`). The theorems of
  `ℝ⁴` restrict to it (`teoremas_de_R4_se_restringen`); the continuum does not:
  every convergent sequence is eventually constant, registered times are
  countable (`registrados_ne_continuo`), none falls in `(0, τ_sbpk)`, and a
  capped eon is finite.

## Layer 3 — Cosmology

Build target `NavaRobertsonIndependent.Cosmology`. It uses Layers 1–2 and is
imported by neither. The cosmological number is `Ω_b = 0.049543679`, proved in `D26a`
(Layer 1) to be `g_s·e^{−1/C∞}`, a function of `π` only; Planck 2018 measures
`Ω_b ≈ 0.049`, within its error. This layer gives the baryonic reading.

- `D26_BaryogenesisEspejo`: a self-contained Szegő-limit computation
  (`C∞ = √(π²/3−2)`, `g_s = 1−1/C∞`, a Boltzmann factor `e^{−1/C∞}`) with
  rational bounds (`Cinf_lt_115`, `gs_lt`) and a spectral-mirror identity
  (`espejo_espectral`, `cos(π−x)=−cos(x)` on the path-graph spectrum). The
  numerical agreement with the documented `Ω_b` decimal is certified in
  `D26b`, not here.
- `D26b_EncierroOmegaB`: certifies, in Lean, what `D26` explicitly left as
  future work — the distance is enclosed on both sides,
  `1.11×10⁻¹⁰ < Ω_b − g_s·e^{−1/C∞} < 1.12×10⁻¹⁰` (`omegaBar_distancia_gt`,
  `omegaBar_encierro`), i.e. `< 2.3×10⁻⁹` relative, via `π` to 20 digits
  (`pi_gt_d20`/`pi_lt_d20`), `C∞` enclosed to 13 digits, and
  `Real.exp_bound`'s Taylor remainder at `n=16`. The previously quoted
  `2×10⁻⁹` relative was a round-down of the true distance (`≈ 2.26×10⁻⁹`)
  and is not provable as an upper bound; the documented decimal is the
  9-digit rounding of `g_s·e^{−1/C∞} = 0.04954367888809…`.

## Layer 4 — Ontology

Build target `NavaRobertsonIndependent.Ontology`. It rests on Layer 1 only (no
physical constant, no cosmology) and nothing imports it. Its structures are
postulates stated in their own signatures.

- `D29_ObservadorMedicionEspectral`: a **declared postulate** (stated as
  such in the structure's own signature, not derived) that a measurement
  is an independent 1D channel distinct from the measured one, registering
  the already-proved real spectrum of `A_d` (`D6`). No auto-measurement is
  possible (`no_auto_medida`).
- `D30_CuentaDistincionCuatroCanales`: a **theorem**
  (`cubo_medido_es_cuatro_canales`): a triple of channels with a genuine,
  distinct observer is a four-channel object, not three, by the same
  postulate.
- `D31_BandaExistenciaMedible`: repackages `D9`+`D24`+`D30` with no new
  proof step, into one theorem per docstring claim. Read its conjuncts as
  independent facts bundled together, not as one implying the other — its
  `4 ≤ d` hypothesis is supplied independently of the measurement data,
  not derived from it, despite the docstring's causal-sounding prose.
- `D33_FaseToroThick`: two phases. The seed has thick/defect `0`; in the torus,
  thick is exactly `ENNReal.ofReal (δ_geom(d))`. It is positive and finite in
  the rupture regime `d ≥ 4` (`toro_entre_cero_e_infinito`), and a nonzero thick
  forces the torus (`sin_cero_absoluto_implica_toro`). The temperature reading
  is explicitly an interpretation of this same model datum, not a thermodynamic
  theorem.
- `D34_RegistroEonAbierto`: the registration hypothesis, with mathematical
  content in every field: a nonzero thick (`D33`), rupture of the path
  (`D13`; this field is the declared postulate "an open eon requires
  elementary dynamics with defect"), and at each tick a real spectral
  measurement (`D29`). Derived, not assumed: the phase is the torus,
  `4 ≤ d` (from the rupture), every reading `2·cos θ` lies strictly in
  `(−2, 2)`, the observer is never the measured channel, and the defect lies
  in the band `δ_geom(4) ≤ δ_geom(d) < δ_geom(4) + Δ` of `D31`, never `0`
  (`cierre_eon_abierto`). The defect depends on `d` only, not on the readings:
  the dynamics fixes it, the observer registers it. Satisfiable with genuine
  spectral readings (`registro_satisfacible`), not with `True` fields.
- `D35_PuenteBanachHilbertAB`: makes the conversation's Banach-to-Hilbert
  bridge explicit. A model-specific relational reading factors through the
  distance `q(A,B)`; H3 carries three spatial coordinates and H4 appends `q` as
  a relational coordinate. D13 gives the first rupture at `d=4`, which
  activates the torus in this model. It also represents each seed's three
  fermions and budget at one point, two distinct complete finite eons, and
  finite or infinite discrete populations of eons. The q-factorization and
  coordinate embedding are stated model rules, not universal consequences of
  the definition of a Banach space. v14 generalizes to `H(3+1+k)` (three axes, `q`,
  and `k` further independent observables; `H4` is `k = 0`), adds the thermal
  route `sin_cero_absoluto_abre_ruptura` (nonzero thick ⇒ torus, `d ≥ 4`,
  rupture of `T_d:P_d`, via `D20`/`D21`/`D13`), and the closing theorem
  `distincion_cancela_cero_e_infinito`: in `H3` without distinction absolute
  zero is admissible; once B is distinguished from A, for every `k` the thick
  at `d = 3+1+k` equals `δ_geom(d)`, is positive and finite, and lies in the
  `D31` band — adding axes never returns it to `0` nor sends it to `∞`.

- `D36_SemillaYRegistroH4`: the seed `d = 3` saturates (`C_Nava(3) = 1`, no
  quantum) but is never registered (`d3_satura_pero_no_se_registra`); in `H₄`
  smoothness without quantum is impossible
  (`suavidad_sin_cuanto_imposible_en_H4`).

## Annex — superseded modules (outside the four layers)

Build target `NavaRobertsonIndependent.Superseded`. Kept compiling for traceability;
no layer imports it, and the verifiers fail if one does.

- `D27_DeformacionTiempo`, `D27b_CurvaturaAcoplamiento`: assumed the cell
  stretches with matter. Superseded by cell counting (`D32`).
- `Constructor_Pinza_Asub_DeltaInf_NoContinuo_Fisico`,
  `D18_PhysicalNonContinuumInstantiated`: replaced by `Physics/PhysicalSupportR4`.
- `DefectoInfinitoRobertsonClay2026` was removed in v14 (tautological; its
  content is proved in `D8`, `D9`, `D10`, `D25`).

## Scope of the formal claims

The finite-path, non-saturation, monotonicity, asymptotic, cosecant and
closed-surface statements of Layer 1 are formal mathematical theorems in Lean,
with no input beyond Mathlib. The Cauchy–Gram and Robertson–Schrödinger
inequalities are proved in `D1_CauchyGram` and `D2_Robertson` (including the
bridge from any two vectors of a complex Hilbert space,
`evaluacionSchrodingerDeGram`).

The SI and physical bridge modules of Layer 2 deliberately expose their
additional inputs. Thus the package does not present dimensional physical
interpretations as consequences of the Robertson–Schrödinger inequality alone.

The numerical minimal registrable time `Tausbpk = ℓ_sub · ℓ_P / c` (about
`1.0174 × 10⁻⁴⁶ s`) has these inputs: `δ_geom(4)` (internal, from `π`), the
baryonic fraction `Ω_b` (documented decimal), the CODATA-2022 Planck length and
the exact SI value of `c`.

The root module `NavaRobertsonIndependent.lean` imports the four layers and is
the single verification target for the complete package.

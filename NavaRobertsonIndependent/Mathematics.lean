import NavaRobertsonIndependent.Mathematics.D0_Habitat
import NavaRobertsonIndependent.Mathematics.D1_CauchyGramInequality
import NavaRobertsonIndependent.Mathematics.D2_Robertson
import NavaRobertsonIndependent.Mathematics.D3_PathGraph
import NavaRobertsonIndependent.Mathematics.D4_WhyNotDiagonal
import NavaRobertsonIndependent.Mathematics.D5_MaximalTension
import NavaRobertsonIndependent.Mathematics.D6_Fiedler
import NavaRobertsonIndependent.Mathematics.D7_Niven
import NavaRobertsonIndependent.Mathematics.D8_Szego
import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
import NavaRobertsonIndependent.Mathematics.D10_Certificate
import NavaRobertsonIndependent.Mathematics.D11_MinimalAreaQuantum
import NavaRobertsonIndependent.Mathematics.D12_FiniteScalarCommutator
import NavaRobertsonIndependent.Mathematics.D13_FirstCombinatorialRupture
import NavaRobertsonIndependent.Mathematics.D14_SzegoGapExcess
import NavaRobertsonIndependent.Mathematics.SumInvSinSq
import NavaRobertsonIndependent.Mathematics.D16_ClosedSurfaceTransport
import NavaRobertsonIndependent.Mathematics.D16b_GaussBonnetBridge
import NavaRobertsonIndependent.Mathematics.D17_IntrinsicTransportDefect
import NavaRobertsonIndependent.Mathematics.D19_FiedlerPositionVariance
import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality
import NavaRobertsonIndependent.Mathematics.D22_TransportPositionInstanceTdPd
import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation
import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap
import NavaRobertsonIndependent.Mathematics.D23c_TensionSpectralGap
import NavaRobertsonIndependent.Mathematics.D23d_BandWidth
import NavaRobertsonIndependent.Mathematics.D23e_TransportTensionExclusion
import NavaRobertsonIndependent.Mathematics.D24_GapFourAsymptote
import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
import NavaRobertsonIndependent.Mathematics.D26a_OmegaFromPi
import NavaRobertsonIndependent.Mathematics.D28_BakryEmeryCurvature
import NavaRobertsonIndependent.Mathematics.D28b_OllivierCurvature
import NavaRobertsonIndependent.Mathematics.PhyslibBridge
import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# Layer 1 — Mathematics

This is the mathematical theorem, stated over Mathlib. The only other import is
physlib's algebraic uncertainty framework, used by `PhyslibBridge` alone. No
physical constant, no unit, no laboratory anchor and no physical hypothesis
appears anywhere in the import closure of this module. The dependency is
one-way: this layer does not import `Physics`, and that is checked by
`Verification/Layer1_Mathematics.lean`.

## The theorem

The Nava–Robertson–Schrödinger Elemental Dimensional Uncertainty Inequality for
the pair `(T_d, P_d)` on the path graph with `d` vertices (`D3`), acting on
`H_d = ℂ^d`:

* at the state of maximal tension `ψ*` (the explicit Fiedler mode): `cov = 0`,
  `Var T · Var P = (c/2)² (1 + δ_geom)²` with `c = −2/(d−1)`, and the
  Robertson–Schrödinger gap is `(c/2)² δ_geom (2 + δ_geom)`, with
  `δ_geom(d) = C_Nava(d) − 1` (`D20`, `D21`);
* the gap vanishes exactly for `d ∈ {2, 3}` and is strictly positive for
  `d ≥ 4` (`D7` Niven, `D21`, `D22`);
* the top eigenvalue `2/(d−1)` of `K_d = i[T_d, P_d]` is simple, so the strict
  inequality holds at every unit state attaining it (`D21`);
* for `d ≥ 4`, `δ_geom` is strictly increasing, with global minimum `δ_geom(4)`
  and strict upper bound `δ_∞ = C_∞ − 1`, where `C_∞² = π²/3 − 2` (`D8`, `D9`);
* the ambient inequality is proved from Cauchy–Gram (`D1`, `D2`).
* the inequality at `ψ*` is physlib's `robertson_schrodinger` instantiated at the
  vector state of `ψ*` with `T_d`, `P_d` as observables, term by term, and it is
  strict there for `d ≥ 4` (`PhyslibBridge`).
* on the cube `Fin dx × Fin dy × Fin dz` of `D4`, one pair `(T, P)` per axis: pairs on
  different axes commute, and at `ψ* ⊗ ψ* ⊗ ψ*` each axis satisfies the inequality with
  its own `C_Nava`, saturating exactly for `2` or `3` sites and strict from `4` (`D37`).

## Order of the chain

`D1` Cauchy–Gram → `D2` Robertson–Schrödinger → `D3` path graph → `D5` maximal
tension → `D6` Fiedler → `D7` Niven → `D8` Szegő → `D9` monotonicity → `D10`
certificate → `D17`–`D23` instantiation with the concrete operators and
saturation of eigenvectors. `D11`–`D16b`, `D24` and `SumInvSinSq` are side results
(dimensionless area quantum `δ_geom(4)²`, finite cosecant-square identity via
Chebyshev roots in `SumInvSinSq`, transport to closed surfaces, and the
gap `C_∞ − C_Nava(4)`).

**The quantum is dimensional** (`D25`): the path-graph family `H₂, H₃, H₄, …` is the
graph of Robertson's bound in every dimension — the graph of an algebraic
obstruction. Each `H_d` has its own quantum `cuantoDim d = δ_geom(d)`: zero exactly
at the seeds `d = 2, 3` (`sin_cuanto_en_d3`), strictly positive and increasing from
`d = 4`, strictly below `δ_∞ > 0` and converging to it (`cuanto_dimensional`).

**`Ω` from `π`** (`D26a`): `omegaPi = (1 − 1/C∞)·e^{−1/C∞}` and the decimal
`0.049543679` is its 9-digit rounding, enclosed on both sides in `(1.11, 1.12)×10⁻¹⁰`
(`decimal_desde_pi`). Pure mathematics; the baryonic reading is Layer 3.
`D28`/`D28b` are a negative result: the interior of the path graph (`D3`) has
zero discrete curvature, both Bakry-Émery (`CD(0,2)` sharp) and Ollivier-Ricci
(Kantorovich–Rubinstein), so no curvature-driven bridge to a physical
stretching hypothesis can be read off the graph itself.
The cosmological reading (`D26`, `D26b`) is Layer 3 (`Cosmology`), and the
observer/measurement postulates (`D29`–`D31`) are Layer 4 (`Ontology`); neither
is imported here.

The word "quantum" in `D11` means the algebraic quantum `δ_geom(4)²`, a pure
number. The physical scale attached to it lives in Layer 2.
-/

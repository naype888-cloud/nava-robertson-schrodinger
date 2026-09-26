/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D0_Habitat
public import NavaRobertsonIndependent.Mathematics.D1_CauchyGramInequality
public import NavaRobertsonIndependent.Mathematics.D2_Robertson
public import NavaRobertsonIndependent.Mathematics.D3_PathGraph
public import NavaRobertsonIndependent.Mathematics.D4_WhyNotDiagonal
public import NavaRobertsonIndependent.Mathematics.D5_MaximalTension
public import NavaRobertsonIndependent.Mathematics.D6_Fiedler
public import NavaRobertsonIndependent.Mathematics.D7_Niven
public import NavaRobertsonIndependent.Mathematics.D8_Szego
public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
public import NavaRobertsonIndependent.Mathematics.D10_Certificate
public import NavaRobertsonIndependent.Mathematics.D11_MinimalAreaQuantum
public import NavaRobertsonIndependent.Mathematics.D12_FiniteScalarCommutator
public import NavaRobertsonIndependent.Mathematics.D13_FirstCombinatorialRupture
public import NavaRobertsonIndependent.Mathematics.D14_SzegoGapExcess
public import NavaRobertsonIndependent.Mathematics.SumInvSinSq
public import NavaRobertsonIndependent.Mathematics.D16_ClosedSurfaceTransport
public import NavaRobertsonIndependent.Mathematics.D16b_GaussBonnetBridge
public import NavaRobertsonIndependent.Mathematics.D17_IntrinsicTransportDefect
public import NavaRobertsonIndependent.Mathematics.D19_FiedlerPositionVariance
public import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
public import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality
public import NavaRobertsonIndependent.Mathematics.D22_TransportPositionInstanceTdPd
public import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation
public import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap
public import NavaRobertsonIndependent.Mathematics.D23c_TensionSpectralGap
public import NavaRobertsonIndependent.Mathematics.D23d_BandWidth
public import NavaRobertsonIndependent.Mathematics.D23e_TransportTensionExclusion
public import NavaRobertsonIndependent.Mathematics.D23f_MinUncertaintyTensionFour
public import NavaRobertsonIndependent.Mathematics.D24_GapFourAsymptote
public import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
public import NavaRobertsonIndependent.Mathematics.D26a_OmegaFromPi
public import NavaRobertsonIndependent.Mathematics.D28_BakryEmeryCurvature
public import NavaRobertsonIndependent.Mathematics.D28b_OllivierCurvature
public import NavaRobertsonIndependent.Mathematics.PhyslibBridge
public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D
public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle
public import NavaRobertsonIndependent.Mathematics.D37c_CubeSpectrum
public import NavaRobertsonIndependent.Mathematics.D37d_CubePythagoras
public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum
public import NavaRobertsonIndependent.Mathematics.D37f_LightCone
public import NavaRobertsonIndependent.Mathematics.D37g_LiebRobinson
public import NavaRobertsonIndependent.Mathematics.D38_GroupVelocity
public import NavaRobertsonIndependent.Mathematics.D39_ConjugatePairs
public import NavaRobertsonIndependent.Mathematics.D40_SpeedLimitUncertainty
public import NavaRobertsonIndependent.Mathematics.D41_MandelstamTammCramerRao
public import NavaRobertsonIndependent.Mathematics.D42_DirectionOctants

/-!
# NRS and NRS³

`T_d` (normalized adjacency of the path graph) and `P_d` (equispaced diagonal) on `ℂ^d`, and
their lifts to the product of three paths (`D37`). Stated over Mathlib; physlib is imported by
`PhyslibBridge` only. No physical constant or unit appears. Reading `T_d : P_d` as motion in
discrete space, with the three factors of the cube as `x, y, z`, is a declared bridge, not a
theorem.

## Contents

- `D0`–`D2` : `H_d`, Cauchy–Schwarz as a Gram defect, Robertson–Schrödinger.
- `D3`–`D6` : the path graph and its uniqueness, the maximal-tension state, the spectrum.
- `D7`–`D10` : Niven, the Szegő limit, monotonicity, the joint certificate.
- `D11`–`D17`, `D24`, `D25`, `SumInvSinSq` : area quantum, scalar commutator, first rupture,
  excess, closed surfaces, intrinsic defect, the gap at `d = 4`, the dimensional quantum.
- `D19`–`D23f` : position variance, Gram step, the NRS inequality (`D21`) and its instance,
  saturation on eigenvectors, the strict band, transport–tension exclusion, `1/φ` at `d = 4`.
- `D26a` : a rational enclosure of `(1 − 1/C_∞) e^{−1/C_∞}`.
- `D28`, `D28b` : the interior of the path is flat (Bakry–Émery, Ollivier–Ricci).
- `D37`–`D37g` : the cube, the NRS angle, spectrum, Pythagoras, volumetric quantum, light
  cone, Lieb–Robinson.
- `D38` : dispersion, group velocity, the Heisenberg equation.
- `D39` : every conjugate pair realized on `T_d : P_d`.
- `D40` : the speed limit excludes minimum uncertainty.
- `D41` : Mandelstam–Tamm and Cramér–Rao on `T_d : P_d` and on the cube.
- `D42` : direction is a sign; the eight octants of the cube share the bounds.
- `PhyslibBridge` : `D21` is physlib's `robertson_schrodinger` at `ψ*`.
-/

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D23g_MinUncertaintyUpperBound
public import NavaRobertsonCertificados.D43_NRSOctahedron
public import NavaRobertsonCertificados.D44_VelocityBand
public import NavaRobertsonCertificados.D45d_WidestBand
public import NavaRobertsonCertificados.D46_ConeInBand
public import NavaRobertsonCertificados.D49d_RobertsonDeterminantBand
public import NavaRobertsonCertificados.D49e_AxisDefectEntangled
public import NavaRobertsonCertificados.D49f_MaxTensionCube
public import NavaRobertsonCertificados.D49h_DeterminantEqualityRelation

/-!
# Certificates

A separate target, not built by default: `D23g`, the bound `≤ 1/φ` on the tension of the
minimum-uncertainty states of `H₄`, and its two exact Positivstellensatz certificates. Build with
`lake build NavaRobertsonCertificados` (20–30 minutes; `CotaCasoA` is a 1 MB identity checked by
`ring`).

`D43`: the Nava–Robertson–Schrödinger octahedron, with the velocity threshold `v*(4)` of
minimum uncertainty.

`D44`: the velocity band `Ϙ(d) = (v*(d), 1]` of forced defect and its width `ϙ(d) = 1 − v*(d)`.

`D45b`–`D45d`: an interval checker for Stark packets, evaluated by the kernel, and with it
`ϙ(d) ≤ 0.0728 < ϙ(4)` for every `d ≥ 5`: `d = 4` has the widest band.

`D46`: the cone speed lies in every band: for every `d ≥ 4`, every unit state at the cone speed
carries a Robertson–Schrödinger surplus, and `d ≥ 4` is sharp.

`D49d`: det|NRS³ in the band: product states with the speed of each axis in `Ϙ(d)`, and in
particular at the cone speed, satisfy `det Σ > (t_x t_y t_z / 8)²`.

`D49e`: the defect of every axis in the band, for every state, entangled or not: speeds in
`Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)` force the three defects, and their product is positive.

`D49f`: maximal tension leaves no room for entanglement: with `|v| = 1` on `x`, `y`, `z` every
state is a phase times `ψ* ⊗ ψ* ⊗ ψ*`, and det|NRS³ holds with ratio
`C_Nava(dx)² C_Nava(dy)² C_Nava(dz)²`, strict from `4` sites per axis.

`D49h`: equality in det|NRS³ with the three speeds in the band needs a relation
`σ_x [T_x, P_x] Φ + σ_y [T_y, P_y] Φ + σ_z [T_z, P_z] Φ = 0` with `σ ≠ 0`.
-/

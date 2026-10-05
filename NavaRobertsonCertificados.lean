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
public import NavaRobertsonCertificados.D49j_RobertsonDeterminantSplitAxis
public import NavaRobertsonCertificados.D49k_RobertsonDeterminantCanonicalAxes
public import NavaRobertsonCertificados.D49l_FreeAxis
public import NavaRobertsonCertificados.D49n_TwoAxes
public import NavaRobertsonCertificados.D49o_BracketSpan
public import NavaRobertsonCertificados.D49p_RelationsDimension
public import NavaRobertsonCertificados.D49q_TransportRelation
public import NavaRobertsonCertificados.D49r_EdgeOperator
public import NavaRobertsonCertificados.D49s_EdgeSlices
public import NavaRobertsonCertificados.D49t_RobertsonDeterminantBandStrict

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
`C_Nava(dx)² C_Nava(dy)² C_Nava(dz)²`, strict from `4` positions per axis.

`D49h`: equality in det|NRS³ with the three speeds in the band needs a relation
`σ_x [T_x, P_x] Φ + σ_y [T_y, P_y] Φ + σ_z [T_z, P_z] Φ = 0` with `σ ≠ 0`.

`D49j`: an axis on its own keeps det|NRS³ strict in the band: if `Φ = w ⊗ χ` splits off `z`,
however entangled `x` and `y` are, `|det Ω| < det Σ`.

`D49k`: det|NRS³ on canonical axes: orthogonal fluctuations of `x`, `y`, `z` give
`det Σ = Π (1 + g_i/ω_i²) · |det Ω|`, strict in the band.

`D49l`: a free axis leaves no state: if the brackets of the relations of `Φ` reach one axis
alone and a relation carries position there without transport, then `[T_i, P_i] Φ = 0`,
`T_i Φ = 0` and `Φ = 0`; transport and `[T_d, P_d]` have no common vector.

`D49n`: brackets on two axes: `σ_i [T_i, P_i] Φ + σ_j [T_j, P_j] Φ = 0` with `σ_i ≠ 0` and a
relation with position on axis `i` alone on `i`, `j` leave `Φ = 0`; so does `[T_i, P_i] Φ = 0`
with a relation carrying position but no transport on axis `i`.

`D49o`: the span `W` of the bracket recipes `σ(a, b)` of pairs of relations: every `w ∈ W`
gives `Σ_k w_k [T_k, P_k] Φ = 0`, and `e_i ∈ W` leaves `Φ = 0`.

`D49p`: how many relations: in the band none lives on one axis, so there are at most four;
at equality at least three; four leave `Φ = 0`.

`D49q`: a transport relation from two tensions: `w_i [T_i, P_i] Φ + w_j [T_j, P_j] Φ = 0` and a
relation without transport on `i`, `j` give `(w_i c(P_i) h_i² T_i + w_j c(P_j) h_j² T_j) Φ = 0`.

`D49r`: `[T_d, [T_d, P_d]] = (2h/ρ_d²) diag(−1, 0, …, 0, +1)`: it lives on the two ends.

`D49s`: the edge of the cube: a transport relation `(α T_x + β T_y) Φ = 0` is a recurrence along
`x`; with two tensions it leaves `Φ = 0` or `Φ` split off `z`.

`D49t`: **det|NRS³ is strict in the band, for every state**: on every box, every unit state whose
speeds on `x`, `y`, `z` lie in the bands satisfies `|det Ω| < det Σ`, entangled or not, canonical
axes or not.
-/

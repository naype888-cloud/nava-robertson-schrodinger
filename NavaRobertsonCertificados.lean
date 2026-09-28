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
-/

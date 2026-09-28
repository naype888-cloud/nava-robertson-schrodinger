/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D23g_MinUncertaintyUpperBound
public import NavaRobertsonCertificados.D43_NRSOctahedron
public import NavaRobertsonCertificados.D44_VelocityBand

/-!
# Certificates

A separate target, not built by default: `D23g`, the bound `≤ 1/φ` on the tension of the
minimum-uncertainty states of `H₄`, and its two exact Positivstellensatz certificates. Build with
`lake build NavaRobertsonCertificados` (20–30 minutes; `CotaCasoA` is a 1 MB identity checked by
`ring`).

`D43`: the Nava–Robertson–Schrödinger octahedron, with the velocity threshold `v*(4)` of
minimum uncertainty.

`D44`: the velocity band `Ϙ(d) = (v*(d), 1]` of forced defect and its width `ϙ(d) = 1 − v*(d)`.
-/

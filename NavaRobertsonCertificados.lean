/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D23g_MinUncertaintyUpperBound

/-!
# Certificates

A separate target, not built by default: `D23g`, the bound `≤ 1/φ` on the tension of the
minimum-uncertainty states of `H₄`, and its two exact Positivstellensatz certificates. Build with
`lake build NavaRobertsonCertificados` (20–30 minutes; `CotaCasoA` is a 1 MB identity checked by
`ring`).
-/

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D23g_MinUncertaintyUpperBound

/-!
# Certificates — separate target

Not part of the default build. Contains `D23g`, the upper bound for the minimum-uncertainty
states of `H₄` (tension `≤ 1/φ`), and its two exact rational Positivstellensatz certificates.
Build with `lake build NavaRobertsonCertificados` (about 20–30 minutes: `CotaCasoA` alone is a
1 MB polynomial identity checked by `ring`).
-/

import NavaRobertsonCertificados.CotaCasoA
import NavaRobertsonCertificados.CotaCasoB

/-!
# Certificates — separate target

Not part of the default build. Contains `D23g`, the upper bound for the minimum-uncertainty
states of `H₄` (tension `≤ 1/φ`), and its two exact rational Positivstellensatz certificates.
Build with `lake build NavaRobertsonCertificados` (about 20–30 minutes: `CotaCasoA` alone is a
1 MB polynomial identity checked by `ring`).
-/

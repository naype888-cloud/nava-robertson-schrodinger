import NavaRobertsonIndependent.Superseded.D27_TimeDeformation
import NavaRobertsonIndependent.Superseded.D27b_CurvatureCoupling
import NavaRobertsonIndependent.Superseded.PhysicalNonContinuumPincerAsubDeltaInf
import NavaRobertsonIndependent.Superseded.D18_PhysicalNonContinuumInstantiated

/-!
# Superseded — superseded or replaced modules (outside the four layers)

Kept compiling for traceability; **no layer imports them**, and the
`Verification/` checks fail if one does.

* `D27_TimeDeformation`, `D27b_CurvatureCoupling`: assumed the cell stretches
  with matter. **Superseded** by cell counting: the cell does not curve,
  curvature adds cells (`Physics/D32_WhyTimeGrows`).
* `PhysicalNonContinuumPincerAsubDeltaInf`, `D18_PhysicalNonContinuumInstantiated`:
  the "non-continuum" as `x > 0 ⇒ x ≠ 0`. **Replaced** by
  `Physics/PhysicalSupportR4`.

`DefectInfinitoRobertsonClay2026` was removed from the package in v14: it was
tautological, and its content is proved in `D8`, `D9`, `D10` and `D25`.
-/

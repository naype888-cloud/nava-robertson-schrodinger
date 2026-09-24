import NavaRobertsonIndependent.Mathematics
import NavaRobertsonIndependent.Physics
import NavaRobertsonIndependent.Cosmology
import NavaRobertsonIndependent.Ontology
import NavaRobertsonIndependent.Superseded

/-!
# Nava–Robertson–Schrödinger Elemental Dimensional Uncertainty Inequality

Single verification target of the package, organised in layers that do not mix:

* `NavaRobertsonIndependent.Mathematics` — Layer 1, the mathematical theorem
  over Mathlib, with no physical input.
* `NavaRobertsonIndependent.Physics` — Layer 2, the physical reading:
  registration floors and quanta, with its inputs stated explicitly. It depends
  on Layer 1; Layer 1 does not depend on it.
* `NavaRobertsonIndependent.Cosmology` — Layer 3, a cosmological reading
  (`Ω_b`), on top of Layers 1–2.
* `NavaRobertsonIndependent.Ontology` — Layer 4, observer and measurement as
  declared postulates, on top of Layer 1 only.

* `NavaRobertsonIndependent.Superseded` — outside the four layers: superseded or replaced
  modules, kept compiling for traceability. No layer imports it.

No lower layer imports a higher one.

Each layer can be built alone: `lake build NavaRobertsonIndependent.Mathematics`.
The files in `Verification/` check the layer boundary and print the axioms of
the headline theorems.
-/

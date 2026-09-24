import Lean
import NavaRobertsonIndependent.Cosmology

/-!
# Verification of Layer 3

Run with `lake env lean Verification/Layer3_Cosmology.lean` from the package root.
Layer 3 may use Layers 1 and 2, but not Layer 4. `#print axioms` shows only the
three standard axioms.
-/

open Lean in
#eval show CoreM Unit from do
  let mods := (← getEnv).header.moduleNames
  let prohibidos : List Name :=
    [`NavaRobertsonIndependent.Ontology,
     `NavaRobertsonIndependent.Superseded]
  let malos := mods.filter fun m => prohibidos.any (·.isPrefixOf m)
  let propios := mods.filter fun m => `NavaRobertsonIndependent |>.isPrefixOf m
  if malos.isEmpty then
    IO.println s!"OK: Layer 3 imports no ontology module ({propios.size} package modules in the closure)"
  else
    throwError s!"BOUNDARY VIOLATION: {malos}"

#print axioms BaryogenesisEspejo.espejo_espectral
#print axioms BaryogenesisEspejo.cadena_baryogenesis
#check @EncierroOmegaB.omegaBar_encierro
#print axioms EncierroOmegaB.omegaBar_encierro
#check @EncierroOmegaB.omegaBar_distancia_gt
#print axioms EncierroOmegaB.omegaBar_distancia_gt

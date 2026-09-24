import Lean
import NavaRobertsonIndependent.Mathematics

/-!
# Verification of Layer 1

Run with `lake env lean Verification/Layer1_Mathematics.lean` from the package root.

1. Boundary: the import closure of `NavaRobertsonIndependent.Mathematics` must
   contain no module of Layers 2, 3 or 4. The check fails loudly if it does.
2. Axioms: the headline theorems of the mathematical theorem, printed. Only
   `propext`, `Classical.choice` and `Quot.sound` are expected.
-/

open Lean

#eval show CoreM Unit from do
  let mods := (← getEnv).header.moduleNames
  let prohibidos : List Name :=
    [`NavaRobertsonIndependent.Physics,
     `NavaRobertsonIndependent.Cosmology,
     `NavaRobertsonIndependent.Ontology,
     `NavaRobertsonIndependent.Superseded]
  let malos := mods.filter fun m => prohibidos.any (·.isPrefixOf m)
  let propios := mods.filter fun m => `NavaRobertsonIndependent |>.isPrefixOf m
  if malos.isEmpty then
    IO.println s!"OK: Layer 1 imports no physics, cosmology or ontology module ({propios.size} package modules in the closure)"
  else
    throwError s!"BOUNDARY VIOLATION: {malos}"

#print axioms Robertson1929.saturadaSchrodinger_iff
#print axioms Gnomon.no_reposición_saturacion_camino
#print axioms Gnomon.limite_szego_CoherenceConstant
#print axioms Gnomon.deltaInf_pos
#print axioms Gnomon.geometricGap_strictMonoOn_ge_four
#print axioms Gnomon.geometricGap_four_le
#print axioms Gnomon.geometricGap_lt_deltaInf
#print axioms BlindajeHd.certificadoBlindajeHd_OK
#print axioms NavaRobertsonSchrodingerEDUI.gap_eq_geometricGap
#print axioms NavaRobertsonSchrodingerEDUI.saturacion_iff
#print axioms NavaRobertsonSchrodingerEDUI.desigualdad_estricta_estado_maximo
#print axioms NavaRobertsonSchrodingerEDUI.saturada_TdPd_iff
#print axioms NavaRobertsonSchrodingerEDUI.defect_pos_TdPd
#print axioms SaturacionAutovectores.autovector_no_maxima_tension
#print axioms SaturacionAutovectores.producto_varianzas_ge_K
#print axioms GapCuatroAsintota.gapCuatroInf_positiva_y_acotada
#print axioms GapCuatroAsintota.ascenso_dentro_de_la_gap
#print axioms GapCuatroAsintota.ascenso_tiende_a_gap
#print axioms CurvaturaBakryEmery.gamma2_eq_bochner
#print axioms CurvaturaBakryEmery.curvatura_camino_CD02
#print axioms CurvaturaBakryEmery.kappa_cero_no_mejorable
#print axioms CurvaturaBakryEmery.n_dos_no_mejorable
#print axioms CurvaturaOllivier.W1_es_uno
#print axioms CurvaturaOllivier.convergencia_bakry_emery_ollivier
#print axioms CuantoDimensional.cuanto_dimensional
#print axioms CuantoDimensional.sin_cuanto_en_d3
#print axioms OmegaDesdePi.decimal_desde_pi
#print axioms PhyslibBridge.robertson_schrodinger_eq_D21
#print axioms PhyslibBridge.physlib_robertson_schrodinger_strict

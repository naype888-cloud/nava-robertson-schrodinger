import Lean
import NavaRobertsonIndependent.Ontology

/-!
# Verification of Layer 4

Run with `lake env lean Verification/Layer4_Ontology.lean` from the package root.
Layer 4 rests on Layer 1 only: the check fails if its import closure contains any
module of Layers 2 or 3. The postulates are structures; `#check` shows them.
-/

open Lean in
#eval show CoreM Unit from do
  let mods := (← getEnv).header.moduleNames
  let prohibidos : List Name :=
    [`NavaRobertsonIndependent.Physics,
     `NavaRobertsonIndependent.Cosmology,
     `NavaRobertsonIndependent.Superseded]
  let malos := mods.filter fun m => prohibidos.any (·.isPrefixOf m)
  let propios := mods.filter fun m => `NavaRobertsonIndependent |>.isPrefixOf m
  if malos.isEmpty then
    IO.println s!"OK: Layer 4 imports no physics or cosmology module ({propios.size} package modules in the closure)"
  else
    throwError s!"BOUNDARY VIOLATION: {malos}"

#check @ObservadorMedicionEspectral.MedicionEspectral
#print axioms ObservadorMedicionEspectral.no_auto_medida
#print axioms CuentaDistincionCuatroCanales.cubo_medido_es_cuatro_canales
#print axioms FaseToroThick.toro_entre_cero_e_infinito
#print axioms FaseToroThick.sin_cero_absoluto_implica_toro
#check @EonAbierto.RegistroEonAbierto
#check @EonAbierto.RegistroEonAbierto.cierre_eon_abierto
#print axioms EonAbierto.RegistroEonAbierto.cierre_eon_abierto
#print axioms EonAbierto.RegistroEonAbierto.registro_satisfacible
#print axioms BandaExistenciaMedible.existencia_medible_banda

#check @PuenteBanachHilbertAB.lectura_Banach_depende_de_q
#check @PuenteBanachHilbertAB.lectura_Hilbert_depende_de_q
#print axioms PuenteBanachHilbertAB.dimension_relacion_AB
#print axioms PuenteBanachHilbertAB.H3_mas_distincion_es_H4
#print axioms PuenteBanachHilbertAB.H4_no_satura
#print axioms PuenteBanachHilbertAB.llega_B_activa_toro
#print axioms PuenteBanachHilbertAB.registroGerminado_thick_defect
#print axioms PuenteBanachHilbertAB.eones_infinito_embebidos
#print axioms PuenteBanachHilbertAB.coordenada_observable
#print axioms PuenteBanachHilbertAB.toro_HilbertRel
#print axioms PuenteBanachHilbertAB.sin_cero_absoluto_abre_ruptura
#check @PuenteBanachHilbertAB.distincion_cancela_cero_e_infinito
#print axioms PuenteBanachHilbertAB.distincion_cancela_cero_e_infinito

#check @SeedYRegistroH4.d3_satura_pero_no_se_registra
#print axioms SeedYRegistroH4.d3_satura_pero_no_se_registra
#check @SeedYRegistroH4.suavidad_sin_cuanto_imposible_en_H4
#print axioms SeedYRegistroH4.suavidad_sin_cuanto_imposible_en_H4

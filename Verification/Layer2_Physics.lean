import Lean
import NavaRobertsonIndependent.Physics

/-!
# Verification of Layer 2

Run with `lake env lean Verification/Layer2_Physics.lean` from the package root.

The physical theorems are conditional on explicit inputs. `#check` shows, for
each headline theorem, exactly which hypotheses appear in its statement, and
`#print axioms` shows that no axiom beyond the three standard ones is used.
The laboratory anchors (`l_P`, `c`, `h`, `Ω_b`) are definitions, not axioms.
The first check fails if Layer 2 imports any module of Layers 3 or 4.
-/

open Lean in
#eval show CoreM Unit from do
  let mods := (← getEnv).header.moduleNames
  let prohibidos : List Name :=
    [`NavaRobertsonIndependent.Cosmology,
     `NavaRobertsonIndependent.Ontology,
     `NavaRobertsonIndependent.Superseded]
  let malos := mods.filter fun m => prohibidos.any (·.isPrefixOf m)
  let propios := mods.filter fun m => `NavaRobertsonIndependent |>.isPrefixOf m
  if malos.isEmpty then
    IO.println s!"OK: Layer 2 imports no cosmology or ontology module ({propios.size} package modules in the closure)"
  else
    throwError s!"BOUNDARY VIOLATION: {malos}"

open LimiteSubPlanckiano CierreRegistroTiempoEnergiaSbpk VelocidadMaximaRegistrable
  PasoElementalCelda

/-! ### 2.1 Registration floors and quanta -/

#check @paquete_subplanckiano
#print axioms paquete_subplanckiano

-- H1 is the hypothesis `hE : DispersionAdmisible deltaH`.
#check @tick_es_cota_mandelstam_tamm
#print axioms tick_es_cota_mandelstam_tamm

#check @ProcesoTransporte.velocidadMedia_le_luz
#print axioms ProcesoTransporte.velocidadMedia_le_luz

#check @ProcesoTransporte.k_le_n_de_duracion
#print axioms ProcesoTransporte.k_le_n_de_duracion

#check @longitudPaso_cuatro
#print axioms longitudPaso_cuatro

#check @paso_en_rango
#print axioms paso_en_rango

#check @longitudPaso_tendsto_longitudPasoInf
#print axioms longitudPaso_tendsto_longitudPasoInf

#check @paso_entre_tick_es_c
#print axioms paso_entre_tick_es_c

#check @ColapsoSchwarzschild.relacionPlanckNewton_satisfacible
#print axioms ColapsoSchwarzschild.relacionPlanckNewton_satisfacible

#check @Omega_b_desde_pi
#print axioms Omega_b_desde_pi

/-! ### 2.2 Dimensional quanta -/

open CuantoDimensionalFisico SaltoMasaDimensional

#check @Tausbpk_le_tickDim
#print axioms Tausbpk_le_tickDim

#check @mas_dimension_mas_tiempo
#print axioms mas_dimension_mas_tiempo

#print axioms salto_masa_no_colapsa_OK
#print axioms certificado_salto_masa_OK

/-! ### 2.3 Time and curvature: the cell does not curve, curvature adds cells -/

open MasCeldasMasTiempo PorQueCreceElTiempo

#check @mas_celdas_mas_costoso_misma_velocidad
#print axioms mas_celdas_mas_costoso_misma_velocidad

-- `HCurvaturaConteo` is the declared hypothesis; it is used and satisfiable.
#check @HCurvaturaConteo
#print axioms hCurvaturaConteo_satisfacible
#check @curva_tarda_mas
#print axioms curva_tarda_mas
#print axioms por_que_crece_el_tiempo

/-! ### 2.4 Physical support: bounded, discrete, finite ℝ⁴ -/

open SoporteFisicoR4

#print axioms R4_es_Hilbert_y_Banach
#print axioms soporte_finito
#print axioms separacion_minima
#check @convergente_es_eventualmente_constante
#print axioms convergente_es_eventualmente_constante
#print axioms registrados_ne_continuo
#print axioms nada_bajo_el_tick
#print axioms eon_capado_finito

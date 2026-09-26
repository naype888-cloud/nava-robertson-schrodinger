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
    IO.println s!"OK: Layer 1 imports no physics/cosmology/ontology module ({propios.size} modules)"
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
#print axioms PathGraph3DNRS.conmutador_ejes_distintos_xy
#print axioms PathGraph3DNRS.saturacion_cubo
#print axioms PathGraph3DNRS.estricta_cubo
#print axioms AnguloNRS.cos_anguloNRS
#print axioms AnguloNRS.anguloNRS_eq_zero_iff
#print axioms AnguloNRS.anguloNRS_strictMonoOn
#print axioms AnguloNRS.angulos_cubo
#print axioms EspectroCubo.autovector_suma
#print axioms EspectroCubo.tensionTotal_psiStar
#print axioms EspectroCubo.tensionTotal_le
#print axioms AnguloNRS.anguloNRS_cuatro
#print axioms AnguloNRS.piso_angular
#print axioms AnguloNRS.piso_angular_cubo
#print axioms IncertidumbreMinimaCuatro.satura_psiSat
#print axioms IncertidumbreMinimaCuatro.tension_psiSat
#print axioms IncertidumbreMinimaCuatro.tension_psiSat_fraccion
#print axioms AnguloNRS.anguloNRS_isotropia
#print axioms AnguloNRS.isotropia_finita_cubo
#print axioms PitagorasCubo.pitagoras_T
#print axioms PitagorasCubo.pitagoras_P
#print axioms PitagorasCubo.angulo_total_cubo
#print axioms PitagorasCubo.angulo_total_cuatro
#print axioms CuantoVolumetrico.cuanto_volumetrico
#print axioms CuantoVolumetrico.cuantoVolumetrico_eq_cero_iff
#print axioms CuantoVolumetrico.cuantoVolumetrico_cuatro
#print axioms CuantoVolumetrico.cuantoVolumetrico_cuatro_sq
#print axioms ConoDeLuz.cono_de_luz
#print axioms ConoDeLuz.cono_de_luz_estado
#print axioms ConoDeLuz.borde_del_cono_ne_zero
#print axioms ConoDeLuz.cono_de_luz_cubo
#print axioms LiebRobinson.lieb_robinson
#print axioms VelocidadGrupo.hasDerivAt_dispersion
#print axioms VelocidadGrupo.heisenberg
#print axioms VelocidadGrupo.abs_velocidad_le
#print axioms VelocidadGrupo.velocidad_psiStar
#print axioms VelocidadGrupo.velocidad_modoFase
#print axioms VelocidadGrupo.velocidades_PsiStar3D
#print axioms VelocidadGrupo.rapidez_sq_PsiStar3D
#print axioms ParesConjugados.anguloG_afin
#print axioms ParesConjugados.razonG_afin
#print axioms ParesConjugados.razon_par
#print axioms ParesConjugados.satura_par_iff
#print axioms ParesConjugados.angulo_par_lt_of_lt
#print axioms ParesConjugados.angulo_par_lt_limite
#print axioms ParesConjugados.cuantoVolumetrico_pares
#print axioms ParesConjugados.cuanto_volumetrico_pares

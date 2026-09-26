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

#print axioms Robertson1929.schrodingerSaturated_iff
#print axioms Gnomon.not_saturated_of_four_le
#print axioms Gnomon.tendsto_CoherenceConstant
#print axioms Gnomon.deltaInf_pos
#print axioms Gnomon.geometricGap_strictMonoOn_ge_four
#print axioms Gnomon.geometricGap_four_le
#print axioms Gnomon.geometricGap_lt_deltaInf
#print axioms HdCertificate.certificate
#print axioms NRSInequality.gap_eq_geometricGap
#print axioms NRSInequality.saturation_iff
#print axioms NRSInequality.strict_inequality_of_maxTension
#print axioms NRSInequality.saturated_TdPd_iff
#print axioms NRSInequality.defect_pos_TdPd
#print axioms EigenvectorSaturation.eigenvector_not_maxTension
#print axioms EigenvectorSaturation.variance_mul_variance_ge
#print axioms GapFourAsymptote.gapFourInf_pos_lt_deltaInf
#print axioms GapFourAsymptote.rise_lt_gapFourInf
#print axioms GapFourAsymptote.rise_tendsto_gapFourInf
#print axioms BakryEmery.gamma2_eq_bochner
#print axioms BakryEmery.path_CD02
#print axioms BakryEmery.kappa_zero_sharp
#print axioms BakryEmery.dim_two_sharp
#print axioms OllivierCurvature.W1_eq_one
#print axioms OllivierCurvature.bakryEmery_ollivier_agree
#print axioms DimensionalQuantum.dimQuantum_certificate
#print axioms DimensionalQuantum.dimQuantum_three
#print axioms OmegaFromPi.decimal_of_pi
#print axioms PhyslibBridge.robertson_schrodinger_eq_D21
#print axioms PhyslibBridge.physlib_robertson_schrodinger_strict
#print axioms PathGraph3DNRS.commutator_axes_xy
#print axioms PathGraph3DNRS.saturation_cube
#print axioms PathGraph3DNRS.strict_cube
#print axioms NRSAngle.cos_angleNRS
#print axioms NRSAngle.angleNRS_eq_zero_iff
#print axioms NRSAngle.angleNRS_strictMonoOn
#print axioms NRSAngle.angles_cube
#print axioms CubeSpectrum.eigenvector_sum
#print axioms CubeSpectrum.tensionTotal_psiStar
#print axioms CubeSpectrum.tensionTotal_le
#print axioms NRSAngle.angleNRS_four
#print axioms NRSAngle.angle_floor
#print axioms NRSAngle.angle_floor_cube
#print axioms MinUncertaintyFour.saturated_psiSat
#print axioms MinUncertaintyFour.tension_psiSat
#print axioms MinUncertaintyFour.tension_psiSat_fraction
#print axioms NRSAngle.angleNRS_isotropy
#print axioms NRSAngle.finite_isotropy_cube
#print axioms CubePythagoras.pythagoras_T
#print axioms CubePythagoras.pythagoras_P
#print axioms CubePythagoras.angle_total_cube
#print axioms CubePythagoras.angle_total_four
#print axioms VolumetricQuantum.volQuantum_certificate
#print axioms VolumetricQuantum.volQuantum_eq_zero_iff
#print axioms VolumetricQuantum.volQuantum_four
#print axioms VolumetricQuantum.volQuantum_four_sq
#print axioms LightCone.lightCone
#print axioms LightCone.lightCone_state
#print axioms LightCone.lightCone_edge_ne_zero
#print axioms LightCone.lightCone_cube
#print axioms LiebRobinson.lieb_robinson
#print axioms GroupVelocity.hasDerivAt_dispersion
#print axioms GroupVelocity.heisenberg
#print axioms GroupVelocity.abs_velocity_le
#print axioms GroupVelocity.velocity_psiStar
#print axioms GroupVelocity.velocity_phaseMode
#print axioms GroupVelocity.velocities_PsiStar3D
#print axioms GroupVelocity.speed_sq_PsiStar3D
#print axioms ConjugatePairs.angleG_affineOp
#print axioms ConjugatePairs.ratioG_affineOp
#print axioms ConjugatePairs.ratio_pair
#print axioms ConjugatePairs.saturated_pair_iff
#print axioms ConjugatePairs.angle_pair_lt_of_lt
#print axioms ConjugatePairs.angle_pair_lt_limit
#print axioms ConjugatePairs.volQuantum_pairs
#print axioms ConjugatePairs.volQuantum_pairs_certificate
#print axioms GroupVelocity.surplus_pos_of_velocity_eq_one
#print axioms GroupVelocity.velocity_lt_one_of_surplus_eq_zero

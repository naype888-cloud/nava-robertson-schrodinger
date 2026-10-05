import NavaRobertsonCertificados

/-!
# Verification of the separate certificates target

Run with `lake env lean Verification/Certificados.lean` after
    `lake build NavaRobertsonCertificados`.
Only `propext`, `Classical.choice` and `Quot.sound` are expected.
-/

#print axioms MinUncertaintyBoundFour.tension_le_of_saturated
#print axioms DensityBound.density_bound
#print axioms CertificateH4.bound_caseA
#print axioms CertificateH4.bound_caseB
#print axioms MinUncertaintyFour.tension_psiSat
#print axioms NRSOctahedron.vStar_isGreatest
#print axioms NRSOctahedron.surplus_pos_of_vStar_lt
#print axioms NRSOctahedron.mtRatio_maxCurrentState_four_bounds
#print axioms NRSOctahedron.navaRobertsonSchrodinger_octahedron
#print axioms VelocityBand.exists_saturated_threshold
#print axioms VelocityBand.surplus_pos_of_mem_band
#print axioms VelocityBand.koppa_pos
#print axioms VelocityBand.koppa_four
#print axioms VelocityBand.velocityBand_certificate
#print axioms BandCertificate.sums_sound
#print axioms BandCertificate.half_sound
#print axioms BandCertificate.check_sound
#print axioms WidestBand.exists_fast
#print axioms WidestBand.kappa_le_threshold
#print axioms WidestBand.koppa_lt_koppa_four
#print axioms WidestBand.koppa_le
#print axioms ConeInBand.surplus_pos_of_near_cone
#print axioms ConeInBand.cone_forced_iff
#print axioms ConeInBand.coneInBand_certificate
#print axioms RobertsonDeterminantBand.robertson_det_band
#print axioms RobertsonDeterminantBand.robertson_det_cone
#print axioms AxisDefectEntangled.gramDefect_pos_of_band
#print axioms AxisDefectEntangled.axis_defects_pos
#print axioms MaxTensionCube.eq_smul_octant
#print axioms MaxTensionCube.det_covMatrix_maxTension
#print axioms MaxTensionCube.robertson_det_maxTension_strict
#print axioms DeterminantEqualityRelation.exists_sigma_of_det_eq
#print axioms SplitAxis.robertson_det_strict_of_orthogonal
#print axioms SplitAxis.robertson_det_strict_of_split
#print axioms CanonicalAxes.det_ratio_canonical
#print axioms CanonicalAxes.robertson_det_canonical_strict

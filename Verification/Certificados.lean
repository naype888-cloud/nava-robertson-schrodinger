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
#print axioms NRSOctahedron.mtRatio_psiStar_four_bounds
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
#print axioms Poincare1911.quantum_mean_energy
#print axioms Poincare1911.classical_mean_energy
#print axioms Poincare1911.planck_lt_rayleigh_jeans
#print axioms Poincare1912.eq_of_laplace
#print axioms Poincare1912.planck_forces_levels
#print axioms Poincare1912.no_density_planck
#print axioms Dirac1928.monomial_linearIndependent
#print axioms Dirac1928.four_le_dim
#print axioms Dirac1928.isLeast_dim

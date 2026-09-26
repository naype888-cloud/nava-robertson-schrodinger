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

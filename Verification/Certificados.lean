import NavaRobertsonCertificados

/-!
# Verification of the separate certificates target

Run with `lake env lean Verification/Certificados.lean` after
    `lake build NavaRobertsonCertificados`.
Only `propext`, `Classical.choice` and `Quot.sound` are expected.
-/

#print axioms CotaMinimaIncertidumbreCuatro.tension_le_of_satura
#print axioms CotaDensidades.cota_densidades
#print axioms CertificadoH4.cota_casoA
#print axioms CertificadoH4.cota_casoB
#print axioms IncertidumbreMinimaCuatro.tension_psiSat

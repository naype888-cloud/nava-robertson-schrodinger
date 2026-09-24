import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
import NavaRobertsonIndependent.Mathematics.D24_GapFourAsymptote
import NavaRobertsonIndependent.Ontology.D30_FourChannelDistinctionCount

/-!
# D31 — La banda de la existencia medible (empaquetado)

Certificado conjunto de la narrativa central, **sin matemática nueva**: cada
componente es un teorema ya probado de `D9` (monotonía del defect),
`D24` (gap cuatro–asíntota) y `D30` (la medición añade el canal
observador). Lo que este módulo añade es el enunciado único que las junta.

Lectura: medir añade el canal de la relación (`D30`: un cubo medido es un
objeto de cuatro canales, no tres); la relación exige `d ≥ 4` (`D13`); y en
`d ≥ 4` el defect geométrico vive en la banda

`δ_geom(4) ≤ δ_geom(d) < δ_geom(4) + Δ`,  con  `Δ = C_∞ − C_Nava(4)`,

o sea: la existencia medible paga el defect mínimo posible del régimen
abierto (`D9`: `d = 4` es el mínimo global exacto) y ninguna dimensión
adicional puede encarecerla en más de `Δ` (`D24`: el ascenso entero está
dentro de la gap). La perfección (`δ = 0`, solo `d ∈ {2, 3}`) queda del
lado sin registro: es la seed, no un mundo medible.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib. Capa 1: el cierre de importaciones contiene solo
módulos matemáticos.
-/

noncomputable section

namespace BandaExistenciaMedible

/-- **La banda del defect** (empaquetado de `D9` + `D24`): en todo el
régimen medible `d ≥ 4`, el defect está acotado abajo por su mínimo global
exacto `δ_geom(4)` y el exceso sobre ese mínimo es estrictamente menor que
la gap `Δ = C_∞ − C_Nava(4)`. -/
theorem banda_del_defect (d : ℕ) (hd : 4 ≤ d) :
    Gnomon.geometricGap 4 ≤ Gnomon.geometricGap d
      ∧ Gnomon.geometricGap d - Gnomon.geometricGap 4
        < GapCuatroAsintota.gapCuatroInf
      ∧ 0 < Gnomon.geometricGap 4 :=
  ⟨Gnomon.geometricGap_four_le d hd,
    GapCuatroAsintota.ascenso_dentro_de_la_gap d hd,
    Gnomon.geometricGap_pos_of_four_le 4 (by omega)⟩

/-- **La banda de la existencia medible** (empaquetado de `D30` + `D9` +
`D24`): sobre cualquier triple de canales con margen de distinción, medir
habita forzosamente un cuarto canal observador distinto (`D30`), y el
defect que la relación enciende está en la banda
`[δ_geom(4), δ_geom(4) + Δ)`. Existir midiendo = vivir en esa banda:
ni la perfección sin registro de la seed, ni un defect sin techo. -/
theorem existencia_medible_banda {dx dy dz : ℕ}
    (P : CuentaDistincionCuatroCanales.Par dx dy dz) (d : ℕ) (hd : 4 ≤ d) :
    (∃ d' : ℕ, d' ≠ dx ∧ 2 ≤ d'
      ∧ Nonempty (CuentaDistincionCuatroCanales.MiradaHermano dx))
      ∧ Gnomon.geometricGap 4 ≤ Gnomon.geometricGap d
      ∧ Gnomon.geometricGap d - Gnomon.geometricGap 4
        < GapCuatroAsintota.gapCuatroInf
      ∧ 0 < Gnomon.geometricGap 4 := by
  obtain ⟨d', _hd', hne, hge, hmirada⟩ :=
    CuentaDistincionCuatroCanales.cubo_medido_es_cuatro_canales P
  exact ⟨⟨d', hne, hge, hmirada⟩, banda_del_defect d hd⟩

#print axioms banda_del_defect
#print axioms existencia_medible_banda

end BandaExistenciaMedible

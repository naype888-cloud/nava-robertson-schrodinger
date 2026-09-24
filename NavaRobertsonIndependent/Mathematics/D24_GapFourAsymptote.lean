import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!
# D24 — La gap entre la dimensión cuatro y el límite de Szegő

`C_Nava(d)` es estrictamente creciente desde `d = 4` (`D9_Monotonia`) y tiende a
`C_∞ = √(π²/3 − 2)` (`D8_Szego`). La gap

  `Δ = C_∞ − C_Nava(4) = δ_∞ − δ_geom(4)`

es un número puro que depende solo de `π`. Este módulo fija sus propiedades:
es positiva, es estrictamente menor que `δ_∞`, acota estrictamente el ascenso de
la cadena desde `d = 4`, y es el límite exacto de ese ascenso. No introduce
unidades ni constantes: es un corolario de `D8` y `D9`.
-/

noncomputable section

namespace GapCuatroAsintota

open Gnomon Filter

/-- La gap entre `C_Nava(4)` y el límite de Szegő `C_∞`. -/
def gapCuatroInf : ℝ := CoherenceConstantInf - CoherenceConstant 4

/-- Misma gap en términos de defects: `Δ = δ_∞ − δ_geom(4)`. -/
theorem gapCuatroInf_eq_deltaInf_sub_geometricGap_cuatro :
    gapCuatroInf = deltaInf - geometricGap 4 := by
  unfold gapCuatroInf deltaInf geometricGap
  ring

/-- La gap es positiva: `C_Nava(4) < C_∞`. -/
theorem gapCuatroInf_pos : 0 < gapCuatroInf := by
  have h := CoherenceConstant_lt_CoherenceConstantInf 4 (le_refl 4)
  unfold gapCuatroInf
  linarith

/-- La gap es estrictamente menor que `δ_∞`, porque `δ_geom(4) > 0`. -/
theorem gapCuatroInf_lt_deltaInf : gapCuatroInf < deltaInf := by
  rw [gapCuatroInf_eq_deltaInf_sub_geometricGap_cuatro]
  linarith [geometricGap_pos_of_four_le 4 (le_refl 4)]

/-- Para todo `d ≥ 4`, el ascenso del defect desde `d = 4` queda estrictamente
dentro de la gap: `δ_geom(d) − δ_geom(4) < Δ`, porque `δ_geom(d) < δ_∞`. -/
theorem ascenso_dentro_de_la_gap (d : ℕ) (hd : 4 ≤ d) :
    geometricGap d - geometricGap 4 < gapCuatroInf := by
  have h := geometricGap_lt_deltaInf d hd
  rw [gapCuatroInf_eq_deltaInf_sub_geometricGap_cuatro]
  linarith

/-- La gap es el límite exacto del ascenso de la cadena desde `d = 4`:
`C_Nava(d) − C_Nava(4) → Δ` cuando `d → ∞` (límite de Szegő, `D8`). -/
theorem ascenso_tiende_a_gap :
    Tendsto (fun d : ℕ => CoherenceConstant d - CoherenceConstant 4) atTop (nhds gapCuatroInf) := by
  unfold gapCuatroInf
  exact limite_szego_CoherenceConstant.sub_const (CoherenceConstant 4)

/-- Forma compacta: la gap es positiva y menor que `δ_∞`. -/
theorem gapCuatroInf_positiva_y_acotada :
    0 < gapCuatroInf ∧ gapCuatroInf < deltaInf :=
  ⟨gapCuatroInf_pos, gapCuatroInf_lt_deltaInf⟩

end GapCuatroAsintota

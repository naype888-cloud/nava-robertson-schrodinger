import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# D33 — La fase toro activa el thick: thick es el defect geométrico

La seed tiene thick/defect `0`. En fase toro, el thick es exactamente la
imagen no negativa extendida del defect geométrico `δ_geom(d)`. La fase toro
se considera en el régimen de ruptura `d ≥ 4`, donde D8 ya demuestra que el
defect es estrictamente positivo. Así, `thick` y `defect` son dos lecturas
del mismo dato, no magnitudes independientes.

Las afirmaciones sobre temperatura son una interpretación del modelo: en la
seed su valor es `0`, y en el toro se lee el mismo defect positivo. Este
módulo no pretende probar una ley termodinámica.
-/

noncomputable section

namespace FaseToroThick

inductive FaseThick
  | seed
  | toro
  deriving DecidableEq

/-- Thick/defect de fase. En la seed vale cero; en toro es `δ_geom(d)`. -/
def thickFase : FaseThick → ℕ → ENNReal
  | .seed, _ => 0
  | .toro, d => ENNReal.ofReal (Gnomon.geometricGap d)

@[simp] theorem thick_seed_es_cero (d : ℕ) : thickFase .seed d = 0 := rfl

theorem thick_toro_eq_defect (d : ℕ) :
    thickFase .toro d = ENNReal.ofReal (Gnomon.geometricGap d) := rfl

theorem thick_toro_positivo (d : ℕ) (hd : 4 ≤ d) : 0 < thickFase .toro d := by
  simp [thickFase, ENNReal.ofReal_pos, Gnomon.geometricGap_pos_of_four_le d hd]

theorem thick_toro_no_cero (d : ℕ) (hd : 4 ≤ d) : thickFase .toro d ≠ 0 :=
  ne_of_gt (thick_toro_positivo d hd)

theorem thick_toro_no_infinito (d : ℕ) : thickFase .toro d ≠ ⊤ := by
  simp [thickFase]

/-- En toro y desde la primera ruptura, thick/defect es positivo y finito. -/
theorem toro_entre_cero_e_infinito (d : ℕ) (hd : 4 ≤ d) :
    0 < thickFase .toro d ∧ thickFase .toro d < ⊤ :=
  ⟨thick_toro_positivo d hd,
    lt_top_iff_ne_top.mpr (thick_toro_no_infinito d)⟩

/-- En el régimen d≥4, thick cero caracteriza exactamente la seed. -/
theorem thickFase_eq_zero_iff (fase : FaseThick) (d : ℕ) (hd : 4 ≤ d) :
    thickFase fase d = 0 ↔ fase = .seed := by
  cases fase with
  | seed => simp
  | toro => simp [thick_toro_no_cero d hd]

/-- En el régimen de ruptura, thick no nulo fuerza la fase toro. -/
theorem sin_cero_absoluto_implica_toro {fase : FaseThick} {d : ℕ}
    (h : thickFase fase d ≠ 0) : fase = .toro := by
  cases fase with
  | seed => exact absurd (thick_seed_es_cero d) h
  | toro => rfl

/-- Lectura térmica del modelo: temperatura seed `0`; en toro la
temperatura se identifica con el mismo defect geométrico. -/
def temperaturaModelo (fase : FaseThick) (d : ℕ) : ℝ :=
  match fase with
  | .seed => 0
  | .toro => Gnomon.geometricGap d

@[simp] theorem temperatura_seed_cero (d : ℕ) :
    temperaturaModelo .seed d = 0 := rfl

theorem temperatura_toro_positiva (d : ℕ) (hd : 4 ≤ d) :
    0 < temperaturaModelo .toro d :=
  Gnomon.geometricGap_pos_of_four_le d hd

end FaseToroThick

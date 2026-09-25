import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!
# El exceso sobre el límite de Szegő

Corolario aritmético directo de la monotonía (`D9_Monotonia.lean`) y el
límite de Szegő (`D8_Szego.lean`): el "exceso" `CoherenceConstantInf - CoherenceConstant(d)` —cuánto
le falta a `CoherenceConstant(d)` para alcanzar el límite `C∞`— es positivo, máximo
exactamente en `d = 4`, estrictamente decreciente en `d`, y se disuelve a
`0`. No es un pilar nuevo: es la misma cadena de `D9_Monotonia.lean` leída
desde el lado del remanente en vez del valor mismo.
-/

open Filter
open scoped Topology

namespace Gnomon

/-- El exceso de coherencia: cuánto le falta a `CoherenceConstant(d)` para alcanzar el
límite de Szegő `C∞`. -/
noncomputable def excesoGap (d : ℕ) : ℝ := CoherenceConstantInf - CoherenceConstant d

/-- El exceso es siempre positivo: `CoherenceConstant(d)` nunca alcanza `C∞` a `d`
finito. -/
theorem excesoGap_pos (d : ℕ) (hd : 4 ≤ d) : 0 < excesoGap d := by
  unfold excesoGap
  linarith [CoherenceConstant_lt_CoherenceConstantInf d hd]

/-- El exceso es estrictamente decreciente en `d`, heredado de la
monotonía de `CoherenceConstant`. -/
theorem excesoGap_strictAnti {a b : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b) (hab : a < b) :
    excesoGap b < excesoGap a := by
  unfold excesoGap
  linarith [CoherenceConstant_strictMonoOn_ge_four ha hb hab]

/-- El exceso máximo de toda la cola `d ≥ 4` se alcanza exactamente en
`d = 4`: el mínimo global de `CoherenceConstant` es el techo del exceso. -/
theorem excesoGap_le_four (d : ℕ) (hd : 4 ≤ d) :
    excesoGap d ≤ excesoGap 4 := by
  unfold excesoGap
  linarith [CoherenceConstant_four_le d hd]

/-- El exceso se apaga por completo: `CoherenceConstantInf − CoherenceConstant(d) → 0`, acotado
arriba
por `excesoGap 4` y llevado a `0` por el límite de Szegő. -/
theorem excesoGap_tendsto_zero :
    Tendsto (fun d : ℕ => excesoGap d) atTop (𝓝 0) := by
  unfold excesoGap
  have h : Tendsto (fun d : ℕ => CoherenceConstantInf - CoherenceConstant d) atTop (𝓝
      (CoherenceConstantInf - CoherenceConstantInf)) :=
    limite_szego_CoherenceConstant.const_sub CoherenceConstantInf
  simpa using h

end Gnomon

import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality
import NavaRobertsonIndependent.Mathematics.D17_IntrinsicTransportDefect

/-!
# D22 — La interfaz `PosicionTransporte` instanciada con `(T_d, P_d)`

`D17` fija la interfaz algebraica `PosicionTransporte d`: una evaluación
Robertson–Schrödinger cuya saturación equivale a la condición de Niven sobre el
camino, `cos²(π/(d+1)) = (d−1)/4`. Este módulo construye esa evaluación con los
operadores concretos: `σ_A = ‖T_d ψ*‖`, `σ_B = ‖P_d ψ*‖`, covarianza `0` y
conmutador `c/2` con `c = −2/(d−1)`. El campo `saturacion_iff_camino` deja de ser
una hipótesis: se demuestra con `D21` (saturación exactamente en `d = 2, 3`) y
`D7` (Niven). El defect intrínseco de `D17` coincide con el defect de Gram
`(C_Nava(d)² − 1)/(d−1)²` de `D20`.
-/

noncomputable section

open Gnomon TransportePosicion RNavaVarianzaFiedler EscalonGramCoherenceConstant Robertson1929
  DinamicaElemental

namespace NavaRobertsonSchrodingerEDUI

/-- Evaluación Robertson–Schrödinger de `(T_d, P_d)` en `ψ*`. -/
def evaluacionTdPd {d : ℕ} (hd : 2 ≤ d) : EvaluacionSchrodinger where
  sigmaA := ‖TdOp d (psiStar d)‖
  sigmaB := ‖PdOp d (psiStar d)‖
  covarianza := 0
  conmutador := commutatorConstant d / 2
  sigmaA_nonneg := norm_nonneg _
  sigmaB_nonneg := norm_nonneg _
  cota_cuadratica := by
    have hb := gap_eq_geometricGap hd
    have hδ := geometricGap_nonneg hd
    have hp := commutatorConstant_half_sq_pos hd
    have hnn : 0 ≤ (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) :=
      mul_nonneg hp.le (mul_nonneg hδ (by linarith))
    rw [varianza_T hd, varianza_P hd, covarianza_cero hd] at hb
    nlinarith

/-- El defect intrínseco de la evaluación de `(T_d, P_d)` es el defect de Gram. -/
theorem defectIntrinseco_TdPd_eq_defectGram {d : ℕ} (hd : 2 ≤ d) :
    defectIntrinseco (evaluacionTdPd hd) = defectGram d := by
  have hb := gap_eq_defectGram hd
  rw [varianza_T hd, varianza_P hd, covarianza_cero hd] at hb
  unfold defectIntrinseco evaluacionTdPd
  simp only
  linarith

/-- La evaluación satura exactamente en `d = 2, 3`. -/
theorem saturada_TdPd_iff {d : ℕ} (hd : 2 ≤ d) :
    SaturadaSchrodinger (evaluacionTdPd hd) ↔ d = 2 ∨ d = 3 := by
  have h := saturacion_iff hd
  rw [varianza_T hd, varianza_P hd, covarianza_cero hd] at h
  unfold SaturadaSchrodinger evaluacionTdPd
  simp only
  rw [← h]
  constructor <;> intro h' <;> linarith

/-- **Instancia real de la interfaz de `D17`.** El campo `saturacion_iff_camino` es
aquí un teorema, no una hipótesis. -/
def posicionTransporteTdPd {d : ℕ} (hd : 2 ≤ d) : PosicionTransporte d where
  evaluacion := evaluacionTdPd hd
  saturacion_iff_camino := by
    rw [saturada_TdPd_iff hd]
    exact (Gnomon.saturacion_iff d hd).symm

/-- Para `d ≥ 4`, el defect de `(T_d, P_d)` en `ψ*` es estrictamente positivo. -/
theorem defect_pos_TdPd {d : ℕ} (hd : 4 ≤ d) :
    0 < (posicionTransporteTdPd (by omega : 2 ≤ d)).defect :=
  (posicionTransporteTdPd (by omega : 2 ≤ d)).defect_pos hd

end NavaRobertsonSchrodingerEDUI

end

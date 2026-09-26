/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality
public import NavaRobertsonIndependent.Mathematics.D17_IntrinsicTransportDefect

/-!
# D22 — `PositionTransport` instantiated with `(T_d, P_d)`

The interface `PositionTransport d` of `D17` built from the concrete operators:
`σ_A = ‖T_d ψ*‖`, `σ_B = ‖P_d ψ*‖`, covariance `0`, commutator `c/2`, `c = −2/(d−1)`. The field
`saturated_iff_path` is proved (`D21`, `D7`), and the intrinsic defect of `D17` is the Gram
defect `(C_Nava(d)² − 1)/(d−1)²` of `D20`.

## Main results

- `NRSInequality.positionTransportTdPd` : the instance.
- `NRSInequality.defect_pos_TdPd` : for `d ≥ 4` the defect is positive.
-/

@[expose] public noncomputable section

open Gnomon TransportPosition FiedlerPositionVariance GramStep Robertson1929
  IntrinsicDefect

namespace NRSInequality

/-- The Robertson–Schrödinger evaluation of `(T_d, P_d)` at `ψ*`. -/
def evaluationTdPd {d : ℕ} (hd : 2 ≤ d) : SchrodingerEvaluation where
  sigmaA := ‖TdOp d (psiStar d)‖
  sigmaB := ‖PdOp d (psiStar d)‖
  covariance := 0
  commutator := commutatorConstant d / 2
  sigmaA_nonneg := norm_nonneg _
  sigmaB_nonneg := norm_nonneg _
  quadratic_bound := by
    have hb := gap_eq_geometricGap hd
    have hδ := geometricGap_nonneg hd
    have hp := commutatorConstant_half_sq_pos hd
    have hnn : 0 ≤ (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) :=
      mul_nonneg hp.le (mul_nonneg hδ (by linarith))
    rw [variance_T hd, variance_P hd, covariance_eq_zero hd] at hb
    nlinarith

/-- The intrinsic defect of `(T_d, P_d)` is the Gram defect. -/
theorem intrinsicDefect_TdPd_eq_defectGram {d : ℕ} (hd : 2 ≤ d) :
    intrinsicDefect (evaluationTdPd hd) = defectGram d := by
  have hb := gap_eq_defectGram hd
  rw [variance_T hd, variance_P hd, covariance_eq_zero hd] at hb
  unfold intrinsicDefect evaluationTdPd
  simp only
  linarith

/-- The evaluation saturates iff `d = 2, 3`. -/
theorem saturated_TdPd_iff {d : ℕ} (hd : 2 ≤ d) :
    SchrodingerSaturated (evaluationTdPd hd) ↔ d = 2 ∨ d = 3 := by
  have h := saturation_iff hd
  rw [variance_T hd, variance_P hd, covariance_eq_zero hd] at h
  unfold SchrodingerSaturated evaluationTdPd
  simp only
  rw [← h]
  constructor <;> intro h' <;> linarith

/-- The instance of the interface of `D17`; `saturated_iff_path` is a theorem here. -/
def positionTransportTdPd {d : ℕ} (hd : 2 ≤ d) : PositionTransport d where
  evaluation := evaluationTdPd hd
  saturated_iff_path := by
    rw [saturated_TdPd_iff hd]
    exact (Gnomon.saturation_iff d hd).symm

/-- For `d ≥ 4` the defect of `(T_d, P_d)` at `ψ*` is positive. -/
theorem defect_pos_TdPd {d : ℕ} (hd : 4 ≤ d) :
    0 < (positionTransportTdPd (by omega : 2 ≤ d)).defect :=
  (positionTransportTdPd (by omega : 2 ≤ d)).defect_pos hd

end NRSInequality

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23d_BandWidth

/-!
# D23e — Maximal transport and maximal tension exclude each other

On `H_d`, `⟨T_d⟩ ≤ 1` (`mean_T_le_one`), attained by the fundamental sine mode without phases
(`mean_T_sineVec`), and `⟨K_d⟩ ≤ 2/(d−1)` (`D23b`), attained by `ψ*` (`D21`). At each top the
other quantity is `0`, so no state reaches both.

## Main results

- `TransportTensionExclusion.tension_eq_zero_of_mean_T_eq_one` : `⟨T_d⟩ = 1 → ⟨K_d⟩ = 0`.
- `TransportTensionExclusion.mean_T_eq_zero_of_maxTension` : `⟨K_d⟩ = 2/(d−1) → ⟨T_d⟩ = 0`.
- `TransportTensionExclusion.not_both_max` : no unit state has both.
-/

@[expose] public noncomputable section

namespace TransportTensionExclusion

open NRSInequality TransportPosition EigenvectorSaturation NearMaxTension
  SpectralExtremal BandWidth

/-! ## 1. The top of transport -/

theorem mean_T_le_one {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    mean (TdOp d) ψ ≤ 1 :=
  le_of_abs_le (abs_mean_le (norm_TdOp_le hd) hψ)

/-- The fundamental sine mode, no phases, unnormalized. -/
def sineVecRaw (d : ℕ) (hd : 1 ≤ d) : Hd d :=
  WithLp.toLp 2 (sineMode d ⟨0, hd⟩)

/-- The normalized fundamental sine mode. -/
def sineVec (d : ℕ) (hd : 1 ≤ d) : Hd d :=
  ((‖sineVecRaw d hd‖ : ℂ)⁻¹) • sineVecRaw d hd

theorem sineVecRaw_ne_zero {d : ℕ} (hd : 1 ≤ d) : sineVecRaw d hd ≠ 0 := by
  intro h
  apply sineMode_ne_zero hd ⟨0, hd⟩
  simpa [sineVecRaw] using congrArg WithLp.ofLp h

theorem norm_sineVec {d : ℕ} (hd : 1 ≤ d) : ‖sineVec d hd‖ = 1 := by
  have hn : ‖sineVecRaw d hd‖ ≠ 0 := norm_ne_zero_iff.mpr (sineVecRaw_ne_zero hd)
  rw [sineVec, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

/-- The fundamental sine mode is fixed by transport: `T_d v = v`. -/
theorem TdOp_sineVecRaw {d : ℕ} (hd : 2 ≤ d) :
    TdOp d (sineVecRaw d (by omega)) = sineVecRaw d (by omega) := by
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  have hA := Ad_sineMode (d := d) (by omega) ⟨0, by omega⟩
  have hang : (2 * Real.cos (modeAngle d ⟨0, by omega⟩) : ℂ) = (rho d : ℂ) := by
    simp [modeAngle, rho]
  rw [hang] at hA
  apply (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).injective
  change (Td d).mulVec (sineMode d ⟨0, by omega⟩) = sineMode d ⟨0, by omega⟩
  rw [Td_eq_smul_Ad, Matrix.smul_mulVec, hA]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem TdOp_sineVec {d : ℕ} (hd : 2 ≤ d) :
    TdOp d (sineVec d (by omega)) = sineVec d (by omega) := by
  rw [sineVec, map_smul, TdOp_sineVecRaw hd]

/-- The top of transport is attained. -/
theorem mean_T_sineVec {d : ℕ} (hd : 2 ≤ d) : mean (TdOp d) (sineVec d (by omega)) = 1 := by
  unfold mean
  rw [TdOp_sineVec hd, inner_self_eq_norm_sq_to_K, norm_sineVec]
  simp

/-! ## 2. Maximal transport gives zero tension -/

/-- If `⟨T_d⟩ = 1` at a unit state, the state is fixed by `T_d`. -/
theorem fixed_of_mean_T_eq_one {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : mean (TdOp d) ψ = 1) : TdOp d ψ = ψ := by
  have hre : (inner ℂ (TdOp d ψ) ψ).re = 1 := by
    rw [← inner_conj_symm, Complex.conj_re]
    exact h
  have hT := norm_TdOp_le hd ψ
  rw [hψ] at hT
  have hsq : ‖TdOp d ψ - ψ‖ ^ 2 ≤ 0 := by
    rw [@norm_sub_sq ℂ, RCLike.re_to_complex, hre, hψ]
    nlinarith [norm_nonneg (TdOp d ψ)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (TdOp d ψ - ψ)]))

/-- **Maximal transport gives zero tension.** -/
theorem tension_eq_zero_of_mean_T_eq_one {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : mean (TdOp d) ψ = 1) : tension d ψ = 0 := by
  have hfix := fixed_of_mean_T_eq_one hd hψ h
  have h0 := expectation_commutator_eq_zero (TdOp d) (PdOp d) (TdOp_isSymmetric d) (a := 1)
    (by rw [hfix, Complex.ofReal_one, one_smul])
  unfold tension KdOp observableTension opCommutator
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right,
    h0, mul_zero, Complex.zero_re]

/-! ## 3. Maximal tension gives zero transport -/

/-- **Maximal tension gives zero transport.** -/
theorem mean_T_eq_zero_of_maxTension {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : tension d ψ = 2 / ((d : ℝ) - 1)) : mean (TdOp d) ψ = 0 := by
  obtain ⟨c, hc, rfl⟩ := maxTension_state_eq_phase hd ψ hψ h
  rw [mean_phase _ _ c hc, mean_T hd]

/-! ## 4. Exclusion -/

/-- No unit state has `⟨T_d⟩ = 1` and `⟨K_d⟩ = 2/(d−1)`. -/
theorem not_both_max {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    ¬ (mean (TdOp d) ψ = 1 ∧ tension d ψ = 2 / ((d : ℝ) - 1)) := by
  rintro ⟨hT, hK⟩
  have := mean_T_eq_zero_of_maxTension hd hψ hK
  rw [hT] at this
  exact one_ne_zero this

end TransportTensionExclusion

end

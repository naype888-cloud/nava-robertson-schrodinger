/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation

/-!
# D23b — The surplus at intermediate states

`D21` computes the Robertson–Schrödinger surplus at maximal tension: the Gram defect
`defectGram d`. `D23` shows that below the maximum some states saturate. Here the surplus is
studied at every unit state as a function of its tension `⟨K_d⟩`. The `ε` below comes from
compactness of the unit sphere, not in closed form.

## Main results

- `NearMaxTension.surplus_eq` : `surplus ψ = Var T_d · Var P_d − (cov² + ⟨K_d⟩²/4)`.
- `NearMaxTension.tension_le` : `⟨K_d⟩ ≤ 2/(d−1)` at every unit state.
- `NearMaxTension.surplus_near_max` : states with tension near `2/(d−1)` have surplus near
  `defectGram d`.
- `NearMaxTension.strict_inequality_band` : for `d ≥ 4` the inequality is strict on a band
  `2/(d−1) − ε < ⟨K_d⟩`.
-/

@[expose] public noncomputable section

namespace NearMaxTension

open NRSInequality TransportPosition EigenvectorSaturation
  GramStep SpectralExtremal

/-- The tension `⟨K_d⟩ = Re ⟪ψ, K_d ψ⟫`. -/
def tension (d : ℕ) (ψ : Hd d) : ℝ :=
  (inner ℂ ψ (KdOp d ψ)).re

/-- The Robertson–Schrödinger surplus of `(T_d, P_d)` at `ψ`: the Gram defect. -/
abbrev surplus (d : ℕ) (ψ : Hd d) : ℝ :=
  gramDefectAt (TdOp d) (PdOp d) ψ

/-! ## 1. The surplus -/

/-- The surplus with the state's own floor `⟨K_d⟩²/4`. -/
theorem surplus_eq (d : ℕ) (ψ : Hd d) :
    surplus d ψ =
      variance (TdOp d) ψ * variance (PdOp d) ψ -
        (covariance (TdOp d) (PdOp d) ψ ^ 2 + tension d ψ ^ 2 / 4) := by
  rw [surplus, gramDefectAt_eq_gap,
    imPart_eq_im_inner (TdOp_isSymmetric d) (PdOp_isSymmetric d), tension, re_inner_KdOp]
  ring

theorem surplus_phase {d : ℕ} (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    surplus d (c • ψ) = surplus d ψ := by
  unfold surplus gramDefectAt
  rw [variance_phase _ _ _ hc, variance_phase _ _ _ hc, centered_phase _ _ _ hc,
    centered_phase _ _ _ hc, inner_smul_left, inner_smul_right, norm_mul, norm_mul,
    Complex.norm_conj, hc]
  simp

theorem tension_psiStar {d : ℕ} (hd : 2 ≤ d) : tension d (psiStar d) = 2 / ((d : ℝ) - 1) := by
  unfold tension
  rw [KdOp_fiedlerVec d hd, inner_smul_right, inner_self_eq_norm_sq_to_K,
    norm_psiStar hd]
  simpa using Complex.ofReal_re (2 / ((d : ℝ) - 1))

theorem surplus_psiStar {d : ℕ} (hd : 2 ≤ d) : surplus d (psiStar d) = defectGram d := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  rw [← gap_eq_defectGram hd, surplus_eq, tension_psiStar hd, commutatorConstant_half_sq hd]
  field_simp
  ring

/-- The tension of a unit state is at most `2/(d−1)`. -/
theorem tension_le {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    tension d ψ ≤ 2 / ((d : ℝ) - 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  have hle := expectation_le_specRadius (KdOp d) (KdOp_isSymmetric d) ψ hψ
  rw [specRadius_KdOp_eq_step d hd] at hle
  exact (Complex.re_le_norm _).trans hle

/-! ## 2. Continuity -/

theorem continuous_mean {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) : Continuous (mean A) :=
  Complex.continuous_re.comp (continuous_id.inner (LinearMap.continuous_of_finiteDimensional A))

theorem continuous_centered {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) : Continuous (centered A) :=
  (LinearMap.continuous_of_finiteDimensional A).sub
    ((Complex.continuous_ofReal.comp (continuous_mean A)).smul continuous_id)

theorem continuous_variance {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) : Continuous (variance A) :=
  (continuous_centered A).norm.pow 2

theorem continuous_tension (d : ℕ) : Continuous (tension d) :=
  Complex.continuous_re.comp
    (continuous_id.inner (LinearMap.continuous_of_finiteDimensional (KdOp d)))

theorem continuous_surplus (d : ℕ) : Continuous (surplus d) :=
  ((continuous_variance _).mul (continuous_variance _)).sub
    (((continuous_centered _).inner (continuous_centered _)).norm.pow 2)

/-! ## 3. The surplus near the maximum -/

/-- Unit states with tension near `2/(d−1)` have surplus near `defectGram d`. -/
theorem surplus_near_max {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ ψ : Hd d, ‖ψ‖ = 1 → 2 / ((d : ℝ) - 1) - ε < tension d ψ →
      |surplus d ψ - defectGram d| < η := by
  set S : Set (Hd d) :=
    Metric.sphere 0 1 ∩ {ψ | η ≤ |surplus d ψ - defectGram d|} with hS
  have hSc : IsCompact S :=
    (isCompact_sphere 0 1).inter_right
      (isClosed_le continuous_const ((continuous_surplus d).sub continuous_const).abs)
  have hfuera : ∀ ψ : Hd d, ‖ψ‖ = 1 → ψ ∉ S → |surplus d ψ - defectGram d| < η := by
    intro ψ hψ hnS
    by_contra h
    exact hnS ⟨by simpa using hψ, le_of_not_gt h⟩
  rcases S.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ψ hψ _ => hfuera ψ hψ (by simp [he])⟩
  obtain ⟨ψ₀, hψ₀S, hmax⟩ := hSc.exists_isMaxOn hne (continuous_tension d).continuousOn
  have hψ₀ : ‖ψ₀‖ = 1 := by simpa using hψ₀S.1
  have hlt : tension d ψ₀ < 2 / ((d : ℝ) - 1) := by
    refine lt_of_le_of_ne (tension_le hd ψ₀ hψ₀) fun heq => ?_
    obtain ⟨c, hc, rfl⟩ := maxTension_state_eq_phase hd ψ₀ hψ₀ heq
    have h := hψ₀S.2
    simp only [Set.mem_ofPred_eq, surplus_phase _ c hc, surplus_psiStar hd, sub_self,
      abs_zero] at h
    linarith
  refine ⟨2 / ((d : ℝ) - 1) - tension d ψ₀, by linarith, fun ψ hψ hK => hfuera ψ hψ ?_⟩
  intro hψS
  have := hmax hψS
  simp only [Set.mem_ofPred_eq] at this
  linarith

/-- For `d ≥ 4` there is `ε > 0` such that every unit state with `⟨K_d⟩ > 2/(d−1) − ε`
satisfies Robertson–Schrödinger strictly, with floor `⟨K_d⟩²/4`. -/
theorem strict_inequality_band {d : ℕ} (hd : 4 ≤ d) :
    ∃ ε > 0, ∀ ψ : Hd d, ‖ψ‖ = 1 → 2 / ((d : ℝ) - 1) - ε < tension d ψ →
      covariance (TdOp d) (PdOp d) ψ ^ 2 + tension d ψ ^ 2 / 4 <
        variance (TdOp d) ψ * variance (PdOp d) ψ := by
  obtain ⟨ε, hε, h⟩ := surplus_near_max (by omega : 2 ≤ d) (gramStep_gram_pos hd)
  refine ⟨ε, hε, fun ψ hψ hK => ?_⟩
  have h1 := h ψ hψ hK
  have h2 : 0 < surplus d ψ := by
    have := neg_abs_le (surplus d ψ - defectGram d)
    linarith
  rw [surplus_eq] at h2
  linarith

end NearMaxTension

end

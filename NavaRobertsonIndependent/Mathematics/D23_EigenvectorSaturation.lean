/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality

/-!
# D23 — Robertson–Schrödinger saturates on eigenvectors of `A − iλB`

With the mean, fluctuation, variance and covariance of `D21`, Robertson–Schrödinger holds with
equality exactly when the Gram defect
`gramDefectAt A B ψ = Var A · Var B − ‖⟪Ãψ, B̃ψ⟫‖² = Var A · Var B − (cov² + Im²)` vanishes.

## Main results

- `EigenvectorSaturation.gramDefectAt_eq_zero_iff` : the defect vanishes iff `Var B = 0` or
  `Ãψ = c • B̃ψ`.
- `EigenvectorSaturation.saturation_of_eigenvector` : if `(A − iλB)ψ = μψ`, `λ` real, then
  `cov = 0` and `Var A · Var B = Im²`.
- `EigenvectorSaturation.eigenvector_not_maxTension` : for `d ≥ 4` no unit eigenvector of
  `T_d − iλP_d` has maximal tension; there the inequality is strict (`D21`).
- `EigenvectorSaturation.variance_mul_variance_pos` : if `⟨K_d⟩ ≠ 0`,
  `Var T · Var P ≥ ⟨K_d⟩²/4 > 0`.
- `EigenvectorSaturation.expectation_commutator_eq_zero` : if `Aψ = aψ`, `⟨[A, B]⟩ = 0`; the
  basis vectors have `⟨K_d⟩ = 0` and variance product `0` (`not_comm_and_variance_mul_eq_zero`).
-/

@[expose] public noncomputable section

namespace EigenvectorSaturation

open NRSInequality TransportPosition SpectralExtremal

/-- `Im ⟪Ãψ, B̃ψ⟫`; for symmetric `A`, `B`, `⟪ψ, [A, B] ψ⟫ = 2i Im ⟪Ãψ, B̃ψ⟫`. -/
def imPart {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  (inner ℂ (centered A ψ) (centered B ψ)).im

/-- The Gram defect of the fluctuation vectors: the Robertson–Schrödinger gap. -/
def gramDefectAt {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  variance A ψ * variance B ψ - ‖inner ℂ (centered A ψ) (centered B ψ)‖ ^ 2

/-! ## 1. The Gram defect -/

theorem gramDefectAt_eq_gap {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    gramDefectAt A B ψ =
      variance A ψ * variance B ψ - (covariance A B ψ ^ 2 + imPart A B ψ ^ 2) := by
  unfold gramDefectAt covariance imPart
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gramDefectAt_nonneg {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    0 ≤ gramDefectAt A B ψ := by
  unfold gramDefectAt variance
  have h := norm_inner_le_norm (𝕜 := ℂ) (centered A ψ) (centered B ψ)
  have h2 : ‖inner ℂ (centered A ψ) (centered B ψ)‖ ^ 2 ≤
      (‖centered A ψ‖ * ‖centered B ψ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [h2]

/-- If `Ãψ = c • B̃ψ`, the Gram defect vanishes. -/
theorem gramDefectAt_eq_zero_of_parallel {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d)
    (c : ℂ) (h : centered A ψ = c • centered B ψ) : gramDefectAt A B ψ = 0 := by
  unfold gramDefectAt variance
  rw [h, inner_smul_left, norm_smul, norm_mul, inner_self_eq_norm_sq_to_K]
  simp [mul_pow]
  ring

/-- The Gram defect vanishes iff `B` does not fluctuate at `ψ` or `Ãψ = c • B̃ψ`. -/
theorem gramDefectAt_eq_zero_iff {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    gramDefectAt A B ψ = 0 ↔
      variance B ψ = 0 ∨ ∃ c : ℂ, centered A ψ = c • centered B ψ := by
  constructor
  · intro h
    unfold gramDefectAt variance at h
    rw [sub_eq_zero] at h
    have hn : ‖inner ℂ (centered B ψ) (centered A ψ)‖ = ‖centered B ψ‖ * ‖centered A ψ‖ := by
      rw [norm_inner_symm, mul_comm]
      exact ((sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp (by rw [mul_pow]; exact h)).symm
    rcases ((norm_inner_eq_norm_tfae ℂ _ _).out 1 3).mp hn with hw | ⟨r, hr⟩
    · left
      unfold variance
      rw [hw, norm_zero]
      norm_num
    · exact Or.inr ⟨r, hr⟩
  · rintro (hb | ⟨c, hc⟩)
    · unfold variance at hb
      have hw : centered B ψ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
      unfold gramDefectAt variance
      rw [hw]
      simp
    · exact gramDefectAt_eq_zero_of_parallel A B ψ c hc

/-! ## 2. Eigenvectors of `A − iλB` -/

theorem covariance_eq_zero_of_annihilated {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d)
    (lam : ℝ) (h : centered A ψ = (Complex.I * lam) • centered B ψ) :
    covariance A B ψ = 0 := by
  unfold covariance
  rw [h, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- For symmetric `A`, `⟪ψ, A ψ⟫` is real. -/
theorem inner_self_apply_real {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} (hA : A.IsSymmetric) (ψ : Hd d) :
    inner ℂ ψ (A ψ) = ((mean A ψ : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (inner ℂ ψ (A ψ)) = inner ℂ ψ (A ψ) := by
    rw [inner_conj_symm]
    exact hA ψ ψ
  exact (Complex.conj_eq_iff_re.mp h).symm

/-- An eigenvector of `A − iλB` is annihilated by `Ã − iλB̃`. -/
theorem annihilated_of_eigenvector {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : Hd d} (hψ : ‖ψ‖ = 1) (lam : ℝ) (μ : ℂ)
    (h : A ψ - (Complex.I * lam) • B ψ = μ • ψ) :
    centered A ψ = (Complex.I * lam) • centered B ψ := by
  have hμ : μ = (mean A ψ : ℂ) - (Complex.I * lam) * (mean B ψ : ℂ) := by
    have h1 : inner ℂ ψ (A ψ - (Complex.I * lam) • B ψ) = μ := by
      rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
      simp
    rw [← h1, inner_sub_right, inner_smul_right, inner_self_apply_real hA,
      inner_self_apply_real hB]
  have h2 : A ψ - (Complex.I * lam) • B ψ =
      ((mean A ψ : ℂ) - (Complex.I * lam) * (mean B ψ : ℂ)) • ψ := by
    rw [h, hμ]
  unfold centered
  calc A ψ - (mean A ψ : ℂ) • ψ
      = (A ψ - (Complex.I * lam) • B ψ) + (Complex.I * lam) • B ψ - (mean A ψ : ℂ) • ψ := by
        abel
    _ = ((mean A ψ : ℂ) - (Complex.I * lam) * (mean B ψ : ℂ)) • ψ +
          (Complex.I * lam) • B ψ - (mean A ψ : ℂ) • ψ := by rw [h2]
    _ = (Complex.I * lam) • (B ψ - (mean B ψ : ℂ) • ψ) := by
        simp only [sub_smul, mul_smul, smul_sub]
        abel

/-- **Saturation on eigenvectors.** If `ψ` is a unit vector with `(A − iλB)ψ = μψ`, `λ` real,
`A`, `B` symmetric, then `cov = 0` and `Var A · Var B = Im²`. -/
theorem saturation_of_eigenvector {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : Hd d} (hψ : ‖ψ‖ = 1) (lam : ℝ) (μ : ℂ)
    (h : A ψ - (Complex.I * lam) • B ψ = μ • ψ) :
    covariance A B ψ = 0 ∧ variance A ψ * variance B ψ = imPart A B ψ ^ 2 := by
  have hc := annihilated_of_eigenvector hA hB hψ lam μ h
  have hcov := covariance_eq_zero_of_annihilated A B ψ lam hc
  have hg := gramDefectAt_eq_zero_of_parallel A B ψ _ hc
  rw [gramDefectAt_eq_gap, hcov] at hg
  exact ⟨hcov, by linarith⟩

/-! ## 3. Eigenvectors of `T_d − iλP_d` do not have maximal tension -/

/-- For symmetric `A`, `B`, `Im ⟪Ãψ, B̃ψ⟫ = Im ⟪Aψ, Bψ⟫`. -/
theorem imPart_eq_im_inner {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : Hd d) :
    imPart A B ψ = (inner ℂ (A ψ) (B ψ)).im := by
  have ha : inner ℂ (A ψ) ψ = ((mean A ψ : ℝ) : ℂ) := by
    rw [← inner_conj_symm (A ψ) ψ, inner_self_apply_real hA]
    simp
  have hb : inner ℂ ψ (B ψ) = ((mean B ψ : ℝ) : ℂ) := inner_self_apply_real hB ψ
  have hn : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have key : inner ℂ (centered A ψ) (centered B ψ) =
      inner ℂ (A ψ) (B ψ) - ((mean A ψ * mean B ψ * (2 - ‖ψ‖ ^ 2) : ℝ) : ℂ) := by
    unfold centered
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, ha, hb, hn,
      Complex.conj_ofReal]
    push_cast
    ring
  unfold imPart
  rw [key, Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- `Re ⟪ψ, K_d ψ⟫ = −2 Im ⟪T_d ψ, P_d ψ⟫`. -/
theorem re_inner_KdOp (d : ℕ) (ψ : Hd d) :
    (inner ℂ ψ (KdOp d ψ)).re = -2 * (inner ℂ (TdOp d ψ) (PdOp d ψ)).im := by
  have h1 : inner ℂ ψ (TdOp d (PdOp d ψ)) = inner ℂ (TdOp d ψ) (PdOp d ψ) :=
    (TdOp_isSymmetric d ψ (PdOp d ψ)).symm
  have h2 : inner ℂ ψ (PdOp d (TdOp d ψ)) = inner ℂ (PdOp d ψ) (TdOp d ψ) :=
    (PdOp_isSymmetric d ψ (TdOp d ψ)).symm
  have h3 : (inner ℂ (PdOp d ψ) (TdOp d ψ)).im = -(inner ℂ (TdOp d ψ) (PdOp d ψ)).im := by
    rw [← inner_conj_symm (PdOp d ψ) (TdOp d ψ), Complex.conj_im]
  unfold KdOp observableTension opCommutator
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right,
    inner_sub_right, h1, h2]
  simp [Complex.mul_re, Complex.sub_im]
  linarith [h3]

/-- For `d ≥ 4`, if `ψ` is a unit vector with `(T_d − iλP_d)ψ = μψ`, `λ` real, then
`⟨K_d⟩ ≠ 2/(d−1)`. -/
theorem eigenvector_not_maxTension {d : ℕ} (hd : 4 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (lam : ℝ) (μ : ℂ) (h : TdOp d ψ - (Complex.I * lam) • PdOp d ψ = μ • ψ) :
    (inner ℂ ψ (KdOp d ψ)).re ≠ 2 / ((d : ℝ) - 1) := by
  intro hK
  obtain ⟨hcov, hprod⟩ :=
    saturation_of_eigenvector (TdOp_isSymmetric d) (PdOp_isSymmetric d) hψ lam μ h
  have hstrict := strict_inequality_of_maxTension hd ψ hψ hK
  rw [hcov, hprod, imPart_eq_im_inner (TdOp_isSymmetric d) (PdOp_isSymmetric d)] at hstrict
  have hIm : (inner ℂ (TdOp d ψ) (PdOp d ψ)).im = -(1 / ((d : ℝ) - 1)) := by
    have h4 := re_inner_KdOp d ψ
    rw [hK, show 2 / ((d : ℝ) - 1) = 2 * (1 / ((d : ℝ) - 1)) by ring] at h4
    linarith
  rw [hIm, commutatorConstant_half_sq (by omega), show (-(1 / ((d : ℝ) - 1))) ^ 2 = 1 / ((d : ℝ) -
      1) ^ 2 by
    rw [neg_sq, div_pow, one_pow]] at hstrict
  simp at hstrict

/-! ## 4. With transport the uncertainty is positive -/

/-- `Var T_d · Var P_d ≥ ⟨K_d⟩²/4` at every state. -/
theorem variance_mul_variance_ge (d : ℕ) (ψ : Hd d) :
    ((inner ℂ ψ (KdOp d ψ)).re) ^ 2 / 4 ≤ variance (TdOp d) ψ * variance (PdOp d) ψ := by
  have hg := gramDefectAt_nonneg (TdOp d) (PdOp d) ψ
  rw [gramDefectAt_eq_gap,
    imPart_eq_im_inner (TdOp_isSymmetric d) (PdOp_isSymmetric d)] at hg
  rw [re_inner_KdOp d ψ]
  nlinarith [sq_nonneg (covariance (TdOp d) (PdOp d) ψ)]

/-- If `⟨K_d⟩ ≠ 0`, `Var T_d · Var P_d > 0`. -/
theorem variance_mul_variance_pos (d : ℕ) (ψ : Hd d)
    (h : (inner ℂ ψ (KdOp d ψ)).re ≠ 0) :
    0 < variance (TdOp d) ψ * variance (PdOp d) ψ :=
  lt_of_lt_of_le (by positivity) (variance_mul_variance_ge d ψ)

/-- A unit eigenvector with real eigenvalue has zero fluctuation vector. -/
theorem centered_eigenvector {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} {ψ : Hd d} (hψ : ‖ψ‖ = 1) (a : ℝ)
    (h : A ψ = (a : ℂ) • ψ) : centered A ψ = 0 := by
  have hm : mean A ψ = a := by
    unfold mean
    rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp
  unfold centered
  rw [hm, h, sub_self]

/-- If `A ψ = a ψ`, `A` symmetric, `a` real, then `⟪ψ, [A, B] ψ⟫ = 0` for every `B`. -/
theorem expectation_commutator_eq_zero {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (hA : A.IsSymmetric)
    {ψ : Hd d} (a : ℝ) (h : A ψ = (a : ℂ) • ψ) :
    inner ℂ ψ (A (B ψ) - B (A ψ)) = 0 := by
  have h1 : inner ℂ ψ (A (B ψ)) = inner ℂ (A ψ) (B ψ) := (hA ψ (B ψ)).symm
  rw [inner_sub_right, h1, h, inner_smul_left, map_smul, inner_smul_right]
  simp

/-- Each basis vector is an eigenvector of `P_d`. -/
theorem Pd_basis (d : ℕ) (j : Fin d) :
    PdOp d (EuclideanSpace.single j 1) =
      ((posCoord d j : ℝ) : ℂ) • (EuclideanSpace.single j (1 : ℂ) : Hd d) := by
  ext i
  simp [PdOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Pd]
  by_cases h : i = j <;> simp [h]

/-- At each basis vector `Var P_d = 0` and the Gram defect is `0`. -/
theorem basis_state_saturates (d : ℕ) (j : Fin d) :
    variance (PdOp d) (EuclideanSpace.single j 1) = 0 ∧
      gramDefectAt (TdOp d) (PdOp d) (EuclideanSpace.single j 1) = 0 := by
  have hn : ‖(EuclideanSpace.single j (1 : ℂ) : Hd d)‖ = 1 := by simp
  have hc := centered_eigenvector hn (posCoord d j) (Pd_basis d j)
  have hv : variance (PdOp d) (EuclideanSpace.single j 1) = 0 := by
    unfold variance
    rw [hc]
    simp
  exact ⟨hv, (gramDefectAt_eq_zero_iff _ _ _).mpr (Or.inl hv)⟩

/-- `T_d` and `P_d` do not commute, yet some unit vector with `⟨K_d⟩ = 0` has variance
product `0`. -/
theorem not_comm_and_variance_mul_eq_zero (d : ℕ) (hd : 2 ≤ d) :
    opCommutator (TdOp d) (PdOp d) ≠ 0 ∧
      ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ variance (TdOp d) ψ * variance (PdOp d) ψ = 0 := by
  constructor
  · intro hC
    have hK : KdOp d = 0 := by
      unfold KdOp observableTension
      rw [hC, smul_zero]
    have h1 := KdOp_fiedlerVec d hd
    rw [hK, LinearMap.zero_apply] at h1
    have hn := norm_psiStar hd
    have h2 : ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) = 0 ∨ fiedlerVec d = 0 :=
      smul_eq_zero.mp h1.symm
    rcases h2 with h2 | h2
    · have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have : (2 / ((d : ℝ) - 1) : ℝ) = 0 := by exact_mod_cast h2
      have hpos : (0 : ℝ) < 2 / ((d : ℝ) - 1) := div_pos (by norm_num) hd1
      linarith
    · have : ‖psiStar d‖ = 0 := by
        change ‖fiedlerVec d‖ = 0
        rw [h2, norm_zero]
      linarith
  · let j : Fin d := ⟨0, by omega⟩
    refine ⟨EuclideanSpace.single j 1, by simp, ?_⟩
    rw [(basis_state_saturates d j).1, mul_zero]

end EigenvectorSaturation

end

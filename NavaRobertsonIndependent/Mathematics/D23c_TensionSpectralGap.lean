/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap

/-!
# D23c — The spectral gap of `K_d`: tension controls the distance to `ψ*`

The top eigenvalue `2/(d−1)` of `K_d` is simple (`D21`); here is the explicit gap to the rest
of the spectrum, `λ_k = (2/(d−1)) cos θ_k / cos θ_0` with `θ_k = (k+1)π/(d+1)`.

## Main results

- `BandWidth.eigenvalueK_le_second` : every other eigenvalue is at most `secondEigenvalue d`.
- `BandWidth.gapK_pos` : `gapK d = 2/(d−1) − secondEigenvalue d > 0`.
- `BandWidth.dist_le_deficit` : `gapK d · ‖ψ − ⟪ψ*, ψ⟫ ψ*‖² ≤ 2/(d−1) − ⟨K_d⟩_ψ`.
-/

@[expose] public noncomputable section

namespace BandWidth

open NRSInequality TransportPosition EigenvectorSaturation NearMaxTension
  SpectralExtremal

/-! ## 1. Spectral expansion of the quadratic form -/

section Generico

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem re_inner_eq_sum (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (v : H) :
    (inner ℂ v (K v)).re =
      ∑ i, hK.eigenvalues rfl i * ‖(hK.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
  rw [← (hK.eigenvectorBasis rfl).repr.inner_map_map v (K v), PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hK.eigenvectorBasis_apply_self_apply rfl v i, ← smul_eq_mul, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem norm_sq_eq_sum (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (v : H) :
    ‖v‖ ^ 2 = ∑ i, ‖(hK.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
  rw [← (hK.eigenvectorBasis rfl).repr.norm_map, EuclideanSpace.norm_sq_eq]

end Generico

/-! ## 2. The second eigenvalue and the gap -/

/-- A bound for every eigenvalue of `K_d` other than the top one. -/
def secondEigenvalue (d : ℕ) : ℝ :=
  (2 / ((d : ℝ) - 1)) * Real.cos (2 * Real.pi / ((d : ℝ) + 1)) /
    Real.cos (Real.pi / ((d : ℝ) + 1))

/-- The spectral gap of `K_d`. -/
def gapK (d : ℕ) : ℝ := 2 / ((d : ℝ) - 1) - secondEigenvalue d

theorem cos_fiedlerAngle_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Real.cos (Real.pi / ((d : ℝ) + 1)) := by
  have h := rho_pos d hd
  unfold rho at h
  linarith

theorem eigenvalueK_eq {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    eigenvalueK d k =
      (((2 / ((d : ℝ) - 1)) * Real.cos (modeAngle d k) /
        Real.cos (Real.pi / ((d : ℝ) + 1)) : ℝ) : ℂ) := by
  have hc := (cos_fiedlerAngle_pos hd).ne'
  simp only [eigenvalueK, eigenvalueAd, rho]
  push_cast
  field_simp

theorem eigenvalueK_le_second {d : ℕ} (hd : 2 ≤ d) (k : Fin d) (hk : k.val ≠ 0) :
    (eigenvalueK d k).re ≤ secondEigenvalue d := by
  rw [eigenvalueK_eq hd, Complex.ofReal_re, secondEigenvalue]
  have hc := cos_fiedlerAngle_pos hd
  have hdpos : 0 < 2 / ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_pos (by norm_num) (by linarith)
  apply div_le_div_of_nonneg_right _ hc.le
  apply mul_le_mul_of_nonneg_left _ hdpos.le
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (modeAngle_mem_Icc k).2
  unfold modeAngle
  have hk1 : (2 : ℝ) ≤ (k.val : ℝ) + 1 := by
    have : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
    have : (1 : ℝ) ≤ k.val := by exact_mod_cast this
    linarith
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hk1 (by positivity)

theorem gapK_pos {d : ℕ} (hd : 2 ≤ d) : 0 < gapK d := by
  have hc := cos_fiedlerAngle_pos hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < 2 / ((d : ℝ) - 1) := div_pos (by norm_num) (by linarith)
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  have hlt : Real.cos (2 * Real.pi / ((d : ℝ) + 1)) < Real.cos (Real.pi / ((d : ℝ) + 1)) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
    · rw [mul_div_assoc]
      have : 0 < Real.pi / ((d : ℝ) + 1) := by positivity
      linarith
  unfold gapK secondEigenvalue
  rw [mul_div_assoc]
  have hq : Real.cos (2 * Real.pi / ((d : ℝ) + 1)) / Real.cos (Real.pi / ((d : ℝ) + 1)) < 1 :=
    (div_lt_one hc).mpr hlt
  nlinarith

/-! ## 3. States orthogonal to `ψ*` -/

/-- If `φ ⊥ ψ*`, its tension is at most `secondEigenvalue d · ‖φ‖²`. -/
theorem tension_orthogonal_le {d : ℕ} (hd : 2 ≤ d) (φ : Hd d)
    (hφ : inner ℂ (psiStar d) φ = 0) :
    tension d φ ≤ secondEigenvalue d * ‖φ‖ ^ 2 := by
  have hK := KdOp_isSymmetric d
  unfold tension
  rw [re_inner_eq_sum (KdOp d) hK, norm_sq_eq_sum (KdOp d) hK, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨k, hk⟩ := KdOp_eigenvalue_exhausts_spectrum hd (hK.hasEigenvalue_eigenvalues rfl i)
  by_cases hk0 : k.val = 0
  · -- top eigenvalue: the eigenvector is a multiple of `ψ*`, so the coordinate is `0`
    have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
    have hv : KdOp d (hK.eigenvectorBasis rfl i) =
        ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • hK.eigenvectorBasis rfl i := by
      rw [hK.apply_eigenvectorBasis rfl i, hk, hk', eigenvalueK_fundamental d hd]
    obtain ⟨c, hc⟩ := top_eigenvector_smul hd _ hv
    have h0 : (hK.eigenvectorBasis rfl).repr φ i = 0 := by
      rw [OrthonormalBasis.repr_apply_apply, hc, inner_smul_left, hφ, mul_zero]
    simp [h0]
  · have hle : hK.eigenvalues rfl i ≤ secondEigenvalue d := by
      have := eigenvalueK_le_second hd k hk0
      rw [← hk] at this
      simpa using this
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

/-! ## 4. Tension controls the distance to `ψ*` -/

theorem inner_psiStar_self {d : ℕ} (hd : 2 ≤ d) : inner ℂ (psiStar d) (psiStar d) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_psiStar hd]
  simp

/-- The component of `ψ` orthogonal to `ψ*`. -/
def orthComponent (d : ℕ) (ψ : Hd d) : Hd d :=
  ψ - inner ℂ (psiStar d) ψ • psiStar d

theorem orthComponent_perp {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) :
    inner ℂ (psiStar d) (orthComponent d ψ) = 0 := by
  rw [orthComponent, inner_sub_right, inner_smul_right, inner_psiStar_self hd, mul_one,
    sub_self]

/-- `‖ψ‖² = |⟪ψ*, ψ⟫|² + ‖φ‖²`. -/
theorem norm_sq_decomp {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) :
    ‖ψ‖ ^ 2 = ‖inner ℂ (psiStar d) ψ‖ ^ 2 + ‖orthComponent d ψ‖ ^ 2 := by
  set a := inner ℂ (psiStar d) ψ
  set φ := orthComponent d ψ
  have hψ : ψ = a • psiStar d + φ := by simp [φ, orthComponent, a]
  have h0 : inner ℂ (a • psiStar d) φ = 0 := by
    rw [inner_smul_left, orthComponent_perp hd, mul_zero]
  conv_lhs => rw [hψ]
  rw [@norm_add_sq ℂ, h0, norm_smul, norm_psiStar hd]
  simp

/-- `⟨K⟩_ψ = (2/(d−1)) |⟪ψ*, ψ⟫|² + ⟨K⟩_φ`. -/
theorem tension_decomp {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) :
    tension d ψ = 2 / ((d : ℝ) - 1) * ‖inner ℂ (psiStar d) ψ‖ ^ 2 +
      tension d (orthComponent d ψ) := by
  set a := inner ℂ (psiStar d) ψ
  set φ := orthComponent d ψ
  have hψ : ψ = a • psiStar d + φ := by simp [φ, orthComponent, a]
  have hperp : inner ℂ (psiStar d) φ = 0 := orthComponent_perp hd ψ
  have hperp' : inner ℂ φ (psiStar d) = 0 := by
    rw [← inner_conj_symm, hperp, map_zero]
  have hKφ : inner ℂ (psiStar d) (KdOp d φ) = 0 := by
    rw [← KdOp_isSymmetric d, KdOp_fiedlerVec d hd, inner_smul_left, hperp, mul_zero]
  have hK := KdOp_fiedlerVec d hd
  unfold tension
  conv_lhs => rw [hψ]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hK, hKφ, hperp', inner_psiStar_self hd, mul_zero, add_zero, mul_one]
  rw [Complex.add_re]
  congr 1
  rw [mul_comm a, mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  rw [zero_add]

/-- **Tension controls the distance to `ψ*`.** For every unit state,
`gapK d · ‖ψ − ⟪ψ*, ψ⟫ ψ*‖² ≤ 2/(d−1) − ⟨K_d⟩_ψ`. -/
theorem dist_le_deficit {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    gapK d * ‖orthComponent d ψ‖ ^ 2 ≤ 2 / ((d : ℝ) - 1) - tension d ψ := by
  have hn := norm_sq_decomp hd ψ
  have ht := tension_decomp hd ψ
  have hφ := tension_orthogonal_le hd _ (orthComponent_perp hd ψ)
  rw [hψ, one_pow] at hn
  unfold gapK
  have e : 2 / ((d : ℝ) - 1) = 2 / ((d : ℝ) - 1) *
      (‖inner ℂ (psiStar d) ψ‖ ^ 2 + ‖orthComponent d ψ‖ ^ 2) := by
    rw [← hn, mul_one]
  nlinarith

end BandWidth

end

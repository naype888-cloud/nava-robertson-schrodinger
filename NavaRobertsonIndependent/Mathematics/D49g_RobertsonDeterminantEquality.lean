/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D49_RobertsonDeterminant

/-!
# D49g — When Robertson 1934 is an equality

`D49` proves `‖det B‖ ≤ det A` for `A` positive definite and `A ± B` positive semidefinite, by
conjugating with the normalizer `T` of `A` (`T A Tᴴ = 1`): `K = T B Tᴴ` has its eigenvalues in
`[−1, 1]` and `det B = det K · det A`. Equality forces every eigenvalue of `K` to be `±1`, so
`K² = 1` and `(1 + K)(1 − K) = 0`, that is

  `(A + B) A⁻¹ (A − B) = 0`.

The columns of `A⁻¹(A − B)` lie in the kernel of `A + B`, those of `A⁻¹(A + B)` in the kernel of
`A − B`, and they add up to twice the identity: the two kernels span everything. When
`A − B = (A + B)ᵀ` the two kernels have the same dimension, so each has at least half of it.
For Robertson's matrices this is the kernel of the Gram matrix `Σ + iΩ`: relations among the
fluctuation vectors.

## Main results

- `Matrix.PosDef.add_mul_inv_mul_sub_eq_zero` : equality gives `(A + B) A⁻¹ (A − B) = 0`.
- `Matrix.exists_add_of_norm_det_eq` : every vector is a sum of kernel vectors of `A + B` and
  of `A − B`.
- `Matrix.finrank_ker_transpose` : `Gᵀ` and `G` have kernels of the same dimension.
-/

@[expose] public noncomputable section

namespace Matrix

open scoped ComplexOrder
open Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The equality case.** If `‖det B‖ = det A`, then `(A + B) A⁻¹ (A − B) = 0`. -/
theorem PosDef.add_mul_inv_mul_sub_eq_zero {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.IsHermitian) (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef)
    (heq : ‖B.det‖ = (A.det).re) : (A + B) * A⁻¹ * (A - B) = 0 := by
  set T := hA.normalizer
  have hT := hA.normalizer_mul_mul_conjTranspose
  set K := T * B * Tᴴ
  have hK : K.IsHermitian := by
    simp only [IsHermitian, K, conjTranspose_mul, conjTranspose_conjTranspose, hB.eq, mul_assoc]
  have hm : (1 - K).PosSemidef := by
    have := h₁.mul_mul_conjTranspose_same T
    rwa [mul_sub, sub_mul, hT] at this
  have hp : (1 + K).PosSemidef := by
    have := h₂.mul_mul_conjTranspose_same T
    rwa [mul_add, add_mul, hT] at this
  -- `det K` has norm one
  have hdetA : A.det = ((∏ i, hA.1.eigenvalues i : ℝ) : ℂ) := by
    rw [hA.1.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have hprod : 0 < ∏ i, hA.1.eigenvalues i := Finset.prod_pos fun i _ => hA.eigenvalues_pos i
  have hBK : B.det = K.det * A.det := by
    have h := congrArg det hT
    rw [det_mul, det_mul, det_one] at h
    simp only [K, det_mul]
    linear_combination (-B.det) * h
  have hK1 : ‖K.det‖ = 1 := by
    rw [hBK, norm_mul, hdetA, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hprod] at heq
    calc ‖K.det‖ = ‖K.det‖ * (∏ i, hA.1.eigenvalues i) / ∏ i, hA.1.eigenvalues i := by
          field_simp
      _ = 1 := by rw [heq, div_self hprod.ne']
  -- every eigenvalue of `K` is `±1`
  have hle (i : n) : |hK.eigenvalues i| ≤ 1 := hK.abs_eigenvalues_le_one hm hp i
  have habs (j : n) : |hK.eigenvalues j| = 1 := by
    rw [hK.det_eq_prod_eigenvalues, norm_prod] at hK1
    simp only [RCLike.norm_ofReal] at hK1
    by_contra hj
    have hlt : |hK.eigenvalues j| < 1 := lt_of_le_of_ne (hle j) hj
    have hrest : ∏ i ∈ Finset.univ.erase j, |hK.eigenvalues i| ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => hle i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)] at hK1
    nlinarith [abs_nonneg (hK.eigenvalues j)]
  -- hence `K² = 1`
  have hKK : K * K = 1 := by
    set U : Matrix n n ℂ := (hK.eigenvectorUnitary : Matrix n n ℂ)
    have hUU : star U * U = 1 := coe_star_mul_self _
    have hUU' : U * star U = 1 := coe_mul_star_self _
    have hKU : K = U * diagonal (fun i => (hK.eigenvalues i : ℂ)) * star U := by
      conv_lhs => rw [hK.spectral_theorem, conjStarAlgAut_apply]
      rfl
    have hD : diagonal (fun i => (hK.eigenvalues i : ℂ)) *
        diagonal (fun i => (hK.eigenvalues i : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      ext i
      have := habs i
      have h2 : hK.eigenvalues i ^ 2 = 1 := by rw [← sq_abs, this, one_pow]
      exact_mod_cast (by nlinarith [h2] : hK.eigenvalues i * hK.eigenvalues i = 1)
    rw [hKU]
    calc U * diagonal (fun i => (hK.eigenvalues i : ℂ)) * star U *
          (U * diagonal (fun i => (hK.eigenvalues i : ℂ)) * star U)
        = U * (diagonal (fun i => (hK.eigenvalues i : ℂ)) * (star U * U) *
          diagonal (fun i => (hK.eigenvalues i : ℂ))) * star U := by simp only [mul_assoc]
      _ = 1 := by rw [hUU, mul_one, hD, mul_one, hUU']
  -- `T` is invertible and `A⁻¹ = Tᴴ T`
  have hdetT : IsUnit T.det := by
    have h := congrArg det hT
    rw [det_mul, det_mul, det_one] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at h
    simp at h
  have hdetTH : IsUnit Tᴴ.det := by
    rw [det_conjTranspose]
    exact hdetT.star
  have hAinv : A⁻¹ = Tᴴ * T := by
    have h1 : T * A * Tᴴ * (Tᴴ)⁻¹ = (Tᴴ)⁻¹ := by rw [hT, one_mul]
    rw [mul_assoc (T * A), mul_nonsing_inv _ hdetTH, mul_one] at h1
    have h2 : Tᴴ * (T * A) = 1 := by
      rw [h1]
      exact mul_nonsing_inv _ hdetTH
    exact inv_eq_left_inv (by rw [← mul_assoc] at h2; exact h2)
  -- conclude
  have hX : T * ((A + B) * A⁻¹ * (A - B)) * Tᴴ = 0 := by
    have e1 : T * (A + B) * Tᴴ = 1 + K := by rw [mul_add, add_mul, hT]
    have e2 : T * (A - B) * Tᴴ = 1 - K := by rw [mul_sub, sub_mul, hT]
    calc T * ((A + B) * A⁻¹ * (A - B)) * Tᴴ
        = (T * (A + B) * Tᴴ) * (T * (A - B) * Tᴴ) := by rw [hAinv]; simp only [mul_assoc]
      _ = 0 := by rw [e1, e2, add_mul, one_mul, mul_sub, mul_one, hKK]; abel
  have hback : T⁻¹ * (T * ((A + B) * A⁻¹ * (A - B)) * Tᴴ) * (Tᴴ)⁻¹ = (A + B) * A⁻¹ * (A - B) := by
    simp only [← mul_assoc]
    rw [nonsing_inv_mul _ hdetT, one_mul, mul_assoc _ Tᴴ, mul_nonsing_inv _ hdetTH, mul_one]
  rw [← hback, hX, mul_zero, zero_mul]

/-- **The two kernels span everything.** At equality every vector is `y + z` with
`(A + B) y = 0` and `(A − B) z = 0`. -/
theorem exists_add_of_norm_det_eq {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.IsHermitian)
    (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef) (heq : ‖B.det‖ = (A.det).re)
    (x : n → ℂ) : ∃ y z, (A + B) *ᵥ y = 0 ∧ (A - B) *ᵥ z = 0 ∧ x = y + z := by
  have hP := hA.add_mul_inv_mul_sub_eq_zero hB h₁ h₂ heq
  have hM := hA.add_mul_inv_mul_sub_eq_zero hB.neg (by rwa [sub_neg_eq_add])
    (by rwa [← sub_eq_add_neg]) (by rw [det_neg, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, heq])
  rw [sub_neg_eq_add, ← sub_eq_add_neg] at hM
  have hAi : A⁻¹ * A = 1 := nonsing_inv_mul _ (hA.isUnit.map detMonoidHom)
  refine ⟨(A⁻¹ * (A - B)) *ᵥ ((2 : ℂ)⁻¹ • x), (A⁻¹ * (A + B)) *ᵥ ((2 : ℂ)⁻¹ • x), ?_, ?_, ?_⟩
  · rw [mulVec_mulVec, ← mul_assoc, hP, zero_mulVec]
  · rw [mulVec_mulVec, ← mul_assoc, hM, zero_mulVec]
  · rw [← add_mulVec, ← mul_add, sub_add_add_cancel, mul_add, hAi, add_mulVec, one_mulVec,
      ← add_smul]
    norm_num

omit [DecidableEq n] in
/-- `G` and `Gᵀ` have kernels of the same dimension. -/
theorem finrank_ker_transpose (G : Matrix n n ℂ) :
    Module.finrank ℂ (LinearMap.ker Gᵀ.mulVecLin) =
      Module.finrank ℂ (LinearMap.ker G.mulVecLin) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker Gᵀ.mulVecLin
  have h3 : Gᵀ.rank = G.rank := rank_transpose G
  rw [rank] at h3
  rw [rank] at h3
  omega

end Matrix

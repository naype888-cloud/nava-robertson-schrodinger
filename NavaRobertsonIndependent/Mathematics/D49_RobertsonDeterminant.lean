/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef

/-!
# D49 — Robertson 1934: several observables

Robertson's relation for a finite family of observables (Phys. Rev. 46, 794 (1934)). For a
state `Φ` and operators `L_j` on `ℂ^ι`, the centered vectors `c_j = L_j Φ − ⟨L_j⟩ Φ` have Gram
matrix `Σ + iΩ`, with `Σ_jk = Re ⟨c_j, c_k⟩` the covariance matrix and `Ω_jk = Im ⟨c_j, c_k⟩`.
A Gram matrix is positive semidefinite, and so is its transpose `Σ − iΩ`; a determinant bound
for positive matrices then gives `|det Ω| ≤ det Σ`. For two observables this is `D2`'s
Robertson–Schrödinger; for the pairs of the three axes it is `D49b`.

## Main results

- `Matrix.PosDef.norm_det_le_re_det` : `‖det B‖ ≤ det A` when `A` is positive definite and
  `A ± B` are positive semidefinite.
- `Matrix.abs_det_le_det_of_posSemidef` : `|det W| ≤ det S` when `S ± iW` are positive
  semidefinite.
- `RobertsonDeterminant.gram_centeredG` : `Σ + iΩ` is the Gram matrix of the centered vectors.
- `RobertsonDeterminant.robertson_det` : `|det Ω| ≤ det Σ`, for every state and every finite
  family of operators.
- `RobertsonDeterminant.tensionG_eq` : for symmetric `L`, `M`, `⟨i[L, M]⟩ = −2 Im ⟨c_L, c_M⟩`.
-/

@[expose] public noncomputable section

/-! ## 1. A determinant bound for positive matrices -/

namespace Matrix

open scoped ComplexOrder
open Unitary Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix `T` with `T A Tᴴ = 1` for a positive definite `A`: the inverse square roots of the
eigenvalues of `A` times the adjoint of its eigenvector unitary. -/
def PosDef.normalizer {A : Matrix n n ℂ} (hA : A.PosDef) : Matrix n n ℂ :=
  diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i))⁻¹ : ℂ)) *
    star (hA.1.eigenvectorUnitary : Matrix n n ℂ)

theorem PosDef.normalizer_mul_mul_conjTranspose {A : Matrix n n ℂ} (hA : A.PosDef) :
    hA.normalizer * A * hA.normalizerᴴ = 1 := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  set α := hA.1.eigenvalues
  set D : Matrix n n ℂ := diagonal fun i => ((Real.sqrt (α i))⁻¹ : ℂ)
  have hUU : star U * U = 1 := coe_star_mul_self _
  have hAU : A = U * diagonal (fun i => (α i : ℂ)) * star U := by
    conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply]
    rfl
  have hDD : D * diagonal (fun i => (α i : ℂ)) * D = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    have hs : (Real.sqrt (α i) : ℂ) ^ 2 = α i := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (hA.eigenvalues_pos i).le]
    have hne : (Real.sqrt (α i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
    rw [← hs]
    field_simp
  have hT : hA.normalizer = D * star U := rfl
  have hTH : hA.normalizerᴴ = U * D := by
    simp [hT, D, conjTranspose_mul, diagonal_conjTranspose, Pi.star_def, star_eq_conjTranspose]
  rw [hTH, hT, hAU]
  calc D * star U * (U * diagonal (fun i => (α i : ℂ)) * star U) * (U * D)
      = D * (star U * U) * diagonal (fun i => (α i : ℂ)) * (star U * U) * D := by
        simp only [mul_assoc]
    _ = 1 := by rw [hUU, mul_one, mul_one, hDD]

/-- The eigenvalues of a hermitian `K` with `1 − K` and `1 + K` positive semidefinite lie in
`[−1, 1]`. -/
theorem IsHermitian.abs_eigenvalues_le_one {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (hm : (1 - K).PosSemidef) (hp : (1 + K).PosSemidef) (i : n) : |hK.eigenvalues i| ≤ 1 := by
  set v := hK.eigenvectorBasis i
  have hv : star (v : n → ℂ) ⬝ᵥ (v : n → ℂ) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hK.eigenvectorBasis.orthonormal.1 i]
    simp
  have h0 := hm.re_dotProduct_nonneg (v : n → ℂ)
  have h1 := hp.re_dotProduct_nonneg (v : n → ℂ)
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hK.mulVec_eigenvectorBasis, dotProduct_smul,
    hv] at h0
  rw [add_mulVec, one_mulVec, dotProduct_add, hK.mulVec_eigenvectorBasis, dotProduct_smul,
    hv] at h1
  simp at h0 h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If `A` is positive definite, `B` hermitian and `A − B`, `A + B` positive semidefinite, then
`‖det B‖ ≤ re (det A)`: conjugating by the normalizer of `A` puts `B` between `−1` and `1`. -/
theorem PosDef.norm_det_le_re_det {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.IsHermitian)
    (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef) : ‖B.det‖ ≤ (A.det).re := by
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
  have hdetK : ‖K.det‖ ≤ 1 := by
    rw [hK.det_eq_prod_eigenvalues, norm_prod]
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [RCLike.norm_ofReal]
    exact hK.abs_eigenvalues_le_one hm hp i
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
  rw [hBK, norm_mul, hdetA, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hprod]
  nlinarith [norm_nonneg K.det]

omit [Fintype n] in
theorem map_ofReal_add_smul_one (S : Matrix n n ℝ) (ε : ℝ) :
    (S + ε • 1).map ((↑) : ℝ → ℂ) = S.map ((↑) : ℝ → ℂ) + (ε : ℂ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- For real `S` and `W`, if `S − iW` and `S + iW` are positive semidefinite then
`|det W| ≤ det S` (`norm_det_le_re_det` at `S + ε`, then `ε → 0`). -/
theorem abs_det_le_det_of_posSemidef {S W : Matrix n n ℝ}
    (h₁ : (S.map ((↑) : ℝ → ℂ) - Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef)
    (h₂ : (S.map ((↑) : ℝ → ℂ) + Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef) :
    |W.det| ≤ S.det := by
  have hS : (S.map ((↑) : ℝ → ℂ)).PosSemidef := by
    have h := (h₁.add h₂).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
    convert h using 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    ring
  have hB : (Complex.I • W.map ((↑) : ℝ → ℂ)).IsHermitian := by
    rw [show Complex.I • W.map ((↑) : ℝ → ℂ) =
      S.map ((↑) : ℝ → ℂ) - (S.map ((↑) : ℝ → ℂ) - Complex.I • W.map ((↑) : ℝ → ℂ)) by abel]
    exact hS.1.sub h₁.1
  have key : ∀ ε : ℝ, 0 < ε → |W.det| ≤ (S + ε • 1).det := by
    intro ε hε
    have hε1 : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
      PosSemidef.one.smul (Complex.zero_le_real.mpr hε.le)
    have hA : ((S + ε • 1).map ((↑) : ℝ → ℂ)).PosDef := by
      rw [map_ofReal_add_smul_one]
      exact PosDef.posSemidef_add hS (PosDef.one.smul (Complex.zero_lt_real.mpr hε))
    have h₁' : ((S + ε • 1).map ((↑) : ℝ → ℂ) - Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef := by
      rw [map_ofReal_add_smul_one, add_sub_right_comm]
      exact h₁.add hε1
    have h₂' : ((S + ε • 1).map ((↑) : ℝ → ℂ) + Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef := by
      rw [map_ofReal_add_smul_one, add_right_comm]
      exact h₂.add hε1
    have h := hA.norm_det_le_re_det hB h₁' h₂'
    have hW : (W.map ((↑) : ℝ → ℂ)).det = (W.det : ℂ) := (RingHom.map_det Complex.ofRealHom W).symm
    have hSε : ((S + ε • 1).map ((↑) : ℝ → ℂ)).det = ((S + ε • 1).det : ℂ) :=
      (RingHom.map_det Complex.ofRealHom _).symm
    rwa [det_smul, hW, hSε, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
  have hlim : Tendsto (fun ε : ℝ => (S + ε • (1 : Matrix n n ℝ)).det) (𝓝[>] 0) (𝓝 S.det) := by
    have hc : Continuous fun ε : ℝ => (S + ε • (1 : Matrix n n ℝ)).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

end Matrix

/-! ## 2. Several observables -/

namespace RobertsonDeterminant

open Matrix PathGraph3DNRS SpectralExtremal
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι]

/-- The covariance matrix `Σ_jk = Re ⟨c_j, c_k⟩` of a family of operators at `Φ`. -/
def covMatrix (L : κ → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ ι) :
    Matrix κ κ ℝ :=
  of fun j k => covarianceG (L j) (L k) Φ

/-- The matrix `Ω_jk = Im ⟨c_j, c_k⟩` of a family of operators at `Φ`. -/
def imMatrix (L : κ → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ ι) :
    Matrix κ κ ℝ :=
  of fun j k => (inner ℂ (centeredG (L j) Φ) (centeredG (L k) Φ)).im

variable (L : κ → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ ι)

/-- `Σ + iΩ` is the Gram matrix of the centered vectors. -/
theorem gram_centeredG :
    gram ℂ (fun j => centeredG (L j) Φ) =
      (covMatrix L Φ).map ((↑) : ℝ → ℂ) + Complex.I • (imMatrix L Φ).map ((↑) : ℝ → ℂ) := by
  ext j k
  simp only [gram, of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, covMatrix,
    imMatrix, covarianceG, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-- `Σ − iΩ` is the transpose of the Gram matrix. -/
theorem transpose_gram_centeredG :
    (gram ℂ (fun j => centeredG (L j) Φ))ᵀ =
      (covMatrix L Φ).map ((↑) : ℝ → ℂ) - Complex.I • (imMatrix L Φ).map ((↑) : ℝ → ℂ) := by
  ext j k
  simp only [transpose_apply, gram, of_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, covMatrix, imMatrix, covarianceG, smul_eq_mul]
  apply Complex.ext <;> simp
  · rw [← inner_conj_symm (centeredG (L k) Φ), Complex.conj_re]
  · rw [← inner_conj_symm (centeredG (L k) Φ), Complex.conj_im]

/-- **Robertson 1934**: for every state and every finite family of operators,
`|det Ω| ≤ det Σ`. -/
theorem robertson_det [Fintype κ] [DecidableEq κ] :
    |(imMatrix L Φ).det| ≤ (covMatrix L Φ).det := by
  have hG := posSemidef_gram ℂ fun j => centeredG (L j) Φ
  exact abs_det_le_det_of_posSemidef
    (by rw [← transpose_gram_centeredG]; exact hG.transpose)
    (by rw [← gram_centeredG]; exact hG)

variable {L Φ}

/-- For symmetric `L`, `M` the tension `⟨i[L, M]⟩` is `−2 Im ⟨c_L, c_M⟩`. -/
theorem tensionG_eq {L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hL : L.IsSymmetric)
    (hM : M.IsSymmetric) :
    tensionG L M Φ = -2 * (inner ℂ (centeredG L Φ) (centeredG M Φ)).im := by
  have hrL : (inner ℂ (L Φ) Φ).im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [inner_conj_symm]
    exact (hL Φ Φ).symm
  have hrM : (inner ℂ Φ (M Φ)).im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [inner_conj_symm]
    exact hM Φ Φ
  have hsw : (inner ℂ (M Φ) (L Φ)).im = -(inner ℂ (L Φ) (M Φ)).im := by
    rw [← inner_conj_symm (L Φ) (M Φ), Complex.conj_im, neg_neg]
  simp only [tensionG, observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, centeredG, inner_smul_right, inner_sub_left, inner_sub_right,
    inner_smul_left, Complex.conj_ofReal]
  rw [← hL Φ (M Φ), ← hM Φ (L Φ)]
  simp [Complex.mul_re, Complex.mul_im, hrL, hrM, hsw, ← Complex.ofReal_pow]
  ring

end RobertsonDeterminant

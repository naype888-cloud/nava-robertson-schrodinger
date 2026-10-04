/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49h_DeterminantEqualityRelation

/-!
# D49j — An axis on its own keeps det|NRS³ strict in the band

If the fluctuation vectors of the `z` axis are orthogonal to those of `x` and `y`, the `6 × 6`
matrices split into a `4 × 4` block for `(x, y)` and a `2 × 2` block for `z`:

  `det Σ = det Σ_xy · det Σ_z`,  `|det Ω| = |det Ω_xy| · |det Ω_z|`.

Robertson 1934 on the four observables of `x` and `y` gives `|det Ω_xy| ≤ det Σ_xy` (`D49`), and
on `z` the gap is the defect of the axis, `det Σ_z − |det Ω_z| = defect_z`, positive in the band
for every state (`D49e`). So the bound is strict, whatever the entanglement between `x` and `y`.

This holds in particular when `z` splits off, `Φ = w ⊗ χ` with `w` on `z` and `χ` on `(x, y)`:
the case where `x` and `y` are glued together and the third axis is left on its own. The band
does the work through that axis.

## Main results

- `SplitAxis.robertson_det_strict_of_orthogonal` : orthogonal `z` fluctuations and speeds in the
  band give `|det Ω| < det Σ`.
- `SplitAxis.robertson_det_strict_of_split` : the same when `Φ = w ⊗ χ` splits off `z`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition NearMaxTension GroupVelocity PathGraph3DNRS CauchyGram
open RobertsonDeterminant RobertsonDeterminant3D AxisDefectEntangled VelocityBand
open DeterminantEqualityRelation SpectralExtremal CubePythagoras

namespace SplitAxis

/-- The six indices split into the four of `(x, y)` and the two of `z`. -/
def splitZ : (Fin 2 × Fin 2) ⊕ Fin 2 ≃ Fin 2 × Fin 3 where
  toFun
    | .inl q => (q.1, q.2.castSucc)
    | .inr s => (s, 2)
  invFun p := if h : p.2 = 2 then .inr p.1 else .inl (p.1, ⟨p.2, by omega⟩)
  left_inv := by
    rintro (⟨s, i⟩ | s)
    · have : i.castSucc ≠ (2 : Fin 3) := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [this]
    · simp
  right_inv := by
    rintro ⟨s, i⟩
    by_cases h : i = 2
    · subst h; simp
    · simp [h]

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- The four observables of `x` and `y`. -/
def famXY (dx dy dz : ℕ) (q : Fin 2 × Fin 2) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  pairs dx dy dz (q.1, q.2.castSucc)

/-- The two observables of `z`. -/
def famZ (dx dy dz : ℕ) (s : Fin 2) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := pairs dx dy dz (s, 2)

theorem castSucc_ne_two (i : Fin 2) : i.castSucc ≠ (2 : Fin 3) := by
  intro h; have := congrArg Fin.val h; simp at this; omega

variable (horth : ∀ s t (i : Fin 2), inner ℂ (fluct Φ (s, i.castSucc)) (fluct Φ (t, 2)) = 0)
include horth

theorem horth' (s t : Fin 2) (i : Fin 2) :
    inner ℂ (fluct Φ (t, 2)) (fluct Φ (s, i.castSucc)) = 0 := by
  rw [← inner_conj_symm, horth, map_zero]

theorem covMatrix_split :
    (covMatrix (pairs dx dy dz) Φ).submatrix splitZ splitZ =
      fromBlocks (covMatrix (famXY dx dy dz) Φ) 0 0 (covMatrix (famZ dx dy dz) Φ) := by
  ext (⟨s, i⟩ | s) (⟨t, j⟩ | t)
  · rfl
  · have h := horth s t i
    simp only [fluct] at h
    simp [covMatrix, covarianceG, splitZ, famZ, h]
  · have h := horth' horth t s j
    simp only [fluct] at h
    simp [covMatrix, covarianceG, splitZ, famXY, h]
  · rfl

theorem imMatrix_split :
    (imMatrix (pairs dx dy dz) Φ).submatrix splitZ splitZ =
      fromBlocks (imMatrix (famXY dx dy dz) Φ) 0 0 (imMatrix (famZ dx dy dz) Φ) := by
  ext (⟨s, i⟩ | s) (⟨t, j⟩ | t)
  · rfl
  · have h := horth s t i
    simp only [fluct] at h
    simp [imMatrix, splitZ, famZ, h]
  · have h := horth' horth t s j
    simp only [fluct] at h
    simp [imMatrix, splitZ, famXY, h]
  · rfl

omit horth in
/-- On `z`, `det Σ_z − |det Ω_z|` is the defect of the axis. -/
theorem det_z_sub (Φ : H3D dx dy dz) :
    (covMatrix (famZ dx dy dz) Φ).det - |(imMatrix (famZ dx dy dz) Φ).det| =
      gramDefectC (fluct Φ (0, 2)) (fluct Φ (1, 2)) := by
  set u := fluct Φ (0, 2)
  set v := fluct Φ (1, 2)
  have hvu : inner ℂ v u = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm v u).symm
  have huu : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hvv : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (inner ℂ u u).im = 0 := by simp [← Complex.ofReal_pow]
  have him' : (inner ℂ v v).im = 0 := by simp [← Complex.ofReal_pow]
  rw [det_fin_two, det_fin_two]
  simp only [covMatrix, imMatrix, covarianceG, of_apply, famZ]
  change (inner ℂ u u).re * (inner ℂ v v).re - (inner ℂ u v).re * (inner ℂ v u).re -
    |(inner ℂ u u).im * (inner ℂ v v).im - (inner ℂ u v).im * (inner ℂ v u).im| = _
  rw [hvu, Complex.conj_re, Complex.conj_im, huu, hvv, him, him', gramDefectC, varianceC,
    varianceC, Complex.sq_norm, Complex.normSq_apply,
    show (0 : ℝ) * 0 - (inner ℂ u v).im * -(inner ℂ u v).im =
      (inner ℂ u v).im * (inner ℂ u v).im by ring, abs_of_nonneg (mul_self_nonneg _)]
  ring

/-- **An orthogonal axis keeps det|NRS³ strict in the band.** -/
theorem robertson_det_strict_of_orthogonal (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    (hΦ : ‖Φ‖ = 1) (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy)
    (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    |(imMatrix (pairs dx dy dz) Φ).det| < (covMatrix (pairs dx dy dz) Φ).det := by
  have hS : (covMatrix (pairs dx dy dz) Φ).det =
      (covMatrix (famXY dx dy dz) Φ).det * (covMatrix (famZ dx dy dz) Φ).det := by
    rw [← det_submatrix_equiv_self splitZ, covMatrix_split horth, det_fromBlocks_zero₂₁]
  have hW : |(imMatrix (pairs dx dy dz) Φ).det| =
      |(imMatrix (famXY dx dy dz) Φ).det| * |(imMatrix (famZ dx dy dz) Φ).det| := by
    rw [← det_submatrix_equiv_self splitZ, imMatrix_split horth, det_fromBlocks_zero₂₁, abs_mul]
  -- the tensions are not zero in the band, so `det Ω ≠ 0`
  have hv0 (d : ℕ) (hd : 2 ≤ d) {v : ℝ} (hv : |v| ∈ Ϙ d) : v ≠ 0 := by
    rintro rfl
    obtain ⟨ψ, -, -, hs⟩ := (threshold_isGreatest (d := d) (by omega)).1
    have h0 : 0 ≤ threshold d := hs ▸ abs_nonneg _
    have := hv.1
    rw [abs_zero] at this
    linarith
  have ht (i : Fin 3) :
      tensionG (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ = -2 * omega Φ i :=
    tensionG_eq (pairs_isSymmetric dx dy dz _) (pairs_isSymmetric dx dy dz _)
  have hom0 : omega Φ 0 ≠ 0 := fun h0 => hv0 dx hx hbx (by
    show ((dx : ℝ) - 1) / 2 * tensionG (pairs dx dy dz (0, 0)) (pairs dx dy dz (1, 0)) Φ = 0
    rw [ht 0, h0, mul_zero, mul_zero])
  have hom1 : omega Φ 1 ≠ 0 := fun h0 => hv0 dy hy hby (by
    show ((dy : ℝ) - 1) / 2 * tensionG (pairs dx dy dz (0, 1)) (pairs dx dy dz (1, 1)) Φ = 0
    rw [ht 1, h0, mul_zero, mul_zero])
  have hom2 : omega Φ 2 ≠ 0 := fun h0 => hv0 dz hz hbz (by
    show ((dz : ℝ) - 1) / 2 * tensionG (pairs dx dy dz (0, 2)) (pairs dx dy dz (1, 2)) Φ = 0
    rw [ht 2, h0, mul_zero, mul_zero])
  have hWne : |(imMatrix (pairs dx dy dz) Φ).det| ≠ 0 := by
    rw [abs_det_imMatrix_pairs]
    exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hom0 hom1) hom2)
  have hxy0 : 0 < |(imMatrix (famXY dx dy dz) Φ).det| := by
    rcases (abs_nonneg (imMatrix (famXY dx dy dz) Φ).det).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hW, ← h, zero_mul]) hWne
  -- Robertson 1934 on `(x, y)` and the defect of `z`
  have hxy := robertson_det (famXY dx dy dz) Φ
  have hzd := gramDefect_pos_of_band hz (eZ dx dy dz) hΦ hbz
  have hz' : |(imMatrix (famZ dx dy dz) Φ).det| < (covMatrix (famZ dx dy dz) Φ).det := by
    have := det_z_sub (dx := dx) (dy := dy) Φ
    have hpos : 0 < gramDefectC (fluct Φ (0, 2)) (fluct Φ (1, 2)) := hzd
    linarith
  rw [hS, hW]
  calc |(imMatrix (famXY dx dy dz) Φ).det| * |(imMatrix (famZ dx dy dz) Φ).det|
      < |(imMatrix (famXY dx dy dz) Φ).det| * (covMatrix (famZ dx dy dz) Φ).det :=
        mul_lt_mul_of_pos_left hz' hxy0
    _ ≤ (covMatrix (famXY dx dy dz) Φ).det * (covMatrix (famZ dx dy dz) Φ).det :=
        mul_le_mul_of_nonneg_right hxy ((abs_nonneg _).trans hz'.le)

omit horth

/-! ## The third axis split off -/

theorem prodAlong_sub_right {ι α β : Type*} (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α)
    (φ φ' : EuclideanSpace ℂ β) : prodAlong e ψ (φ - φ') = prodAlong e ψ φ - prodAlong e ψ φ' := by
  ext p
  simp [prodAlong_apply, mul_sub]

theorem prodAlong_smul_right {ι α β : Type*} (e : ι ≃ α × β) (c : ℂ) (ψ : EuclideanSpace ℂ α)
    (φ : EuclideanSpace ℂ β) : prodAlong e ψ (c • φ) = c • prodAlong e ψ φ := by
  ext p
  simp only [prodAlong_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- An operator of `x` acts on the `(x, y)` factor of `w ⊗ χ`. -/
theorem liftX_prodZ (A : Matrix (Fin dx) (Fin dx) ℂ) (w : Hd dz)
    (χ : EuclideanSpace ℂ (Fin dx × Fin dy)) :
    Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A) (prodAlong (eZ dx dy dz) w χ) =
      prodAlong (eZ dx dy dz) w (WithLp.toLp 2 fun q => ∑ i', A q.1 i' * χ (i', q.2)) := by
  ext ⟨i, j, k⟩
  have h := liftAlong_apply_col (eX dx dy dz) A (prodAlong (eZ dx dy dz) w χ) i (j, k)
  rw [show (i, j, k) = (eX dx dy dz).symm (i, (j, k)) from rfl, h]
  simp only [Matrix.mulVec, dotProduct, AxisDefectEntangled.col, prodAlong_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp [eX, eZ]
  ring

/-- An operator of `y` acts on the `(x, y)` factor of `w ⊗ χ`. -/
theorem liftY_prodZ (A : Matrix (Fin dy) (Fin dy) ℂ) (w : Hd dz)
    (χ : EuclideanSpace ℂ (Fin dx × Fin dy)) :
    Matrix.toEuclideanLin (liftAlong (eY dx dy dz) A) (prodAlong (eZ dx dy dz) w χ) =
      prodAlong (eZ dx dy dz) w (WithLp.toLp 2 fun q => ∑ j', A q.2 j' * χ (q.1, j')) := by
  ext ⟨i, j, k⟩
  have h := liftAlong_apply_col (eY dx dy dz) A (prodAlong (eZ dx dy dz) w χ) j (i, k)
  rw [show (i, j, k) = (eY dx dy dz).symm (j, (i, k)) from rfl, h]
  simp only [Matrix.mulVec, dotProduct, AxisDefectEntangled.col, prodAlong_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp [eY, eZ]
  ring

/-- **The third axis split off.** If `Φ = w ⊗ χ` with `w` on `z` and `χ` on `(x, y)` (however
entangled), and the three speeds lie in the band, det|NRS³ is strict. -/
theorem robertson_det_strict_of_split (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {w : Hd dz}
    {χ : EuclideanSpace ℂ (Fin dx × Fin dy)} (hw : ‖w‖ = 1) (hχ : ‖χ‖ = 1)
    (hbx : |velocityX (prodAlong (eZ dx dy dz) w χ)| ∈ Ϙ dx)
    (hby : |velocityY (prodAlong (eZ dx dy dz) w χ)| ∈ Ϙ dy)
    (hbz : |velocityZ (prodAlong (eZ dx dy dz) w χ)| ∈ Ϙ dz) :
    |(imMatrix (pairs dx dy dz) (prodAlong (eZ dx dy dz) w χ)).det| <
      (covMatrix (pairs dx dy dz) (prodAlong (eZ dx dy dz) w χ)).det := by
  set Φ := prodAlong (eZ dx dy dz) w χ
  have hz' (t : Fin 2) : fluct Φ (t, 2) =
      prodAlong (eZ dx dy dz) (centeredG (Matrix.toEuclideanLin (![Td dz, Pd dz] t)) w) χ :=
    centeredG_lift (eZ dx dy dz) hχ _ _
  have hwB (t : Fin 2) :
      inner ℂ w (centeredG (Matrix.toEuclideanLin (![Td dz, Pd dz] t)) w) = 0 := by
    have hs := RobertsonDeterminantProduct.pair_isSymmetric dz t
    rw [RobertsonDeterminantProduct.pair_eq] at hs
    exact inner_centeredG_self hs hw
  refine robertson_det_strict_of_orthogonal ?_ hx hy hz (norm_prodAlong_eq_one _ hw hχ) hbx hby
    hbz
  intro s t i
  rw [hz' t]
  fin_cases i
  · change inner ℂ (centeredG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz)
      (![Td dx, Pd dx] s))) Φ) _ = 0
    rw [centeredG, liftX_prodZ, ← prodAlong_smul_right, ← prodAlong_sub_right, inner_prodAlong,
      hwB, zero_mul]
  · change inner ℂ (centeredG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz)
      (![Td dy, Pd dy] s))) Φ) _ = 0
    rw [centeredG, liftY_prodZ, ← prodAlong_smul_right, ← prodAlong_sub_right, inner_prodAlong,
      hwB, zero_mul]

end SplitAxis

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50e_Columns

/-!
# D50f — The band of the proper time, for every state of the cube

`D23d` proves for `H_d` that the surplus is within the tension deficit of `defectGram d`:
`gapK d · (surplus ψ − defectGram d)² ≤ 2048 (2/(d−1) − ⟨K_d⟩_ψ)`. Here the same bound, with the
same constants, for every unit state `Φ` of `ℂ^d ⊗ ℂ^β` (an axis of the cube and the rest), with
`τ²` the proper time of the axis (`D50c`).

The proof is that of `D23d`, column by column: the spectral gap of `K_d` (`D23c`) acts on each
column, the columns add, and the component along `maxCurrentState ⊗ u` is a unit state to which the
Lipschitz bound of the Gram defect (`D50d`) applies.

## Main results

- `ProperTimeBand.deficit_le` : `gapK d · Σ_r ‖φ_r⊥‖² ≤ 2/(d−1) − ⟨K⟩_Φ`.
- `ProperTimeBand.properTimeAxis_band` : `gapK d · (τ² − defectGram d)² ≤ 2048 (2/(d−1) − ⟨K⟩_Φ)`.
- `ProperTimeBand.properTime_cube_band` : the same on `x`, `y` and `z` of the open cube.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open TransportPosition NearMaxTension PathGraph3DNRS AxisDefectEntangled BandWidth
  SpectralExtremal Columns ProperTimeAxis ProperTime GramLipschitz NRSInequality
  EigenvectorSaturation CauchyGram GramStep

namespace ProperTimeBand

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] {d : ℕ}

/-- The amplitude of the maximal current state in column `r`. -/
def amp (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) : ℂ :=
  inner ℂ (maxCurrentState d) (colE e Φ r)

theorem col_decomp (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) :
    colE e Φ r = amp e Φ r • maxCurrentState d + orthComponent d (colE e Φ r) := by
  simp [orthComponent, amp]

theorem sum_decomp (hd : 2 ≤ d) (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    ‖Φ‖ ^ 2 = ∑ r, ‖amp e Φ r‖ ^ 2 + ∑ r, ‖orthComponent d (colE e Φ r)‖ ^ 2 := by
  rw [norm_sq_eq_sum_col e, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => norm_sq_decomp hd (colE e Φ r)

/-- **The tension deficit controls the part off `maxCurrentState`**, for every unit state. -/
theorem deficit_le (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι} (hΦ : ‖Φ‖ = 1) :
    gapK d * ∑ r, ‖orthComponent d (colE e Φ r)‖ ^ 2 ≤
      2 / ((d : ℝ) - 1) - tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
        (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ := by
  have hs := sum_decomp hd e Φ
  rw [hΦ, one_pow] at hs
  have ht : tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ ≤
      2 / ((d : ℝ) - 1) * ∑ r, ‖amp e Φ r‖ ^ 2 +
        secondEigenvalue d * ∑ r, ‖orthComponent d (colE e Φ r)‖ ^ 2 := by
    rw [tensionG_eq_sum_col, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [tension_decomp hd]
    have := tension_orthogonal_le hd _ (orthComponent_perp hd (colE e Φ r))
    show _ ≤ _
    simp only [amp]
    linarith
  have e : 2 / ((d : ℝ) - 1) = 2 / ((d : ℝ) - 1) * ∑ r, ‖amp e Φ r‖ ^ 2 +
      2 / ((d : ℝ) - 1) * ∑ r, ‖orthComponent d (colE e Φ r)‖ ^ 2 := by
    rw [← mul_add, ← hs, mul_one]
  unfold gapK
  linarith

/-- A vector of norm at most `1` has a unit vector within `1 − ‖χ‖²`. -/
theorem exists_unit_near [Nonempty β] (χ : EuclideanSpace ℂ β) (h : ‖χ‖ ≤ 1) :
    ∃ u : EuclideanSpace ℂ β, ‖u‖ = 1 ∧ ‖χ - u‖ ^ 2 ≤ 1 - ‖χ‖ ^ 2 := by
  by_cases h0 : χ = 0
  · obtain ⟨r⟩ := ‹Nonempty β›
    refine ⟨EuclideanSpace.single r 1, by simp, ?_⟩
    simp [h0]
  · have hs : 0 < ‖χ‖ := norm_pos_iff.mpr h0
    refine ⟨((‖χ‖⁻¹ : ℝ) : ℂ) • χ, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
        inv_mul_cancel₀ hs.ne']
    · have e : χ - ((‖χ‖⁻¹ : ℝ) : ℂ) • χ = (((1 - ‖χ‖⁻¹ : ℝ)) : ℂ) • χ := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have e2 : |1 - ‖χ‖⁻¹| * ‖χ‖ = 1 - ‖χ‖ := by
        rw [abs_of_nonpos (by rw [sub_nonpos]; exact one_le_inv_iff₀.mpr ⟨hs, h⟩)]
        field_simp
        ring
      rw [e2]
      nlinarith [norm_nonneg χ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq β] in
theorem colE_prodAlong (e : ι ≃ Fin d × β) (ψ : Hd d) (u : EuclideanSpace ℂ β) (r : β) :
    colE e (prodAlong e ψ u) r = u r • ψ := by
  ext i
  simp [colE_apply, prodAlong_apply, mul_comm]

/-- The squared distance from `Φ` to `maxCurrentState ⊗ u` splits into the part off
`maxCurrentState` and the distance of the amplitudes. -/
theorem dist_sq_eq (hd : 2 ≤ d) (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι)
    (u : EuclideanSpace ℂ β) :
    ‖Φ - prodAlong e (maxCurrentState d) u‖ ^ 2 =
      ∑ r, ‖orthComponent d (colE e Φ r)‖ ^ 2 +
        ‖(WithLp.toLp 2 (amp e Φ) : EuclideanSpace ℂ β) - u‖ ^ 2 := by
  rw [norm_sq_eq_sum_col e, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  set M := maxCurrentState d
  set o := orthComponent d (colE e Φ r)
  have e1 : colE e (Φ - prodAlong e M u) r = o + (amp e Φ r - u r) • M := by
    rw [colE_sub, colE_prodAlong, sub_smul]
    have h := col_decomp e Φ r
    calc colE e Φ r - u r • M = (amp e Φ r • M + o) - u r • M := by rw [← h]
      _ = _ := by abel
  have h0 : inner ℂ o ((amp e Φ r - u r) • M) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, orthComponent_perp hd, map_zero, mul_zero]
  rw [e1, @norm_add_sq ℂ, h0, norm_smul, norm_maxCurrentState hd]
  simp

/-- **The band of the proper time, for every state of the cube.** The bound of `D23d`, with the
same constants, for the axis `e` of every unit state `Φ`:
`gapK d · (τ² − defectGram d)² ≤ 2048 (2/(d−1) − ⟨K⟩_Φ)`. -/
theorem properTimeAxis_band (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (hΦ : ‖Φ‖ = 1) :
    gapK d * (properTimeAxis e Φ ^ 2 - defectGram d) ^ 2 ≤
      2048 * (2 / ((d : ℝ) - 1) - tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
        (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ) := by
  have : Nonempty β := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : IsEmpty ι := ⟨fun p => hne.false (e p).2⟩
    have h0 : Φ = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero] at hΦ
    exact zero_ne_one hΦ
  set M := maxCurrentState d
  set O := ∑ r, ‖orthComponent d (colE e Φ r)‖ ^ 2
  set A := ∑ r, ‖amp e Φ r‖ ^ 2
  have hs := sum_decomp hd e Φ
  rw [hΦ, one_pow] at hs
  set χ : EuclideanSpace ℂ β := WithLp.toLp 2 (amp e Φ)
  have hχ : ‖χ‖ ^ 2 = A := by
    rw [EuclideanSpace.norm_sq_eq]
  have hO : 0 ≤ O := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hχ1 : ‖χ‖ ≤ 1 := by
    have : ‖χ‖ ^ 2 ≤ 1 := by rw [hχ]; linarith
    nlinarith [norm_nonneg χ]
  obtain ⟨u, hu, hdist⟩ := exists_unit_near χ hχ1
  have hΦ' : ‖prodAlong e M u‖ = 1 := norm_prodAlong_eq_one e (norm_maxCurrentState hd) hu
  have hA : ∀ x, ‖Matrix.toEuclideanLin (liftAlong e (Td d)) x‖ ≤ ‖x‖ :=
    norm_lift_le e (fun x => norm_TdOp_le hd x)
  have hB : ∀ x, ‖Matrix.toEuclideanLin (liftAlong e (Pd d)) x‖ ≤ ‖x‖ :=
    norm_lift_le e (fun x => norm_PdOp_le hd x)
  have hL := gram_lipschitz hA hB hΦ hΦ'
  have hG : gramDefectC (centeredG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e M u))
      (centeredG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e M u)) =
        defectGram d := by
    rw [← properTimeAxis_sq, properTimeAxis_prodAlong e hu, properTime_sq,
      surplus_maxCurrentState hd]
  rw [hG, ← properTimeAxis_sq] at hL
  have hD := dist_sq_eq hd e Φ u
  have hN : ‖Φ - prodAlong e M u‖ ^ 2 ≤ 2 * O := by
    rw [hD]; nlinarith
  have h1 : (properTimeAxis e Φ ^ 2 - defectGram d) ^ 2 ≤ 2048 * O := by
    have := sq_le_sq' (neg_le_of_abs_le hL) (le_of_abs_le hL)
    nlinarith [norm_nonneg (Φ - prodAlong e M u)]
  have hg := gapK_pos hd
  have hdef := deficit_le hd e hΦ
  nlinarith

variable {dx dy dz : ℕ}

/-- **The same bound on the three axes of the open cube**, for every unit state `Φ`. -/
theorem properTime_cube_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) :
    gapK dx * (properTimeAxis (eX dx dy dz) Φ ^ 2 - defectGram dx) ^ 2 ≤
        2048 * (2 / ((dx : ℝ) - 1) - tensionG (TX dx dy dz) (PX dx dy dz) Φ) ∧
      gapK dy * (properTimeAxis (eY dx dy dz) Φ ^ 2 - defectGram dy) ^ 2 ≤
        2048 * (2 / ((dy : ℝ) - 1) - tensionG (TY dx dy dz) (PY dx dy dz) Φ) ∧
      gapK dz * (properTimeAxis (eZ dx dy dz) Φ ^ 2 - defectGram dz) ^ 2 ≤
        2048 * (2 / ((dz : ℝ) - 1) - tensionG (TZ dx dy dz) (PZ dx dy dz) Φ) :=
  ⟨properTimeAxis_band hx _ hΦ, properTimeAxis_band hy _ hΦ, properTimeAxis_band hz _ hΦ⟩

end ProperTimeBand

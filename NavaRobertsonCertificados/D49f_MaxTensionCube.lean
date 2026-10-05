/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49e_AxisDefectEntangled
public import NavaRobertsonIndependent.Mathematics.D42_DirectionOctants

/-!
# D49f — Maximal tension on an axis leaves no room for entanglement

On `H_d` the tension `⟨K_d⟩` reaches its top `±2/(d−1)` only at the maximal current state and its
reflection
(`D21`, `D42`). Here the state `Φ` lives on a product `ℂ^d ⊗ ℂ^β` and may be entangled. The
tension of the axis is the sum of the tensions of the columns of `Φ`, each bounded by
`2/(d−1)` times its weight; at the top every column is at the top, so every column is a multiple
of the maximal current state (or of its reflection). On the cube, with maximal tension on `x`, `y`
and `z`, `Φ` is a
phase times the product of the maximal current states (each factor in its direction): no
entanglement is possible.

## Main results

- `MaxTensionCube.tensionG_eq_sum_col` : the tension of an axis is the sum over the columns.
- `MaxTensionCube.col_eq_smul_psiDir` : at maximal tension every column is a multiple of
  the maximal current state in its direction.
- `MaxTensionCube.eq_smul_octant` : maximal tension on `x`, `y`, `z` makes `Φ` a phase times the
  octant state the product of the maximal current states.
- `MaxTensionCube.det_covMatrix_maxTension` : then
  `det Σ = C_Nava(dx)² C_Nava(dy)² C_Nava(dz)² · (t_x t_y t_z / 8)²`, for every state.
- `MaxTensionCube.robertson_det_maxTension_strict` : strict on every box with `4` or more positions
  on each axis.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality NearMaxTension GroupVelocity PathGraph3DNRS GramStep
open SpectralExtremal Direction AxisDefectEntangled CubeSpectrum Gnomon
open RobertsonDeterminant RobertsonDeterminant3D RobertsonDeterminantProduct

namespace MaxTensionCube

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] {d : ℕ}

/-! ## 1. Columns as states of `H_d` -/

/-- The column `r` of `Φ` as a vector of `H_d`. -/
def colV (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) : Hd d :=
  WithLp.toLp 2 (col e Φ r)

omit [DecidableEq ι] [DecidableEq β] in
theorem inner_eq_sum_col (e : ι ≃ Fin d × β) (Φ Ψ : EuclideanSpace ℂ ι) :
    inner ℂ Φ Ψ = ∑ r, inner ℂ (colV e Φ r) (colV e Ψ r) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, colV, col]
  rw [Fintype.sum_equiv e _ (fun x => Ψ (e.symm x) * (starRingEnd ℂ) (Φ (e.symm x)))
    (fun q => by simp), Fintype.sum_prod_type, Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq β] in
theorem norm_sq_eq_sum_col (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    ‖Φ‖ ^ 2 = ∑ r, ‖colV e Φ r‖ ^ 2 := by
  have h := inner_eq_sum_col e Φ Φ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem colV_lift (e : ι ≃ Fin d × β) (A : Matrix (Fin d) (Fin d) ℂ) (Φ : EuclideanSpace ℂ ι)
    (r : β) : colV e (Matrix.toEuclideanLin (liftAlong e A) Φ) r =
      Matrix.toEuclideanLin A (colV e Φ r) := by
  ext i
  simp only [colV, col]
  rw [liftAlong_apply_col]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- The tension observable acts column by column. -/
theorem colV_tension (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) :
    colV e (observableTension (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ) r = KdOp d (colV e Φ r) := by
  have hsub (Ψ Ψ' : EuclideanSpace ℂ ι) : colV e (Ψ - Ψ') r = colV e Ψ r - colV e Ψ' r := by
    ext i; simp [colV, col]
  have hsmul (c : ℂ) (Ψ : EuclideanSpace ℂ ι) : colV e (c • Ψ) r = c • colV e Ψ r := by
    ext i; simp [colV, col]
  simp only [observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, hsmul, hsub, colV_lift, KdOp, TdOp, PdOp]

/-- **The tension of an axis is the sum of the tensions of the columns.** -/
theorem tensionG_eq_sum_col (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ = ∑ r, tension d (colV e Φ r) := by
  rw [tensionG, inner_eq_sum_col e, Complex.re_sum]
  simp only [colV_tension, tension]

/-! ## 2. One column against the top -/

theorem tension_smul (c : ℂ) (u : Hd d) : tension d (c • u) = ‖c‖ ^ 2 * tension d u := by
  simp only [tension, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [mul_comm c, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- `|⟨u, K_d u⟩| ≤ (2/(d−1)) ‖u‖²` for every vector. -/
theorem abs_tension_le_sq (hd : 2 ≤ d) (u : Hd d) :
    |tension d u| ≤ 2 / ((d : ℝ) - 1) * ‖u‖ ^ 2 := by
  by_cases hu : u = 0
  · subst hu
    simp [tension]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have h1 : ‖(‖u‖⁻¹ : ℂ) • u‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn.ne']
  have h := abs_tension_le hd _ h1
  rw [tension_smul, norm_inv, Complex.norm_real, norm_norm, abs_mul, abs_of_pos (by positivity),
    inv_pow] at h
  rwa [inv_mul_le_iff₀ (by positivity), mul_comm] at h

/-- A column at the top of the tension in direction `b` is a multiple of the maximal current state
in direction
`b`. -/
theorem col_eq_smul_psiDir (hd : 2 ≤ d) (b : Bool) (u : Hd d)
    (h : tension d u = sgn b * (2 / ((d : ℝ) - 1)) * ‖u‖ ^ 2) : ∃ c : ℂ, u = c • psiDir d b := by
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu]⟩
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set ũ := (‖u‖⁻¹ : ℂ) • u
  have h1 : ‖ũ‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn.ne']
  have ht : tension d ũ = sgn b * (2 / ((d : ℝ) - 1)) := by
    rw [tension_smul, h, norm_inv, Complex.norm_real, norm_norm]
    field_simp
  have hu' : u = (‖u‖ : ℂ) • ũ := by
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  cases b
  · obtain ⟨c, -, hc⟩ := maxTension_state_eq_phase hd ũ h1
      (by simp only [sgn, Bool.cond_false, one_mul] at ht; exact ht)
    exact ⟨(‖u‖ : ℂ) * c, hu'.trans (by rw [hc, smul_smul]; rfl)⟩
  · have hr : tension d (reflect d ũ) = 2 / ((d : ℝ) - 1) := by
      rw [tension_reflect, ht]; simp [sgn]
    obtain ⟨c, -, hc⟩ := maxTension_state_eq_phase hd (reflect d ũ)
      (by rw [LinearIsometryEquiv.norm_map, h1]) hr
    have hrr : ũ = c • reflect d (maxCurrentState d) := by
      have := congrArg (reflect d).symm hc
      rw [LinearIsometryEquiv.symm_apply_apply, map_smul] at this
      rw [this]
      congr 1
      ext i
      simp [reflect]
    exact ⟨(‖u‖ : ℂ) * c, hu'.trans (by rw [hrr, smul_smul]; rfl)⟩

/-- **One axis at maximal tension.** If the tension of the axis is `±2/(d−1)`, every column of
`Φ` is a multiple of the maximal current state in that direction, whether or not `Φ` is entangled
with the rest. -/
theorem cols_of_maxTension (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (hΦ : ‖Φ‖ = 1) (b : Bool)
    (ht : tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ = sgn b * (2 / ((d : ℝ) - 1))) :
    ∀ r, ∃ c : ℂ, colV e Φ r = c • psiDir d b := by
  set k := 2 / ((d : ℝ) - 1)
  have hs2 : sgn b * sgn b = 1 := by cases b <;> simp [sgn]
  have hg (r : β) : 0 ≤ k * ‖colV e Φ r‖ ^ 2 - sgn b * tension d (colV e Φ r) := by
    have h1 := abs_tension_le_sq hd (colV e Φ r)
    have h2 : sgn b * tension d (colV e Φ r) ≤ |tension d (colV e Φ r)| := by
      cases b
      · simpa [sgn] using le_abs_self _
      · simpa [sgn] using neg_le_abs _
    linarith
  have hsum : ∑ r, (k * ‖colV e Φ r‖ ^ 2 - sgn b * tension d (colV e Φ r)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← norm_sq_eq_sum_col, hΦ,
      ← tensionG_eq_sum_col, ht, one_pow, mul_one, ← mul_assoc, hs2, one_mul, sub_self]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hg r)).mp hsum
  intro r
  apply col_eq_smul_psiDir hd b
  linear_combination (-sgn b) * h0 r (Finset.mem_univ r) - tension d (colV e Φ r) * hs2

/-! ## 3. The three axes -/

theorem surplus_reflect (ψ : Hd d) : surplus d (reflect d ψ) = surplus d ψ := by
  have h1 : variance (TdOp d) (reflect d ψ) = variance (TdOp d) ψ :=
    varianceG_comm (reflect d) TdOp_reflect ψ
  have h2 : variance (PdOp d) (reflect d ψ) = variance (PdOp d) ψ :=
    varianceG_anti (reflect d) PdOp_reflect ψ
  have h3 : covariance (TdOp d) (PdOp d) (reflect d ψ) = -covariance (TdOp d) (PdOp d) ψ :=
    covarianceG_anti (reflect d) TdOp_reflect PdOp_reflect ψ
  rw [surplus_eq, surplus_eq, h1, h2, h3, tension_reflect]
  ring

/-- One block at the maximal current state in either direction: `C_Nava(d)² · t²/4`. -/
theorem block_psiDir (hd : 2 ≤ d) (b : Bool) :
    surplus d (psiDir d b) + tension d (psiDir d b) ^ 2 / 4 =
      CoherenceConstant d ^ 2 * (tension d (psiDir d b) ^ 2 / 4) := by
  cases b
  · exact block_maxCurrentState hd
  · simp only [psiDir, Bool.cond_true, surplus_reflect, tension_reflect, neg_sq]
    exact block_maxCurrentState hd

/-- `|v| = 1` on an axis: the tension is `±2/(d−1)`. -/
theorem exists_sgn_of_abs_velocity {t : ℝ} (hd : 2 ≤ d) (h : |((d : ℝ) - 1) / 2 * t| = 1) :
    ∃ b : Bool, t = sgn b * (2 / ((d : ℝ) - 1)) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rcases (abs_eq zero_le_one).mp h with h | h
  · exact ⟨false, by simp only [sgn, Bool.cond_false, one_mul]; field_simp; linarith⟩
  · exact ⟨true, by simp only [sgn, Bool.cond_true]; field_simp; linarith⟩

variable {dx dy dz : ℕ}

/-- **No entanglement at maximal tension.** Maximal tension on `x`, `y` and `z` makes `Φ` a phase
times the product of the maximal current states (each factor in its direction). -/
theorem eq_smul_octant (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (bx b_y bz : Bool)
    (htx : tensionG (TX dx dy dz) (PX dx dy dz) Φ = sgn bx * (2 / ((dx : ℝ) - 1)))
    (hty : tensionG (TY dx dy dz) (PY dx dy dz) Φ = sgn b_y * (2 / ((dy : ℝ) - 1)))
    (htz : tensionG (TZ dx dy dz) (PZ dx dy dz) Φ = sgn bz * (2 / ((dz : ℝ) - 1))) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ Φ = c • octant dx dy dz bx b_y bz := by
  choose α hα using cols_of_maxTension hx (eX dx dy dz) hΦ bx htx
  choose β hβ using cols_of_maxTension hy (eY dx dy dz) hΦ b_y hty
  choose γ hγ using cols_of_maxTension hz (eZ dx dy dz) hΦ bz htz
  set u := psiDir dx bx
  set v := psiDir dy b_y
  set w := psiDir dz bz
  have hX (i j k) : Φ (i, j, k) = α (j, k) * u i := congrArg (fun f : Hd dx => f i) (hα (j, k))
  have hY (i j k) : Φ (i, j, k) = β (i, k) * v j := congrArg (fun f : Hd dy => f j) (hβ (i, k))
  have hZ (i j k) : Φ (i, j, k) = γ (i, j) * w k := congrArg (fun f : Hd dz => f k) (hγ (i, j))
  have hne {n : ℕ} (hn : 2 ≤ n) (b : Bool) : ∃ i, psiDir n b i ≠ 0 := by
    by_contra hc
    push Not at hc
    have : psiDir n b = 0 := by ext i; simp [hc i]
    have h1 := norm_psiDir hn b
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨i₀, hi₀⟩ := hne hx bx
  obtain ⟨j₀, hj₀⟩ := hne hy b_y
  have hu0 : u i₀ ≠ 0 := hi₀
  have hv0 : v j₀ ≠ 0 := hj₀
  have hoct : ‖octant dx dy dz bx b_y bz‖ = 1 := by
    rw [octant, prod3_eq_eX]
    exact norm_prodAlong_eq_one _ (norm_psiDir hx bx) (norm_rest_dir hy hz b_y bz)
  have hΦc : Φ = (γ (i₀, j₀) / (u i₀ * v j₀)) • octant dx dy dz bx b_y bz := by
    ext ⟨i, j, k⟩
    have h1 : α (j, k) * u i₀ = β (i₀, k) * v j := (hX i₀ j k).symm.trans (hY i₀ j k)
    have h2 : β (i₀, k) * v j₀ = γ (i₀, j₀) * w k := (hY i₀ j₀ k).symm.trans (hZ i₀ j₀ k)
    rw [hX i j k]
    simp only [octant, prod3, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (u i * v j₀) * h1 + (u i * v j) * h2
  refine ⟨_, ?_, hΦc⟩
  have := congrArg norm hΦc
  rwa [norm_smul, hoct, mul_one, hΦ, eq_comm] at this

/-- **det|NRS³ at maximal tension, for every state.** -/
theorem det_covMatrix_maxTension (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (hvx : |velocityX Φ| = 1) (hvy : |velocityY Φ| = 1)
    (hvz : |velocityZ Φ| = 1) :
    (covMatrix (pairs dx dy dz) Φ).det =
      (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 *
        ((tensionG (TX dx dy dz) (PX dx dy dz) Φ * tensionG (TY dx dy dz) (PY dx dy dz) Φ *
          tensionG (TZ dx dy dz) (PZ dx dy dz) Φ) / 8) ^ 2 := by
  obtain ⟨bx, hbx⟩ := exists_sgn_of_abs_velocity hx hvx
  obtain ⟨b_y, hby⟩ := exists_sgn_of_abs_velocity hy hvy
  obtain ⟨bz, hbz⟩ := exists_sgn_of_abs_velocity hz hvz
  obtain ⟨c, hc, hΦc⟩ := eq_smul_octant hx hy hz hΦ bx b_y bz hbx hby hbz
  have hprod : Φ = prod3 (c • psiDir dx bx) (psiDir dy b_y) (psiDir dz bz) := by
    rw [hΦc]
    ext p
    simp [octant, prod3, mul_assoc]
  have hu : ‖c • psiDir dx bx‖ = 1 := by rw [norm_smul, hc, norm_psiDir hx, one_mul]
  have hv := norm_psiDir hy b_y
  have hw := norm_psiDir hz bz
  obtain ⟨tx, ty, tz⟩ := tensions_prod3 hu hv hw
  rw [hprod, det_covMatrix_prod3 hu hv hw, tx, ty, tz, surplus_phase _ _ hc, tension_smul, hc,
    one_pow, one_mul, block_psiDir hx, block_psiDir hy, block_psiDir hz]
  ring

/-- **Strict at maximal tension, for every state**, on every box with `4` or more positions on each
of `x`, `y`, `z`. -/
theorem robertson_det_maxTension_strict (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz)
    {Φ : H3D dx dy dz} (hΦ : ‖Φ‖ = 1) (hvx : |velocityX Φ| = 1) (hvy : |velocityY Φ| = 1)
    (hvz : |velocityZ Φ| = 1) :
    ((tensionG (TX dx dy dz) (PX dx dy dz) Φ * tensionG (TY dx dy dz) (PY dx dy dz) Φ *
        tensionG (TZ dx dy dz) (PZ dx dy dz) Φ) / 8) ^ 2 <
      (covMatrix (pairs dx dy dz) Φ).det := by
  rw [det_covMatrix_maxTension (by omega) (by omega) (by omega) hΦ hvx hvy hvz]
  have hC (n : ℕ) (hn : 4 ≤ n) : 1 < CoherenceConstant n := by
    rw [CoherenceConstant_eq_one_add_geometricGap]
    linarith [geometricGap_pos_of_four_le n hn]
  have ht (n : ℕ) (hn : 4 ≤ n) {t : ℝ} (h : |((n : ℝ) - 1) / 2 * t| = 1) : t ≠ 0 := by
    rintro rfl
    simp at h
  have hB : 0 < ((tensionG (TX dx dy dz) (PX dx dy dz) Φ * tensionG (TY dx dy dz) (PY dx dy dz) Φ *
      tensionG (TZ dx dy dz) (PZ dx dy dz) Φ) / 8) ^ 2 := by
    have := ht dx hx hvx
    have := ht dy hy hvy
    have := ht dz hz hvz
    positivity
  have h1 : 1 < (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 := by
    have := hC dx hx
    have := hC dy hy
    have := hC dz hz
    have : 1 < CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz := by
      have h := mul_lt_mul'' (mul_lt_mul'' (hC dx hx) (hC dy hy) zero_le_one zero_le_one)
        (hC dz hz) (by norm_num) zero_le_one
      simpa using h
    nlinarith
  nlinarith

end MaxTensionCube

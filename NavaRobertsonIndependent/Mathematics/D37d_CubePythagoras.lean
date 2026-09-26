/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle
public import NavaRobertsonIndependent.Mathematics.D37c_CubeSpectrum

/-!
# D37d — Pythagoras for uncertainty

At `Ψ* = ψ* ⊗ ψ* ⊗ ψ*` each axis carries its pair of fluctuation vectors, open at
`θ_NRS(d_axis)` (`D37b`). Fluctuation vectors of different axes are orthogonal.

## Main results

- `CubePythagoras.orthogonal_axes_xy` (and `_xz`, `_yz`) : different axes are orthogonal.
- `CubePythagoras.pythagoras_T`, `CubePythagoras.pythagoras_P` :
  `Var(T_x + T_y + T_z) = Var T_x + Var T_y + Var T_z`, and the same for `P`.
- `CubePythagoras.angle_total_cube` : on `d × d × d` the total pair meets at `θ_NRS(d)`; at
  `4 × 4 × 4`, `θ_NRS(4) ≈ 7.43°` (`angle_total_four`).
-/

@[expose] public noncomputable section

open Real TransportPosition NRSInequality SpectralExtremal
open PathGraph3DNRS CubeSpectrum NRSAngle

namespace CubePythagoras

/-! ## 1. Fluctuation vectors of a unit state -/

/-- For a symmetric operator and a unit vector, the fluctuation vector is orthogonal to the state.
-/
theorem inner_centeredG_self {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} (hA : A.IsSymmetric) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) : inner ℂ ψ (centeredG A ψ) = 0 := by
  have h1 : inner ℂ ψ ψ = 1 := inner_self_of_norm_one hψ
  have h2 : ((inner ℂ ψ (A ψ)).re : ℂ) = inner ℂ ψ (A ψ) := by
    rw [← hA ψ ψ]; exact hA.coe_re_inner_apply_self ψ
  rw [centeredG, inner_sub_right, inner_smul_right, h1, mul_one, meanG, h2, sub_self]

theorem inner_self_centeredG {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} (hA : A.IsSymmetric) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) : inner ℂ (centeredG A ψ) ψ = 0 := by
  rw [← inner_conj_symm, inner_centeredG_self hA hψ, map_zero]

/-! ## 2. Fluctuation vectors of the cube, factor by factor -/

section Cubo

variable {dx dy dz : ℕ}

theorem inner_prod3 (u u' : Hd dx) (v v' : Hd dy) (w w' : Hd dz) :
    inner ℂ (prod3 u v w) (prod3 u' v' w') = inner ℂ u u' * inner ℂ v v' * inner ℂ w w' := by
  rw [prod3_eq_eX, prod3_eq_eX, inner_prodAlong, inner_prodAlong]; ring

theorem centered_X (hy : 2 ≤ dy) (hz : 2 ≤ dz) (A : Matrix (Fin dx) (Fin dx) ℂ) :
    centeredG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A)) (PsiStar3D dx dy dz) =
      prod3 (centeredG (Matrix.toEuclideanLin A) (psiStar dx)) (psiStar dy) (psiStar dz) := by
  rw [PsiStar3D_eq_eX, centeredG_lift _ (norm_rest hy hz), ← prod3_eq_eX]

theorem centered_Y (hx : 2 ≤ dx) (hz : 2 ≤ dz) (A : Matrix (Fin dy) (Fin dy) ℂ) :
    centeredG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) A)) (PsiStar3D dx dy dz) =
      prod3 (psiStar dx) (centeredG (Matrix.toEuclideanLin A) (psiStar dy)) (psiStar dz) := by
  rw [PsiStar3D_eq_eY, centeredG_lift _ (norm_rest hx hz), ← prod3_eq_eY]

theorem centered_Z (hx : 2 ≤ dx) (hy : 2 ≤ dy) (A : Matrix (Fin dz) (Fin dz) ℂ) :
    centeredG (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) A)) (PsiStar3D dx dy dz) =
      prod3 (psiStar dx) (psiStar dy) (centeredG (Matrix.toEuclideanLin A) (psiStar dz)) := by
  rw [PsiStar3D_eq_eZ, centeredG_lift _ (norm_rest hx hy), ← prod3_eq_eZ]

/-! ## 3. Perpendicular axes -/

variable (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
include hx hy hz

/-- Fluctuation vectors of the `x` and `y` axes are orthogonal (for any symmetric `A`, `B`). -/
theorem orthogonal_axes_xy {A : Matrix (Fin dx) (Fin dx) ℂ} {B : Matrix (Fin dy) (Fin dy) ℂ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetric) :
    inner ℂ (centeredG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A)) (PsiStar3D dx dy dz))
      (centeredG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) B)) (PsiStar3D dx dy dz)) = 0 := by
  rw [centered_X hy hz, centered_Y hx hz, inner_prod3, inner_self_centeredG hA (norm_psiStar hx)]
  ring

theorem orthogonal_axes_xz {A : Matrix (Fin dx) (Fin dx) ℂ} {B : Matrix (Fin dz) (Fin dz) ℂ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetric) :
    inner ℂ (centeredG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A)) (PsiStar3D dx dy dz))
      (centeredG (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) B)) (PsiStar3D dx dy dz)) = 0 := by
  rw [centered_X hy hz, centered_Z hx hy, inner_prod3, inner_self_centeredG hA (norm_psiStar hx)]
  ring

theorem orthogonal_axes_yz {A : Matrix (Fin dy) (Fin dy) ℂ} {B : Matrix (Fin dz) (Fin dz) ℂ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetric) :
    inner ℂ (centeredG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) A)) (PsiStar3D dx dy dz))
      (centeredG (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) B)) (PsiStar3D dx dy dz)) = 0 := by
  rw [centered_Y hx hz, centered_Z hx hy, inner_prod3, inner_self_centeredG hA (norm_psiStar hy)]
  ring

/-! ## 4. Pythagoras -/

omit hx hy hz in
theorem meanG_add {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : meanG (L + M) Ψ = meanG L Ψ + meanG M Ψ := by
  simp [meanG]

omit hx hy hz in
theorem centeredG_add {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : centeredG (L + M) Ψ = centeredG L Ψ + centeredG M Ψ := by
  rw [centeredG, centeredG, centeredG, meanG_add, LinearMap.add_apply]
  push_cast; rw [add_smul]; abel

omit hx hy hz in
/-- Pythagoras for three mutually orthogonal vectors. -/
theorem norm_sq_add_three {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a b c : E)
    (hab : inner ℂ a b = 0) (hac : inner ℂ a c = 0) (hbc : inner ℂ b c = 0) :
    ‖a + b + c‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), inner_add_left, hac, hbc, hab]
  simp

/-- **Pythagoras for transport uncertainty.** `Var(T_x + T_y + T_z) = Var T_x + Var T_y + Var T_z`.
-/
theorem pythagoras_T :
    varianceG (TX dx dy dz + TY dx dy dz + TZ dx dy dz) (PsiStar3D dx dy dz) =
      varianceG (TX dx dy dz) (PsiStar3D dx dy dz) + varianceG (TY dx dy dz) (PsiStar3D dx dy dz) +
        varianceG (TZ dx dy dz) (PsiStar3D dx dy dz) := by
  simp only [varianceG, centeredG_add]
  exact norm_sq_add_three _ _ _ (orthogonal_axes_xy hx hy hz (TdOp_isSymmetric dx))
    (orthogonal_axes_xz hx hy hz (TdOp_isSymmetric dx))
    (orthogonal_axes_yz hx hy hz (TdOp_isSymmetric dy))

/-- **Pythagoras for position uncertainty.** `Var(P_x + P_y + P_z) = Var P_x + Var P_y + Var P_z`.
-/
theorem pythagoras_P :
    varianceG (PX dx dy dz + PY dx dy dz + PZ dx dy dz) (PsiStar3D dx dy dz) =
      varianceG (PX dx dy dz) (PsiStar3D dx dy dz) + varianceG (PY dx dy dz) (PsiStar3D dx dy dz) +
        varianceG (PZ dx dy dz) (PsiStar3D dx dy dz) := by
  simp only [varianceG, centeredG_add]
  exact norm_sq_add_three _ _ _ (orthogonal_axes_xy hx hy hz (PdOp_isSymmetric dx))
    (orthogonal_axes_xz hx hy hz (PdOp_isSymmetric dx))
    (orthogonal_axes_yz hx hy hz (PdOp_isSymmetric dy))

end Cubo

/-! ## 5. The star has the angle of its axes -/

section Igual

variable {d : ℕ} (hd : 2 ≤ d)
include hd

/-- On the cube `d × d × d`, the total pair `(T_x + T_y + T_z, P_x + P_y + P_z)` meets at exactly
the NRS angle of one axis. -/
theorem angle_total_cube :
    angleG (TX d d d + TY d d d + TZ d d d) (PX d d d + PY d d d + PZ d d d) (PsiStar3D d d d) =
      angleNRS d := by
  set x := centeredG (TdOp d) (psiStar d)
  set y := centeredG (PdOp d) (psiStar d)
  set n := psiStar d
  have hn : inner ℂ n n = 1 := inner_self_of_norm_one (norm_psiStar hd)
  have hxn : inner ℂ x n = 0 := inner_self_centeredG (TdOp_isSymmetric d) (norm_psiStar hd)
  have hnx : inner ℂ n x = 0 := inner_centeredG_self (TdOp_isSymmetric d) (norm_psiStar hd)
  have hyn : inner ℂ y n = 0 := inner_self_centeredG (PdOp_isSymmetric d) (norm_psiStar hd)
  have hny : inner ℂ n y = 0 := inner_centeredG_self (PdOp_isSymmetric d) (norm_psiStar hd)
  have eT : centeredG (TX d d d + TY d d d + TZ d d d) (PsiStar3D d d d) =
      prod3 x n n + prod3 n x n + prod3 n n x := by
    rw [centeredG_add, centeredG_add, TX, TY, TZ, centered_X hd hd, centered_Y hd hd,
      centered_Z hd hd]; rfl
  have eP : centeredG (PX d d d + PY d d d + PZ d d d) (PsiStar3D d d d) =
      prod3 y n n + prod3 n y n + prod3 n n y := by
    rw [centeredG_add, centeredG_add, PX, PY, PZ, centered_X hd hd, centered_Y hd hd,
      centered_Z hd hd]; rfl
  have hin : inner ℂ (prod3 x n n + prod3 n x n + prod3 n n x) (prod3 y n n + prod3 n y n + prod3 n
      n y) =
      3 * inner ℂ x y := by
    simp only [inner_add_left, inner_add_right, inner_prod3, hn, hxn, hny]; ring
  have hnT : ‖prod3 x n n + prod3 n x n + prod3 n n x‖ = Real.sqrt 3 * ‖x‖ := by
    have h := norm_sq_add_three (prod3 x n n) (prod3 n x n) (prod3 n n x)
      (by rw [inner_prod3, hxn, hnx]; ring) (by rw [inner_prod3, hxn, hnx]; ring)
      (by rw [inner_prod3, hxn, hnx]; ring)
    have e : ∀ u v w : Hd d, ‖prod3 u v w‖ ^ 2 = ((inner ℂ (prod3 u v w) (prod3 u v w)).re) := by
      intro u v w; exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    have h1 : ‖prod3 x n n‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [e, inner_prod3, hn, mul_one, mul_one]; exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    have h2 : ‖prod3 n x n‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [e, inner_prod3, hn, one_mul, mul_one]; exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    have h3 : ‖prod3 n n x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [e, inner_prod3, hn, one_mul, one_mul]; exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [h1, h2, h3] at h
    have : ‖prod3 x n n + prod3 n x n + prod3 n n x‖ ^ 2 = (Real.sqrt 3 * ‖x‖) ^ 2 := by
      rw [h, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  have hnP : ‖prod3 y n n + prod3 n y n + prod3 n n y‖ = Real.sqrt 3 * ‖y‖ := by
    have h := norm_sq_add_three (prod3 y n n) (prod3 n y n) (prod3 n n y)
      (by rw [inner_prod3, hyn, hny]; ring) (by rw [inner_prod3, hyn, hny]; ring)
      (by rw [inner_prod3, hyn, hny]; ring)
    have e : ∀ u v w : Hd d, ‖prod3 u v w‖ ^ 2 = ((inner ℂ (prod3 u v w) (prod3 u v w)).re) := by
      intro u v w; exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    have h1 : ‖prod3 y n n‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [e, inner_prod3, hn, mul_one, mul_one]; exact inner_self_eq_norm_sq (𝕜 := ℂ) y
    have h2 : ‖prod3 n y n‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [e, inner_prod3, hn, one_mul, mul_one]; exact inner_self_eq_norm_sq (𝕜 := ℂ) y
    have h3 : ‖prod3 n n y‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [e, inner_prod3, hn, one_mul, one_mul]; exact inner_self_eq_norm_sq (𝕜 := ℂ) y
    rw [h1, h2, h3] at h
    have : ‖prod3 y n n + prod3 n y n + prod3 n n y‖ ^ 2 = (Real.sqrt 3 * ‖y‖) ^ 2 := by
      rw [h, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  rw [angleG, eT, eP, hin, hnT, hnP, angleNRS, angleG]
  congr 1
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hden : Real.sqrt 3 * ‖x‖ * (Real.sqrt 3 * ‖y‖) = 3 * (‖x‖ * ‖y‖) := by
    calc Real.sqrt 3 * ‖x‖ * (Real.sqrt 3 * ‖y‖) = (Real.sqrt 3 * Real.sqrt 3) * (‖x‖ * ‖y‖) := by
          ring
      _ = 3 * (‖x‖ * ‖y‖) := by rw [h3]
  rw [norm_mul, show ‖(3 : ℂ)‖ = 3 by simp, hden, mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]

end Igual

/-- **At the first rupture** `4 × 4 × 4`, the star of the three axes opens exactly
`θ_NRS(4) = arccos (1/√((99 − 42√5)/5)) ≈ 7.43°`. -/
theorem angle_total_four :
    angleG (TX 4 4 4 + TY 4 4 4 + TZ 4 4 4) (PX 4 4 4 + PY 4 4 4 + PZ 4 4 4) (PsiStar3D 4 4 4) =
      arccos (1 / Real.sqrt ((99 - 42 * Real.sqrt 5) / 5)) := by
  rw [angle_total_cube (by norm_num), angleNRS_four]

end CubePythagoras

end

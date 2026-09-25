import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle
import NavaRobertsonIndependent.Mathematics.D37c_CubeSpectrum

/-!
# D37d — The three axes of the cube are perpendicular: Pythagoras for uncertainty

At the maximal-tension state `Ψ* = ψ* ⊗ ψ* ⊗ ψ*` of the cube (`D37`), each axis carries its pair
of fluctuation vectors `(T − ⟨T⟩)Ψ*`, `(P − ⟨P⟩)Ψ*`, open at the NRS angle `θ_NRS(d_axis)`
(`D37b`). This file shows how the three pairs sit together:

* **Perpendicular axes** (`ortogonal_ejes_xy`, `…_xz`, `…_yz`): every fluctuation vector of one
  axis is orthogonal to every fluctuation vector of another axis.
* **Pythagoras for uncertainty** (`pitagoras_T`, `pitagoras_P`):
  `Var(T_x + T_y + T_z) = Var T_x + Var T_y + Var T_z`, and the same for `P`.
* **The star has the angle of its axes** (`angulo_total_cubo`): on the cube `d × d × d`, the
  total pair `(T_x + T_y + T_z, P_x + P_y + P_z)` meets at exactly `θ_NRS(d)` — at the first
  rupture `4 × 4 × 4`, exactly `θ_NRS(4) ≈ 7.44°` (`angulo_total_cuatro`).
-/

noncomputable section

open Real TransportePosicion NavaRobertsonSchrodingerEDUI ConstructorEspectralTP
open PathGraph3DNRS EspectroCubo AnguloNRS

namespace PitagorasCubo

/-! ## 1. Fluctuation vectors of a unit state -/

/-- For a symmetric operator and a unit vector, the fluctuation vector is orthogonal to the state. -/
theorem inner_centradoG_self {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} (hA : A.IsSymmetric) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) : inner ℂ ψ (centradoG A ψ) = 0 := by
  have h1 : inner ℂ ψ ψ = 1 := inner_self_of_norm_one hψ
  have h2 : ((inner ℂ ψ (A ψ)).re : ℂ) = inner ℂ ψ (A ψ) := by
    rw [← hA ψ ψ]; exact hA.coe_re_inner_apply_self ψ
  rw [centradoG, inner_sub_right, inner_smul_right, h1, mul_one, mediaG, h2, sub_self]

theorem inner_self_centradoG {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} (hA : A.IsSymmetric) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) : inner ℂ (centradoG A ψ) ψ = 0 := by
  rw [← inner_conj_symm, inner_centradoG_self hA hψ, map_zero]

/-! ## 2. Fluctuation vectors of the cube, factor by factor -/

section Cubo

variable {dx dy dz : ℕ}

theorem inner_prod3 (u u' : Hd dx) (v v' : Hd dy) (w w' : Hd dz) :
    inner ℂ (prod3 u v w) (prod3 u' v' w') = inner ℂ u u' * inner ℂ v v' * inner ℂ w w' := by
  rw [prod3_eq_eX, prod3_eq_eX, inner_prodAlong, inner_prodAlong]; ring

theorem centrado_X (hy : 2 ≤ dy) (hz : 2 ≤ dz) (A : Matrix (Fin dx) (Fin dx) ℂ) :
    centradoG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A)) (PsiStar3D dx dy dz) =
      prod3 (centradoG (Matrix.toEuclideanLin A) (psiStar dx)) (psiStar dy) (psiStar dz) := by
  rw [PsiStar3D_eq_eX, centradoG_lift _ (norm_resto hy hz), ← prod3_eq_eX]

theorem centrado_Y (hx : 2 ≤ dx) (hz : 2 ≤ dz) (A : Matrix (Fin dy) (Fin dy) ℂ) :
    centradoG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) A)) (PsiStar3D dx dy dz) =
      prod3 (psiStar dx) (centradoG (Matrix.toEuclideanLin A) (psiStar dy)) (psiStar dz) := by
  rw [PsiStar3D_eq_eY, centradoG_lift _ (norm_resto hx hz), ← prod3_eq_eY]

theorem centrado_Z (hx : 2 ≤ dx) (hy : 2 ≤ dy) (A : Matrix (Fin dz) (Fin dz) ℂ) :
    centradoG (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) A)) (PsiStar3D dx dy dz) =
      prod3 (psiStar dx) (psiStar dy) (centradoG (Matrix.toEuclideanLin A) (psiStar dz)) := by
  rw [PsiStar3D_eq_eZ, centradoG_lift _ (norm_resto hx hy), ← prod3_eq_eZ]

/-! ## 3. Perpendicular axes -/

variable (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
include hx hy hz

/-- Fluctuation vectors of the `x` and `y` axes are orthogonal (for any symmetric `A`, `B`). -/
theorem ortogonal_ejes_xy {A : Matrix (Fin dx) (Fin dx) ℂ} {B : Matrix (Fin dy) (Fin dy) ℂ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetric) :
    inner ℂ (centradoG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A)) (PsiStar3D dx dy dz))
      (centradoG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) B)) (PsiStar3D dx dy dz)) = 0 := by
  rw [centrado_X hy hz, centrado_Y hx hz, inner_prod3, inner_self_centradoG hA (norma_psiStar hx)]
  ring

theorem ortogonal_ejes_xz {A : Matrix (Fin dx) (Fin dx) ℂ} {B : Matrix (Fin dz) (Fin dz) ℂ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetric) :
    inner ℂ (centradoG (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A)) (PsiStar3D dx dy dz))
      (centradoG (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) B)) (PsiStar3D dx dy dz)) = 0 := by
  rw [centrado_X hy hz, centrado_Z hx hy, inner_prod3, inner_self_centradoG hA (norma_psiStar hx)]
  ring

theorem ortogonal_ejes_yz {A : Matrix (Fin dy) (Fin dy) ℂ} {B : Matrix (Fin dz) (Fin dz) ℂ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetric) :
    inner ℂ (centradoG (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) A)) (PsiStar3D dx dy dz))
      (centradoG (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) B)) (PsiStar3D dx dy dz)) = 0 := by
  rw [centrado_Y hx hz, centrado_Z hx hy, inner_prod3, inner_self_centradoG hA (norma_psiStar hy)]
  ring

/-! ## 4. Pythagoras -/

omit hx hy hz in
theorem mediaG_add {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : mediaG (L + M) Ψ = mediaG L Ψ + mediaG M Ψ := by
  simp [mediaG]

omit hx hy hz in
theorem centradoG_add {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : centradoG (L + M) Ψ = centradoG L Ψ + centradoG M Ψ := by
  rw [centradoG, centradoG, centradoG, mediaG_add, LinearMap.add_apply]
  push_cast; rw [add_smul]; abel

omit hx hy hz in
/-- Pythagoras for three mutually orthogonal vectors. -/
theorem norm_sq_add_three {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a b c : E)
    (hab : inner ℂ a b = 0) (hac : inner ℂ a c = 0) (hbc : inner ℂ b c = 0) :
    ‖a + b + c‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), inner_add_left, hac, hbc, hab]
  simp

/-- **Pythagoras for transport uncertainty.** `Var(T_x + T_y + T_z) = Var T_x + Var T_y + Var T_z`. -/
theorem pitagoras_T :
    varianzaG (TX dx dy dz + TY dx dy dz + TZ dx dy dz) (PsiStar3D dx dy dz) =
      varianzaG (TX dx dy dz) (PsiStar3D dx dy dz) + varianzaG (TY dx dy dz) (PsiStar3D dx dy dz) +
        varianzaG (TZ dx dy dz) (PsiStar3D dx dy dz) := by
  simp only [varianzaG, centradoG_add]
  exact norm_sq_add_three _ _ _ (ortogonal_ejes_xy hx hy hz (TdOp_simetrico dx))
    (ortogonal_ejes_xz hx hy hz (TdOp_simetrico dx)) (ortogonal_ejes_yz hx hy hz (TdOp_simetrico dy))

/-- **Pythagoras for position uncertainty.** `Var(P_x + P_y + P_z) = Var P_x + Var P_y + Var P_z`. -/
theorem pitagoras_P :
    varianzaG (PX dx dy dz + PY dx dy dz + PZ dx dy dz) (PsiStar3D dx dy dz) =
      varianzaG (PX dx dy dz) (PsiStar3D dx dy dz) + varianzaG (PY dx dy dz) (PsiStar3D dx dy dz) +
        varianzaG (PZ dx dy dz) (PsiStar3D dx dy dz) := by
  simp only [varianzaG, centradoG_add]
  exact norm_sq_add_three _ _ _ (ortogonal_ejes_xy hx hy hz (PdOp_simetrico dx))
    (ortogonal_ejes_xz hx hy hz (PdOp_simetrico dx)) (ortogonal_ejes_yz hx hy hz (PdOp_simetrico dy))

end Cubo

/-! ## 5. The star has the angle of its axes -/

section Igual

variable {d : ℕ} (hd : 2 ≤ d)
include hd

/-- On the cube `d × d × d`, the total pair `(T_x + T_y + T_z, P_x + P_y + P_z)` meets at exactly
the NRS angle of one axis. -/
theorem angulo_total_cubo :
    anguloG (TX d d d + TY d d d + TZ d d d) (PX d d d + PY d d d + PZ d d d) (PsiStar3D d d d) =
      anguloNRS d := by
  set x := centradoG (TdOp d) (psiStar d)
  set y := centradoG (PdOp d) (psiStar d)
  set n := psiStar d
  have hn : inner ℂ n n = 1 := inner_self_of_norm_one (norma_psiStar hd)
  have hxn : inner ℂ x n = 0 := inner_self_centradoG (TdOp_simetrico d) (norma_psiStar hd)
  have hnx : inner ℂ n x = 0 := inner_centradoG_self (TdOp_simetrico d) (norma_psiStar hd)
  have hyn : inner ℂ y n = 0 := inner_self_centradoG (PdOp_simetrico d) (norma_psiStar hd)
  have hny : inner ℂ n y = 0 := inner_centradoG_self (PdOp_simetrico d) (norma_psiStar hd)
  have eT : centradoG (TX d d d + TY d d d + TZ d d d) (PsiStar3D d d d) =
      prod3 x n n + prod3 n x n + prod3 n n x := by
    rw [centradoG_add, centradoG_add, TX, TY, TZ, centrado_X hd hd, centrado_Y hd hd,
      centrado_Z hd hd]; rfl
  have eP : centradoG (PX d d d + PY d d d + PZ d d d) (PsiStar3D d d d) =
      prod3 y n n + prod3 n y n + prod3 n n y := by
    rw [centradoG_add, centradoG_add, PX, PY, PZ, centrado_X hd hd, centrado_Y hd hd,
      centrado_Z hd hd]; rfl
  have hin : inner ℂ (prod3 x n n + prod3 n x n + prod3 n n x) (prod3 y n n + prod3 n y n + prod3 n n y) =
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
  rw [anguloG, eT, eP, hin, hnT, hnP, anguloNRS, anguloG]
  congr 1
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hden : Real.sqrt 3 * ‖x‖ * (Real.sqrt 3 * ‖y‖) = 3 * (‖x‖ * ‖y‖) := by
    calc Real.sqrt 3 * ‖x‖ * (Real.sqrt 3 * ‖y‖) = (Real.sqrt 3 * Real.sqrt 3) * (‖x‖ * ‖y‖) := by
          ring
      _ = 3 * (‖x‖ * ‖y‖) := by rw [h3]
  rw [norm_mul, show ‖(3 : ℂ)‖ = 3 by simp, hden, mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]

end Igual

/-- **At the first rupture** `4 × 4 × 4`, the star of the three axes opens exactly
`θ_NRS(4) = arccos (1/√((99 − 42√5)/5)) ≈ 7.44°`. -/
theorem angulo_total_cuatro :
    anguloG (TX 4 4 4 + TY 4 4 4 + TZ 4 4 4) (PX 4 4 4 + PY 4 4 4 + PZ 4 4 4) (PsiStar3D 4 4 4) =
      arccos (1 / Real.sqrt ((99 - 42 * Real.sqrt 5) / 5)) := by
  rw [angulo_total_cubo (by norm_num), anguloNRS_cuatro]

end PitagorasCubo

end

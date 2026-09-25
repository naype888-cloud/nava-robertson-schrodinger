import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# D37c — The spectrum of the cube, axis by axis

On the cube of `D37`, every axis keeps the spectrum it has on the path (`D6`), and the cube
adds the three:

* **Per axis** (`autovector_lift`): an eigenvector of an axis operator, times any state of
  the other two axes, is an eigenvector of the lifted operator with the same eigenvalue.
* **Sum of spectra** (`autovector_suma`): a product `u ⊗ v ⊗ w` of eigenvectors of one
  operator per axis is an eigenvector of their sum, with eigenvalue `λ + μ + ν`.
* **Maximal tension of the cube** (`tensionTotal_psiStar`, `tensionTotal_le`): with
  `K_• = i[T_•, P_•]` per axis, `Ψ* = ψ* ⊗ ψ* ⊗ ψ*` is an eigenvector of
  `K_x + K_y + K_z` with eigenvalue `2/(dx−1) + 2/(dy−1) + 2/(dz−1)`, and no state of the
  cube exceeds it. The bound is proved by slicing a state into fibres along the axis.

Szegő on the cube therefore splits into the three one-dimensional limits of `D8`: no new
constant appears.
-/

noncomputable section

open TransportePosicion NavaRobertsonSchrodingerEDUI ConstructorEspectralTP
open PathGraph3D (Sitio3D)
open PathGraph3DNRS

namespace EspectroCubo

/-! ## 1. Eigenvectors lift along an axis -/

section Eje

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
  [DecidableEq ι] [DecidableEq α] [DecidableEq β]

theorem autovector_lift (e : ι ≃ α × β) (A : Matrix α α ℂ) {ψ : EuclideanSpace ℂ α} {c : ℂ}
    (h : Matrix.toEuclideanLin A ψ = c • ψ) (φ : EuclideanSpace ℂ β) :
    Matrix.toEuclideanLin (liftAlong e A) (prodAlong e ψ φ) = c • prodAlong e ψ φ := by
  rw [toEuclideanLin_liftAlong, h, prodAlong_smul]

/-! ## 2. Fibres along an axis -/

/-- The fibre of `Φ` over `b`: the axis `α` with the rest frozen at `b`. -/
def fibra (e : ι ≃ α × β) (Φ : EuclideanSpace ℂ ι) (b : β) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 fun a => Φ (e.symm (a, b))

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem inner_eq_sum_fibras (e : ι ≃ α × β) (Φ Ψ : EuclideanSpace ℂ ι) :
    inner ℂ Φ Ψ = ∑ b, inner ℂ (fibra e Φ b) (fibra e Ψ b) := by
  simp only [PiLp.inner_apply, fibra]
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type_right]

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem norm_sq_eq_sum_fibras (e : ι ≃ α × β) (Φ : EuclideanSpace ℂ ι) :
    ‖Φ‖ ^ 2 = ∑ b, ‖fibra e Φ b‖ ^ 2 := by
  have h := inner_eq_sum_fibras e Φ Φ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The lifted operator acts fibre by fibre. -/
theorem fibra_lift (e : ι ≃ α × β) (A : Matrix α α ℂ) (Φ : EuclideanSpace ℂ ι) (b : β) :
    fibra e (Matrix.toEuclideanLin (liftAlong e A) Φ) b =
      Matrix.toEuclideanLin A (fibra e Φ b) := by
  ext a
  simp only [fibra, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    liftAlong, Matrix.of_apply, Equiv.apply_symm_apply]
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type_right,
    Finset.sum_comm]
  simp [Equiv.apply_symm_apply, Finset.sum_ite_eq]

theorem fibra_tension (e : ι ≃ α × β) (A B : Matrix α α ℂ) (Φ : EuclideanSpace ℂ ι) (b : β) :
    fibra e (observableTension (Matrix.toEuclideanLin (liftAlong e A))
        (Matrix.toEuclideanLin (liftAlong e B)) Φ) b =
      observableTension (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (fibra e Φ b) := by
  simp only [observableTension, conmutador, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, ← fibra_lift]
  ext a
  simp [fibra]

end Eje

/-! ## 3. The tension bound on one axis, for every state -/

/-- On `H_d`, `Re ⟨v, K_d v⟩ ≤ (2/(d−1)) ‖v‖²` for every `v` (the top of the spectrum). -/
theorem tension_le_vec {d : ℕ} (hd : 2 ≤ d) (v : Hd d) :
    (inner ℂ v (KdOp d v)).re ≤ 2 / ((d : ℝ) - 1) * ‖v‖ ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  have hK := norma_aplicacion_le_radio_mul_norma (KdOp d) (KdOp_simetrico d) v
  rw [radioEspectral_KdOp_eq_paso d hd] at hK
  calc (inner ℂ v (KdOp d v)).re ≤ ‖inner ℂ v (KdOp d v)‖ := Complex.re_le_norm _
    _ ≤ ‖v‖ * ‖KdOp d v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (2 / ((d : ℝ) - 1) * ‖v‖) := mul_le_mul_of_nonneg_left hK (norm_nonneg _)
    _ = 2 / ((d : ℝ) - 1) * ‖v‖ ^ 2 := by ring

theorem tension_lift_le {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]
    {d : ℕ} (hd : 2 ≤ d) (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    (inner ℂ Φ (observableTension (Matrix.toEuclideanLin (liftAlong e (Td d)))
        (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ)).re ≤ 2 / ((d : ℝ) - 1) * ‖Φ‖ ^ 2 := by
  rw [inner_eq_sum_fibras e, Complex.re_sum, norm_sq_eq_sum_fibras e, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [fibra_tension]
  exact tension_le_vec hd _

/-! ## 4. The cube -/

section Cubo

variable {dx dy dz : ℕ}

/-- Product of one state per axis. -/
def prod3 (u : Hd dx) (v : Hd dy) (w : Hd dz) : H3D dx dy dz :=
  WithLp.toLp 2 fun p => u p.1 * v p.2.1 * w p.2.2

theorem prod3_eq_eX (u : Hd dx) (v : Hd dy) (w : Hd dz) :
    prod3 u v w = prodAlong (eX dx dy dz) u (prodAlong (Equiv.refl _) v w) := by
  ext p; simp [prod3, prodAlong_apply, eX, mul_assoc]

theorem prod3_eq_eY (u : Hd dx) (v : Hd dy) (w : Hd dz) :
    prod3 u v w = prodAlong (eY dx dy dz) v (prodAlong (Equiv.refl _) u w) := by
  ext p; simp [prod3, prodAlong_apply, eY]; ring

theorem prod3_eq_eZ (u : Hd dx) (v : Hd dy) (w : Hd dz) :
    prod3 u v w = prodAlong (eZ dx dy dz) w (prodAlong (Equiv.refl _) u v) := by
  ext p; simp [prod3, prodAlong_apply, eZ]; ring

theorem PsiStar3D_eq_prod3 : PsiStar3D dx dy dz = prod3 (psiStar dx) (psiStar dy) (psiStar dz) :=
  rfl

/-- **Sum of spectra.** One eigenvector per axis gives an eigenvector of the sum, with the
sum of the eigenvalues. -/
theorem autovector_suma (A : Matrix (Fin dx) (Fin dx) ℂ) (B : Matrix (Fin dy) (Fin dy) ℂ)
    (C : Matrix (Fin dz) (Fin dz) ℂ) {u : Hd dx} {v : Hd dy} {w : Hd dz} {l m n : ℂ}
    (hu : Matrix.toEuclideanLin A u = l • u) (hv : Matrix.toEuclideanLin B v = m • v)
    (hw : Matrix.toEuclideanLin C w = n • w) :
    (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A) +
        Matrix.toEuclideanLin (liftAlong (eY dx dy dz) B) +
        Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) C)) (prod3 u v w) =
      (l + m + n) • prod3 u v w := by
  have hx := autovector_lift (eX dx dy dz) A hu (prodAlong (Equiv.refl _) v w)
  have hy := autovector_lift (eY dx dy dz) B hv (prodAlong (Equiv.refl _) u w)
  have hz := autovector_lift (eZ dx dy dz) C hw (prodAlong (Equiv.refl _) u v)
  rw [← prod3_eq_eX] at hx
  rw [← prod3_eq_eY] at hy
  rw [← prod3_eq_eZ] at hz
  rw [LinearMap.add_apply, LinearMap.add_apply, hx, hy, hz, add_smul, add_smul]

/-- Tension of one axis on the cube, `K_x = i[T_x, P_x]`, and the total `K_x + K_y + K_z`. -/
def KX : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := observableTension (TX dx dy dz) (PX dx dy dz)
def KY : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := observableTension (TY dx dy dz) (PY dx dy dz)
def KZ : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := observableTension (TZ dx dy dz) (PZ dx dy dz)
def Ktotal : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := KX + KY + KZ

theorem tension_lift_apply {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι]
    [DecidableEq β] {d : ℕ} (e : ι ≃ Fin d × β) (ψ : Hd d) (φ : EuclideanSpace ℂ β) :
    observableTension (Matrix.toEuclideanLin (liftAlong e (Td d)))
        (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e ψ φ) =
      prodAlong e (KdOp d ψ) φ := by
  simp only [KdOp, TdOp, PdOp, observableTension, conmutador, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, toEuclideanLin_liftAlong, prodAlong_sub,
    prodAlong_smul]

theorem autovalor_psiStar {d : ℕ} (hd : 2 ≤ d) :
    KdOp d (psiStar d) = (((2 / ((d : ℝ) - 1) : ℝ)) : ℂ) • psiStar d :=
  KdOp_vectorFiedlerExplicito d hd

/-- **Maximal tension of the cube.** `Ψ*` is an eigenvector of `K_x + K_y + K_z` with
eigenvalue `2/(dx−1) + 2/(dy−1) + 2/(dz−1)`. -/
theorem tensionTotal_psiStar (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    Ktotal (PsiStar3D dx dy dz) =
      (((2 / ((dx : ℝ) - 1) + 2 / ((dy : ℝ) - 1) + 2 / ((dz : ℝ) - 1) : ℝ)) : ℂ) •
        PsiStar3D dx dy dz := by
  have ex : KX (PsiStar3D dx dy dz) = (((2 / ((dx : ℝ) - 1) : ℝ)) : ℂ) • PsiStar3D dx dy dz := by
    rw [PsiStar3D_eq_eX, KX, TX, PX, tension_lift_apply, autovalor_psiStar hx, prodAlong_smul]
  have ey : KY (PsiStar3D dx dy dz) = (((2 / ((dy : ℝ) - 1) : ℝ)) : ℂ) • PsiStar3D dx dy dz := by
    rw [PsiStar3D_eq_eY, KY, TY, PY, tension_lift_apply, autovalor_psiStar hy, prodAlong_smul]
  have ez : KZ (PsiStar3D dx dy dz) = (((2 / ((dz : ℝ) - 1) : ℝ)) : ℂ) • PsiStar3D dx dy dz := by
    rw [PsiStar3D_eq_eZ, KZ, TZ, PZ, tension_lift_apply, autovalor_psiStar hz, prodAlong_smul]
  rw [Ktotal, LinearMap.add_apply, LinearMap.add_apply, ex, ey, ez, ← add_smul, ← add_smul]
  push_cast
  ring_nf

/-- **No state of the cube exceeds it.** For every `Φ`,
`Re ⟨Φ, (K_x + K_y + K_z) Φ⟩ ≤ (2/(dx−1) + 2/(dy−1) + 2/(dz−1)) ‖Φ‖²`. -/
theorem tensionTotal_le (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (Φ : H3D dx dy dz) :
    (inner ℂ Φ (Ktotal Φ)).re ≤
      (2 / ((dx : ℝ) - 1) + 2 / ((dy : ℝ) - 1) + 2 / ((dz : ℝ) - 1)) * ‖Φ‖ ^ 2 := by
  have bx := tension_lift_le hx (eX dx dy dz) Φ
  have by' := tension_lift_le hy (eY dx dy dz) Φ
  have bz := tension_lift_le hz (eZ dx dy dz) Φ
  simp only [Ktotal, KX, KY, KZ, TX, PX, TY, PY, TZ, PZ, LinearMap.add_apply, inner_add_right,
    Complex.add_re]
  nlinarith [bx, by', bz]

end Cubo

end EspectroCubo

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# D37c — The spectrum of the cube, axis by axis

Each axis keeps its spectrum on the path (`D6`) and the cube adds the three. The Szegő limit
on the cube splits into the three limits of `D8`; no new constant appears.

## Main results

- `CubeSpectrum.eigenvector_lift` : an axis eigenvector times any state of the other axes is
  an eigenvector of the lifted operator.
- `CubeSpectrum.eigenvector_sum` : `u ⊗ v ⊗ w` is an eigenvector of the sum with eigenvalue
  `λ + μ + ν`.
- `CubeSpectrum.tensionTotal_psiStar`, `CubeSpectrum.tensionTotal_le` : `Ψ*` is the top of
  `K_x + K_y + K_z`, with eigenvalue `Σ 2/(dᵢ − 1)`, which no state exceeds.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality SpectralExtremal
open PathGraph3D (Site3D)
open PathGraph3DNRS

namespace CubeSpectrum

/-! ## 1. Eigenvectors lift along an axis -/

section Eje

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
  [DecidableEq ι] [DecidableEq α] [DecidableEq β]

theorem eigenvector_lift (e : ι ≃ α × β) (A : Matrix α α ℂ) {ψ : EuclideanSpace ℂ α} {c : ℂ}
    (h : Matrix.toEuclideanLin A ψ = c • ψ) (φ : EuclideanSpace ℂ β) :
    Matrix.toEuclideanLin (liftAlong e A) (prodAlong e ψ φ) = c • prodAlong e ψ φ := by
  rw [toEuclideanLin_liftAlong, h, prodAlong_smul]

/-! ## 2. Fibres along an axis -/

/-- The fibre of `Φ` over `b`: the axis `α` with the rest frozen at `b`. -/
def fiber (e : ι ≃ α × β) (Φ : EuclideanSpace ℂ ι) (b : β) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 fun a => Φ (e.symm (a, b))

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem inner_eq_sum_fibers (e : ι ≃ α × β) (Φ Ψ : EuclideanSpace ℂ ι) :
    inner ℂ Φ Ψ = ∑ b, inner ℂ (fiber e Φ b) (fiber e Ψ b) := by
  simp only [PiLp.inner_apply, fiber]
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type_right]

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem norm_sq_eq_sum_fibers (e : ι ≃ α × β) (Φ : EuclideanSpace ℂ ι) :
    ‖Φ‖ ^ 2 = ∑ b, ‖fiber e Φ b‖ ^ 2 := by
  have h := inner_eq_sum_fibers e Φ Φ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The lifted operator acts fibre by fibre. -/
theorem fiber_lift (e : ι ≃ α × β) (A : Matrix α α ℂ) (Φ : EuclideanSpace ℂ ι) (b : β) :
    fiber e (Matrix.toEuclideanLin (liftAlong e A) Φ) b =
      Matrix.toEuclideanLin A (fiber e Φ b) := by
  ext a
  simp only [fiber, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    liftAlong, Matrix.of_apply, Equiv.apply_symm_apply]
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type_right,
    Finset.sum_comm]
  simp [Equiv.apply_symm_apply, Finset.sum_ite_eq]

theorem fiber_tension (e : ι ≃ α × β) (A B : Matrix α α ℂ) (Φ : EuclideanSpace ℂ ι) (b : β) :
    fiber e (observableTension (Matrix.toEuclideanLin (liftAlong e A))
        (Matrix.toEuclideanLin (liftAlong e B)) Φ) b =
      observableTension (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (fiber e Φ b) := by
  simp only [observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, ← fiber_lift]
  ext a
  simp [fiber]

end Eje

/-! ## 3. The tension bound on one axis, for every state -/

/-- On `H_d`, `Re ⟨v, K_d v⟩ ≤ (2/(d−1)) ‖v‖²` for every `v` (the top of the spectrum). -/
theorem tension_le_vec {d : ℕ} (hd : 2 ≤ d) (v : Hd d) :
    (inner ℂ v (KdOp d v)).re ≤ 2 / ((d : ℝ) - 1) * ‖v‖ ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  have hK := norm_apply_le_specRadius_mul_norm (KdOp d) (KdOp_isSymmetric d) v
  rw [specRadius_KdOp_eq_step d hd] at hK
  calc (inner ℂ v (KdOp d v)).re ≤ ‖inner ℂ v (KdOp d v)‖ := Complex.re_le_norm _
    _ ≤ ‖v‖ * ‖KdOp d v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (2 / ((d : ℝ) - 1) * ‖v‖) := mul_le_mul_of_nonneg_left hK (norm_nonneg _)
    _ = 2 / ((d : ℝ) - 1) * ‖v‖ ^ 2 := by ring

theorem tension_lift_le {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]
    {d : ℕ} (hd : 2 ≤ d) (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    (inner ℂ Φ (observableTension (Matrix.toEuclideanLin (liftAlong e (Td d)))
        (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ)).re ≤ 2 / ((d : ℝ) - 1) * ‖Φ‖ ^ 2 := by
  rw [inner_eq_sum_fibers e, Complex.re_sum, norm_sq_eq_sum_fibers e, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [fiber_tension]
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
theorem eigenvector_sum (A : Matrix (Fin dx) (Fin dx) ℂ) (B : Matrix (Fin dy) (Fin dy) ℂ)
    (C : Matrix (Fin dz) (Fin dz) ℂ) {u : Hd dx} {v : Hd dy} {w : Hd dz} {l m n : ℂ}
    (hu : Matrix.toEuclideanLin A u = l • u) (hv : Matrix.toEuclideanLin B v = m • v)
    (hw : Matrix.toEuclideanLin C w = n • w) :
    (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A) +
        Matrix.toEuclideanLin (liftAlong (eY dx dy dz) B) +
        Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) C)) (prod3 u v w) =
      (l + m + n) • prod3 u v w := by
  have hx := eigenvector_lift (eX dx dy dz) A hu (prodAlong (Equiv.refl _) v w)
  have hy := eigenvector_lift (eY dx dy dz) B hv (prodAlong (Equiv.refl _) u w)
  have hz := eigenvector_lift (eZ dx dy dz) C hw (prodAlong (Equiv.refl _) u v)
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
  simp only [KdOp, TdOp, PdOp, observableTension, opCommutator, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, toEuclideanLin_liftAlong, prodAlong_sub,
    prodAlong_smul]

theorem eigenvalue_psiStar {d : ℕ} (hd : 2 ≤ d) :
    KdOp d (psiStar d) = (((2 / ((d : ℝ) - 1) : ℝ)) : ℂ) • psiStar d :=
  KdOp_fiedlerVec d hd

/-- **Maximal tension of the cube.** `Ψ*` is an eigenvector of `K_x + K_y + K_z` with
eigenvalue `2/(dx−1) + 2/(dy−1) + 2/(dz−1)`. -/
theorem tensionTotal_psiStar (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    Ktotal (PsiStar3D dx dy dz) =
      (((2 / ((dx : ℝ) - 1) + 2 / ((dy : ℝ) - 1) + 2 / ((dz : ℝ) - 1) : ℝ)) : ℂ) •
        PsiStar3D dx dy dz := by
  have ex : KX (PsiStar3D dx dy dz) = (((2 / ((dx : ℝ) - 1) : ℝ)) : ℂ) • PsiStar3D dx dy dz := by
    rw [PsiStar3D_eq_eX, KX, TX, PX, tension_lift_apply, eigenvalue_psiStar hx, prodAlong_smul]
  have ey : KY (PsiStar3D dx dy dz) = (((2 / ((dy : ℝ) - 1) : ℝ)) : ℂ) • PsiStar3D dx dy dz := by
    rw [PsiStar3D_eq_eY, KY, TY, PY, tension_lift_apply, eigenvalue_psiStar hy, prodAlong_smul]
  have ez : KZ (PsiStar3D dx dy dz) = (((2 / ((dz : ℝ) - 1) : ℝ)) : ℂ) • PsiStar3D dx dy dz := by
    rw [PsiStar3D_eq_eZ, KZ, TZ, PZ, tension_lift_apply, eigenvalue_psiStar hz, prodAlong_smul]
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

end CubeSpectrum

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D4_WhyNotDiagonal
public import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap

/-!
# D37 — The path graph in three axes: one pair `(T, P)` per axis

The cube `Site3D dx dy dz = Fin dx × Fin dy × Fin dz` of `D4` is the Cartesian product of
three paths. Each axis carries the pair `(T_d, P_d)` of `D3` on its coordinate and the
identity on the other two. Everything is proved once for a general axis (`liftAlong`,
`prodAlong`) and instantiated through `eX`, `eY`, `eZ`.

## Main results

- `PathGraph3DNRS.commutator_axes_xy` (and `_xz`, `_yz`) : pairs on different axes commute.
- `PathGraph3DNRS.stats_axis_x` (and `_y`, `_z`) : at `Ψ* = ψ* ⊗ ψ* ⊗ ψ*` the mean, variance,
  covariance and tension of an axis are those of `D21` for that axis.
- `PathGraph3DNRS.saturation_cube` : an axis saturates iff it has `2` or `3` sites.
- `PathGraph3DNRS.strict_cube` : from `4 × 4 × 4`, strict on all three axes.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality SpectralExtremal
open PathGraph3D (Site3D)

namespace PathGraph3DNRS

/-! ## 1. One axis inside a product -/

section Eje

variable {ι α β : Type*}

/-- The product state: amplitude `ψ` on the axis times `φ` on the rest. -/
def prodAlong (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun p => ψ (e p).1 * φ (e p).2

theorem prodAlong_apply (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β)
    (p : ι) : prodAlong e ψ φ p = ψ (e p).1 * φ (e p).2 := rfl

theorem prodAlong_sub (e : ι ≃ α × β) (ψ ψ' : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    prodAlong e (ψ - ψ') φ = prodAlong e ψ φ - prodAlong e ψ' φ := by
  ext p
  simp [prodAlong_apply, sub_mul]

theorem prodAlong_smul (e : ι ≃ α × β) (c : ℂ) (ψ : EuclideanSpace ℂ α)
    (φ : EuclideanSpace ℂ β) : prodAlong e (c • ψ) φ = c • prodAlong e ψ φ := by
  ext p
  simp [prodAlong_apply, mul_assoc]

variable [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq α] [DecidableEq β]

/-- An operator `A` on the axis `α`, lifted to `ι ≃ α × β`: `A` on the axis, identity on the
rest. -/
def liftAlong (e : ι ≃ α × β) (A : Matrix α α ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun p q => A (e p).1 (e q).1 * if (e p).2 = (e q).2 then 1 else 0

/-- The lifted operator acts on the axis factor only. -/
theorem toEuclideanLin_liftAlong (e : ι ≃ α × β) (A : Matrix α α ℂ)
    (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    Matrix.toEuclideanLin (liftAlong e A) (prodAlong e ψ φ) =
      prodAlong e (Matrix.toEuclideanLin A ψ) φ := by
  ext p
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    prodAlong_apply, liftAlong, Matrix.of_apply]
  rw [Fintype.sum_equiv e _ (fun x => A (e p).1 x.1 * (if (e p).2 = x.2 then 1 else 0) *
    (ψ x.1 * φ x.2)) (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, mul_assoc]

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
/-- Inner products factor over the product. -/
theorem inner_prodAlong (e : ι ≃ α × β) (ψ ψ' : EuclideanSpace ℂ α)
    (φ φ' : EuclideanSpace ℂ β) :
    inner ℂ (prodAlong e ψ φ) (prodAlong e ψ' φ') = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, prodAlong_apply]
  rw [Fintype.sum_equiv e _ (fun x => ψ' x.1 * φ' x.2 * (starRingEnd ℂ) (ψ x.1 * φ x.2))
    (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul]
  ring

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem norm_sq_prodAlong (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α)
    (φ : EuclideanSpace ℂ β) (hφ : ‖φ‖ = 1) : ‖prodAlong e ψ φ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have h := inner_prodAlong e ψ ψ φ φ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    hφ] at h
  exact_mod_cast (by simpa using h : ((‖prodAlong e ψ φ‖ ^ 2 : ℝ) : ℂ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ))

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem norm_prodAlong_eq_one (e : ι ≃ α × β) {ψ : EuclideanSpace ℂ α}
    {φ : EuclideanSpace ℂ β} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) : ‖prodAlong e ψ φ‖ = 1 := by
  have h := norm_sq_prodAlong e ψ φ hφ
  rw [hψ, one_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem inner_self_of_norm_one {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1) :
    inner ℂ φ φ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hφ]
  simp

/-! ## 2. The `D21` statistics on any finite site set -/

/-- Mean `Re ⟨Ψ, LΨ⟩`: `D21`'s `mean` on `ℂ^ι` (it is `mean` itself when `ι = Fin d`). -/
def meanG (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ Ψ (L Ψ)).re

def centeredG (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  L Ψ - (meanG L Ψ : ℂ) • Ψ

def varianceG (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  ‖centeredG L Ψ‖ ^ 2

def covarianceG (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ (centeredG L Ψ) (centeredG M Ψ)).re

/-- Tension `⟨i[L, M]⟩` (`D23b`'s `tension` on `ℂ^ι`). -/
def tensionG (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ Ψ (observableTension L M Ψ)).re

/-! ## 3. Lifted statistics are the statistics of the axis -/

variable (e : ι ≃ α × β) {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1)
include hφ

theorem meanG_lift (A : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    meanG (Matrix.toEuclideanLin (liftAlong e A)) (prodAlong e ψ φ) =
      meanG (Matrix.toEuclideanLin A) ψ := by
  rw [meanG, meanG, toEuclideanLin_liftAlong, inner_prodAlong, inner_self_of_norm_one hφ,
    mul_one]

theorem centeredG_lift (A : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    centeredG (Matrix.toEuclideanLin (liftAlong e A)) (prodAlong e ψ φ) =
      prodAlong e (centeredG (Matrix.toEuclideanLin A) ψ) φ := by
  rw [centeredG, centeredG, meanG_lift e hφ, toEuclideanLin_liftAlong, prodAlong_sub,
    prodAlong_smul]

theorem varianceG_lift (A : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    varianceG (Matrix.toEuclideanLin (liftAlong e A)) (prodAlong e ψ φ) =
      varianceG (Matrix.toEuclideanLin A) ψ := by
  rw [varianceG, varianceG, centeredG_lift e hφ, norm_sq_prodAlong e _ _ hφ]

theorem covarianceG_lift (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    covarianceG (Matrix.toEuclideanLin (liftAlong e A)) (Matrix.toEuclideanLin (liftAlong e B))
        (prodAlong e ψ φ) =
      covarianceG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  rw [covarianceG, covarianceG, centeredG_lift e hφ, centeredG_lift e hφ, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one]

theorem tensionG_lift (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    tensionG (Matrix.toEuclideanLin (liftAlong e A)) (Matrix.toEuclideanLin (liftAlong e B))
        (prodAlong e ψ φ) =
      tensionG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  simp only [tensionG, observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, toEuclideanLin_liftAlong, ← prodAlong_sub, ← prodAlong_smul,
    inner_prodAlong, inner_self_of_norm_one hφ, mul_one]

/-! ## 4. NRS on one axis of a product -/

/-- On any axis with `d ≥ 2` sites, lifted into a product with a unit state `φ` on the rest,
the four statistics of `(T, P)` at `ψ* ⊗ φ` are those of `(T_d, P_d)` at `ψ*` (`D21`). -/
theorem stats_axis {d : ℕ} (hd : 2 ≤ d) (e : ι ≃ Fin d × β) :
    varianceG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e (psiStar d) φ) =
        variance (TdOp d) (psiStar d) ∧
      varianceG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) =
        variance (PdOp d) (psiStar d) ∧
      covarianceG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) =
        covariance (TdOp d) (PdOp d) (psiStar d) ∧
      tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) =
        2 / ((d : ℝ) - 1) :=
  ⟨varianceG_lift e hφ _ _, varianceG_lift e hφ _ _, covarianceG_lift e hφ _ _ _,
    (tensionG_lift e hφ _ _ _).trans (NearMaxTension.tension_psiStar hd)⟩

/-- NRS on one axis: saturation exactly for `2` or `3` sites on that axis. -/
theorem saturation_axis {d : ℕ} (hd : 2 ≤ d) (e : ι ≃ Fin d × β) :
    covarianceG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) ^ 2 +
        (commutatorConstant d / 2) ^ 2 =
      varianceG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e (psiStar d) φ) *
        varianceG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) ↔
      d = 2 ∨ d = 3 := by
  obtain ⟨h1, h2, h3, -⟩ := stats_axis hφ hd e
  rw [h1, h2, h3]
  exact saturation_iff hd

/-- NRS on one axis: from `4` sites on, the inequality is strict (the algebraic quantum). -/
theorem strict_axis {d : ℕ} (hd : 4 ≤ d) (e : ι ≃ Fin d × β) :
    covarianceG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) ^ 2 +
        (commutatorConstant d / 2) ^ 2 <
      varianceG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e (psiStar d) φ) *
        varianceG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) := by
  obtain ⟨h1, h2, h3, -⟩ := stats_axis hφ (by omega) e
  rw [h1, h2, h3]
  exact strict_inequality hd

end Eje

/-! ## 5. The cube `Site3D dx dy dz` of `D4` -/

section Cubo

variable (dx dy dz : ℕ)

/-- States on the cube: amplitudes on its `dx·dy·dz` sites. -/
abbrev H3D := EuclideanSpace ℂ (Site3D dx dy dz)

/-- The `x` axis and the rest `(y, z)`. -/
def eX : Site3D dx dy dz ≃ Fin dx × (Fin dy × Fin dz) := Equiv.refl _

/-- The `y` axis and the rest `(x, z)`. -/
def eY : Site3D dx dy dz ≃ Fin dy × (Fin dx × Fin dz) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun q := (q.2.1, q.1, q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `z` axis and the rest `(x, y)`. -/
def eZ : Site3D dx dy dz ≃ Fin dz × (Fin dx × Fin dy) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun q := (q.2.1, q.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `T` and `P` of each axis: `(T_d, P_d)` of `D3` on that coordinate, identity on the others. -/
def TX : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := Matrix.toEuclideanLin (liftAlong (eX dx dy dz) (Td dx))
def PX : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := Matrix.toEuclideanLin (liftAlong (eX dx dy dz) (Pd dx))
def TY : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := Matrix.toEuclideanLin (liftAlong (eY dx dy dz) (Td dy))
def PY : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := Matrix.toEuclideanLin (liftAlong (eY dx dy dz) (Pd dy))
def TZ : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) (Td dz))
def PZ : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz := Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) (Pd dz))

/-- The maximal-tension state of the cube: `ψ*` on each axis. -/
def PsiStar3D : H3D dx dy dz :=
  WithLp.toLp 2 fun p => psiStar dx p.1 * psiStar dy p.2.1 * psiStar dz p.2.2

theorem PsiStar3D_eq_eX :
    PsiStar3D dx dy dz =
      prodAlong (eX dx dy dz) (psiStar dx) (prodAlong (Equiv.refl _) (psiStar dy) (psiStar dz)) :=
          by
  ext p
  simp [PsiStar3D, prodAlong_apply, eX, mul_assoc]

theorem PsiStar3D_eq_eY :
    PsiStar3D dx dy dz =
      prodAlong (eY dx dy dz) (psiStar dy) (prodAlong (Equiv.refl _) (psiStar dx) (psiStar dz)) :=
          by
  ext p
  simp [PsiStar3D, prodAlong_apply, eY]
  ring

theorem PsiStar3D_eq_eZ :
    PsiStar3D dx dy dz =
      prodAlong (eZ dx dy dz) (psiStar dz) (prodAlong (Equiv.refl _) (psiStar dx) (psiStar dy)) :=
          by
  ext p
  simp [PsiStar3D, prodAlong_apply, eZ]
  ring

/-! ## 6. Different axes commute -/

/-- Operators whose matrices commute have zero commutator. -/
theorem commutator_eq_zero_of_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℂ} (h : M * N = N * M) :
    opCommutator (Matrix.toEuclideanLin M) (Matrix.toEuclideanLin N) = 0 := by
  rw [opCommutator, ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, h, sub_self]

theorem liftAlong_xy_comm (A : Matrix (Fin dx) (Fin dx) ℂ) (B : Matrix (Fin dy) (Fin dy) ℂ) :
    liftAlong (eX dx dy dz) A * liftAlong (eY dx dy dz) B =
      liftAlong (eY dx dy dz) B * liftAlong (eX dx dy dz) A := by
  ext p q
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, eX, eY, Equiv.refl_apply,
    Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_xz_comm (A : Matrix (Fin dx) (Fin dx) ℂ) (B : Matrix (Fin dz) (Fin dz) ℂ) :
    liftAlong (eX dx dy dz) A * liftAlong (eZ dx dy dz) B =
      liftAlong (eZ dx dy dz) B * liftAlong (eX dx dy dz) A := by
  ext p q
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, eX, eZ, Equiv.refl_apply,
    Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_yz_comm (A : Matrix (Fin dy) (Fin dy) ℂ) (B : Matrix (Fin dz) (Fin dz) ℂ) :
    liftAlong (eY dx dy dz) A * liftAlong (eZ dx dy dz) B =
      liftAlong (eZ dx dy dz) B * liftAlong (eY dx dy dz) A := by
  ext p q
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, eY, eZ, Equiv.coe_fn_mk,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

/-- `[x, p_y] = 0`: any operator of the `x` axis commutes with any operator of the `y` axis
(in particular `[T_x, P_y] = [P_x, T_y] = [T_x, T_y] = [P_x, P_y] = 0`). Only the pair of the
same axis collides. -/
theorem commutator_axes_xy (A : Matrix (Fin dx) (Fin dx) ℂ)
    (B : Matrix (Fin dy) (Fin dy) ℂ) :
    opCommutator (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A))
      (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) B)) = 0 :=
  commutator_eq_zero_of_mul_comm (liftAlong_xy_comm dx dy dz A B)

theorem commutator_axes_xz (A : Matrix (Fin dx) (Fin dx) ℂ)
    (B : Matrix (Fin dz) (Fin dz) ℂ) :
    opCommutator (Matrix.toEuclideanLin (liftAlong (eX dx dy dz) A))
      (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) B)) = 0 :=
  commutator_eq_zero_of_mul_comm (liftAlong_xz_comm dx dy dz A B)

theorem commutator_axes_yz (A : Matrix (Fin dy) (Fin dy) ℂ)
    (B : Matrix (Fin dz) (Fin dz) ℂ) :
    opCommutator (Matrix.toEuclideanLin (liftAlong (eY dx dy dz) A))
      (Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) B)) = 0 :=
  commutator_eq_zero_of_mul_comm (liftAlong_yz_comm dx dy dz A B)

variable {dx dy dz}

theorem norm_rest {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ‖prodAlong (Equiv.refl (Fin a × Fin b)) (psiStar a) (psiStar b)‖ = 1 :=
  norm_prodAlong_eq_one _ (norm_psiStar ha) (norm_psiStar hb)

/-! ## 7. NRS on each axis of the cube -/

theorem stats_axis_x (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    varianceG (TX dx dy dz) (PsiStar3D dx dy dz) = variance (TdOp dx) (psiStar dx) ∧
      varianceG (PX dx dy dz) (PsiStar3D dx dy dz) = variance (PdOp dx) (psiStar dx) ∧
      covarianceG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) =
        covariance (TdOp dx) (PdOp dx) (psiStar dx) ∧
      tensionG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) = 2 / ((dx : ℝ) - 1) := by
  rw [PsiStar3D_eq_eX]
  exact stats_axis (norm_rest hy hz) hx _

theorem stats_axis_y (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    varianceG (TY dx dy dz) (PsiStar3D dx dy dz) = variance (TdOp dy) (psiStar dy) ∧
      varianceG (PY dx dy dz) (PsiStar3D dx dy dz) = variance (PdOp dy) (psiStar dy) ∧
      covarianceG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) =
        covariance (TdOp dy) (PdOp dy) (psiStar dy) ∧
      tensionG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) = 2 / ((dy : ℝ) - 1) := by
  rw [PsiStar3D_eq_eY]
  exact stats_axis (norm_rest hx hz) hy _

theorem stats_axis_z (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    varianceG (TZ dx dy dz) (PsiStar3D dx dy dz) = variance (TdOp dz) (psiStar dz) ∧
      varianceG (PZ dx dy dz) (PsiStar3D dx dy dz) = variance (PdOp dz) (psiStar dz) ∧
      covarianceG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) =
        covariance (TdOp dz) (PdOp dz) (psiStar dz) ∧
      tensionG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) = 2 / ((dz : ℝ) - 1) := by
  rw [PsiStar3D_eq_eZ]
  exact stats_axis (norm_rest hx hy) hz _

/-- **NRS on the cube.** Each axis saturates Robertson–Schrödinger exactly when it has `2` or
`3` sites, independently of the other two axes. -/
theorem saturation_cube (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    (covarianceG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) ^ 2 +
          (commutatorConstant dx / 2) ^ 2 =
        varianceG (TX dx dy dz) (PsiStar3D dx dy dz) * varianceG (PX dx dy dz) (PsiStar3D dx dy dz)
        ↔ dx = 2 ∨ dx = 3) ∧
    (covarianceG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) ^ 2 +
          (commutatorConstant dy / 2) ^ 2 =
        varianceG (TY dx dy dz) (PsiStar3D dx dy dz) * varianceG (PY dx dy dz) (PsiStar3D dx dy dz)
        ↔ dy = 2 ∨ dy = 3) ∧
    (covarianceG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) ^ 2 +
          (commutatorConstant dz / 2) ^ 2 =
        varianceG (TZ dx dy dz) (PsiStar3D dx dy dz) * varianceG (PZ dx dy dz) (PsiStar3D dx dy dz)
        ↔ dz = 2 ∨ dz = 3) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PsiStar3D_eq_eX]; exact saturation_axis (norm_rest hy hz) hx _
  · rw [PsiStar3D_eq_eY]; exact saturation_axis (norm_rest hx hz) hy _
  · rw [PsiStar3D_eq_eZ]; exact saturation_axis (norm_rest hx hy) hz _

/-- **The algebraic quantum on the `4 × 4 × 4` cube and beyond.** With at least `4` sites on
every axis, the inequality is strict on all three axes at once. -/
theorem strict_cube (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    covarianceG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) ^ 2 +
          (commutatorConstant dx / 2) ^ 2 <
        varianceG (TX dx dy dz) (PsiStar3D dx dy dz) * varianceG (PX dx dy dz) (PsiStar3D dx dy dz)
            ∧
    covarianceG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) ^ 2 +
          (commutatorConstant dy / 2) ^ 2 <
        varianceG (TY dx dy dz) (PsiStar3D dx dy dz) * varianceG (PY dx dy dz) (PsiStar3D dx dy dz)
            ∧
    covarianceG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) ^ 2 +
          (commutatorConstant dz / 2) ^ 2 <
        varianceG (TZ dx dy dz) (PsiStar3D dx dy dz) * varianceG (PZ dx dy dz) (PsiStar3D dx dy dz)
            := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PsiStar3D_eq_eX]; exact strict_axis (norm_rest (by omega) (by omega)) hx _
  · rw [PsiStar3D_eq_eY]; exact strict_axis (norm_rest (by omega) (by omega)) hy _
  · rw [PsiStar3D_eq_eZ]; exact strict_axis (norm_rest (by omega) (by omega)) hz _

end Cubo

end PathGraph3DNRS

end

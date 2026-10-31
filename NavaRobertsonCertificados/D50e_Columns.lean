/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50d_GramLipschitz

/-!
# D50e — A state of `ℂ^d ⊗ ℂ^β` column by column

The columns `Φ(·, r)` of a state of an axis times the rest. Inner products and norms add over
columns, a lifted operator acts on each column, and so does the tension `K_d`. These are the three
facts that carry the spectral gap of `D23c` from `ℂ^d` to every state of the cube.
-/

@[expose] public noncomputable section

open TransportPosition NearMaxTension PathGraph3DNRS AxisDefectEntangled BandWidth SpectralExtremal

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Columns

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] {d : ℕ}

/-- The column `r` of `Φ` as a state of `H_d`. -/
def colE (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) : Hd d :=
  WithLp.toLp 2 (col e Φ r)

theorem colE_apply (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) (i : Fin d) :
    colE e Φ r i = Φ (e.symm (i, r)) := rfl

omit [DecidableEq ι] [DecidableEq β] in
theorem colE_sub (e : ι ≃ Fin d × β) (Φ Ψ : EuclideanSpace ℂ ι) (r : β) :
    colE e (Φ - Ψ) r = colE e Φ r - colE e Ψ r := by
  ext i; simp [colE_apply]

omit [DecidableEq ι] [DecidableEq β] in
theorem colE_smul (e : ι ≃ Fin d × β) (c : ℂ) (Φ : EuclideanSpace ℂ ι) (r : β) :
    colE e (c • Φ) r = c • colE e Φ r := by
  ext i; simp [colE_apply]

omit [DecidableEq ι] [DecidableEq β] in
theorem colE_add (e : ι ≃ Fin d × β) (Φ Ψ : EuclideanSpace ℂ ι) (r : β) :
    colE e (Φ + Ψ) r = colE e Φ r + colE e Ψ r := by
  ext i; simp [colE_apply]

omit [DecidableEq ι] [DecidableEq β] in
/-- **Inner products add over columns.** -/
theorem inner_eq_sum_col (e : ι ≃ Fin d × β) (Φ Ψ : EuclideanSpace ℂ ι) :
    inner ℂ Φ Ψ = ∑ r, inner ℂ (colE e Φ r) (colE e Ψ r) := by
  simp only [PiLp.inner_apply, colE_apply]
  rw [Fintype.sum_equiv e _ (fun x => inner ℂ (Φ (e.symm x)) (Ψ (e.symm x)))
    (fun p => by simp), Fintype.sum_prod_type, Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq β] in
theorem norm_sq_eq_sum_col (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    ‖Φ‖ ^ 2 = ∑ r, ‖colE e Φ r‖ ^ 2 := by
  have h := inner_eq_sum_col e Φ Φ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- A lifted operator acts on each column. -/
theorem colE_lift (e : ι ≃ Fin d × β) (A : Matrix (Fin d) (Fin d) ℂ)
    (Φ : EuclideanSpace ℂ ι) (r : β) :
    colE e (Matrix.toEuclideanLin (liftAlong e A) Φ) r = Matrix.toEuclideanLin A (colE e Φ r) := by
  ext i
  rw [colE_apply, liftAlong_apply_col]
  simp [colE, col, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- A lifted contraction is a contraction. -/
theorem norm_lift_le (e : ι ≃ Fin d × β) {A : Matrix (Fin d) (Fin d) ℂ}
    (hc : ∀ x : Hd d, ‖Matrix.toEuclideanLin A x‖ ≤ ‖x‖) (Φ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin (liftAlong e A) Φ‖ ≤ ‖Φ‖ := by
  have h : ‖Matrix.toEuclideanLin (liftAlong e A) Φ‖ ^ 2 ≤ ‖Φ‖ ^ 2 := by
    rw [norm_sq_eq_sum_col e, norm_sq_eq_sum_col e Φ]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [colE_lift]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc _) 2
  exact le_of_sq_le_sq h (norm_nonneg _) |>.trans_eq rfl

/-- **The tension adds over columns.** -/
theorem tensionG_eq_sum_col (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
        (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ = ∑ r, tension d (colE e Φ r) := by
  have hcol : ∀ r, colE e (observableTension (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ) r = KdOp d (colE e Φ r) := by
    intro r
    simp only [KdOp, observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, colE_smul, colE_sub, colE_lift]
    rfl
  rw [tensionG, inner_eq_sum_col e, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hcol]
  rfl

end Columns

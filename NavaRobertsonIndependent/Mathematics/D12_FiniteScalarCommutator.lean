/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# D12 — No scalar commutator in finite dimension

In finite dimension no commutator is a nonzero multiple of the identity: `[Q, P]` has trace
zero (`Matrix.trace_mul_comm`). This concerns the additive commutator only; the multiplicative
relation `W₂ W₁ = −W₁ W₂` holds exactly for `W₁ = !![0,1;1,0]`, `W₂ = !![1,0;0,-1]`.

## Main results

- `FiniteScalarCommutator.no_nonzero_scalar_exact_commutator` : `[Q, P] ≠ c • 1` for `c ≠ 0`.
- `FiniteScalarCommutator.weylPair_anticomm` : `W₂ W₁ = −(W₁ W₂)`.
-/

@[expose] public noncomputable section

namespace FiniteScalarCommutator

/-- The matrix commutator `[Q, P] = QP − PQ`. -/
def commutator {d : ℕ}
    (Q P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Q * P - P * Q

/-- A matrix commutator has trace zero. -/
theorem trace_commutator_zero {d : ℕ}
    (Q P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (commutator Q P) = 0 := by
  rw [commutator, Matrix.trace_sub, Matrix.trace_mul_comm Q P, sub_self]

/-- In positive finite dimension a commutator is not a nonzero multiple of the identity. -/
theorem no_nonzero_scalar_exact_commutator {d : ℕ} (hd : 0 < d)
    (Q P : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hc : c ≠ 0) :
    commutator Q P ≠ c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  have hleft : Matrix.trace (commutator Q P) = 0 :=
    trace_commutator_zero Q P
  have hright : Matrix.trace (c • (1 : Matrix (Fin d) (Fin d) ℂ)) = c * d := by
    simp
  rw [hleft, hright] at ht
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  exact (mul_ne_zero hc hd0) ht.symm

/-- In particular a commutator is not `i c • 1` for a real `c ≠ 0`. -/
theorem commutator_ne_imaginary_scalar {d : ℕ} (hd : 0 < d)
    (Q P : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (hc : c ≠ 0) :
    commutator Q P ≠ (Complex.I * (c : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  apply no_nonzero_scalar_exact_commutator hd Q P
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc)

/-! ## An exact Weyl pair in dimension two -/

/-- The first matrix of the Weyl pair. -/
def W1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The second matrix of the Weyl pair. -/
def W2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- **Weyl relation.** `W₂ W₁ = −(W₁ W₂)`. -/
theorem weylPair_anticomm : W2 * W1 = -(W1 * W2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W1, W2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `W₁` and `W₂` do not commute. -/
theorem weylPair_not_comm : W2 * W1 ≠ W1 * W2 := by
  intro h
  have hij := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [W1, W2, Matrix.mul_apply, Fin.sum_univ_two] at hij

end FiniteScalarCommutator

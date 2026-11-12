/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation
public import NavaRobertsonIndependent.Mathematics.D56_MassNecessaryConditions

/-!
# D57 — The fourth condition: the defect belongs to the state, not to the carrier

`D56` shows that `c`, `ℓ > 0` and `C_N > 1` are necessary for mass and hold iff `4 ≤ d`. They
are not sufficient: a carrier meets all three and has no mass. Here the carrier is a basis
vector of the axis, an eigenvector of position. By `D23` (`basis_state_saturates`) it
saturates the Robertson bound for `(T_d, P_d)` in every dimension `d`, so its Gram defect is `0`
even when `d ≥ 4`.

The fourth condition is that the state carries the defect: its Gram defect is positive.

## Main results

- `StateCarriesDefect d ψ` : `ψ` is a unit vector with positive Gram defect for `(T_d, P_d)`.
- `Massive d ℓ ψ` : the three necessary conditions and `StateCarriesDefect d ψ`.
- `basis_not_carrying_defect` : a basis vector never carries the defect, for any `d`.
- `massNecessary_not_sufficient` : for `4 ≤ d` and `0 < ℓ`, the three conditions hold and some
  unit state does not carry the defect.
- `massive_four_le` : a massive state has `4 ≤ d`.
- `massive_not_basis` : a massive state is not a basis vector.
-/

@[expose] public noncomputable section

open EigenvectorSaturation TransportPosition MassNecessary

namespace StateDefect

/-- The state carries the defect: it is a unit vector whose Gram defect for `(T_d, P_d)` is
positive. -/
def StateCarriesDefect (d : ℕ) (ψ : Hd d) : Prop :=
  ‖ψ‖ = 1 ∧ 0 < gramDefectAt (TdOp d) (PdOp d) ψ

/-- Massive: the three necessary conditions of `D56` and a state that carries the defect. -/
def Massive (d : ℕ) (ℓ : ℝ) (ψ : Hd d) : Prop :=
  MassNecessaryConditions d ℓ ∧ StateCarriesDefect d ψ

/-- The carrier, a basis vector of the axis, never carries the defect, in any dimension. -/
theorem basis_not_carrying_defect (d : ℕ) (j : Fin d) :
    ¬ StateCarriesDefect d (EuclideanSpace.single j (1 : ℂ)) := by
  rintro ⟨-, hpos⟩
  rw [(basis_state_saturates d j).2] at hpos
  exact lt_irrefl _ hpos

/-- The three conditions of `D56` are not sufficient for mass: for `4 ≤ d` they hold, and the
basis vector is a unit state that does not carry the defect. -/
theorem massNecessary_not_sufficient {d : ℕ} {ℓ : ℝ} (hd : 4 ≤ d) (hℓ : 0 < ℓ) :
    MassNecessaryConditions d ℓ ∧ ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ ¬ StateCarriesDefect d ψ := by
  refine ⟨(massNecessaryConditions_iff (by omega) hℓ).mpr hd, ?_⟩
  refine ⟨EuclideanSpace.single ⟨0, by omega⟩ (1 : ℂ), by simp, ?_⟩
  exact basis_not_carrying_defect d ⟨0, by omega⟩

/-- A massive state lives in `d ≥ 4`. -/
theorem massive_four_le {d : ℕ} {ℓ : ℝ} {ψ : Hd d} (hd : 2 ≤ d) (h : Massive d ℓ ψ) :
    4 ≤ d :=
  (one_lt_CoherenceConstant_iff hd).mp h.1.coherenceAboveOne

/-- A massive state is not a basis vector. -/
theorem massive_not_basis {d : ℕ} {ℓ : ℝ} (j : Fin d) :
    ¬ Massive d ℓ (EuclideanSpace.single j (1 : ℂ)) :=
  fun h => basis_not_carrying_defect d j h.2

end StateDefect

end

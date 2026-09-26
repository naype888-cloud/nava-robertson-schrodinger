/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
public import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant

/-!
# D25 — The dimensional quantum

Each `H_d` has its own quantum `dimQuantum d = δ(d) = C_Nava(d) − 1`, the obstruction of
Robertson's bound on `T_d : P_d`. It vanishes exactly at `d = 2, 3`, is positive from `d = 4`,
grows strictly with `d` from `dimQuantum 4`, stays below `δ_∞` and tends to it: `d = ∞` is a
limit of the family, not a dimension, and does not close the quantum. No units appear.

## Main results

- `DimensionalQuantum.dimQuantum_eq_zero_iff` : `δ(d) = 0 ↔ d = 2 ∨ d = 3`.
- `DimensionalQuantum.dimQuantum_certificate` : zero only at `d = 2, 3`, positive and
  increasing from `d = 4`, below and tending to `δ_∞ > 0`.
-/

@[expose] public noncomputable section

namespace DimensionalQuantum

open Gnomon Filter Topology

/-- The quantum of `H_d`. -/
def dimQuantum (d : ℕ) : ℝ := geometricGap d

/-- The quantum vanishes exactly at `d = 2, 3`. -/
theorem dimQuantum_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) : dimQuantum d = 0 ↔ d = 2 ∨ d = 3 := by
  rw [← CoherenceConstant_eq_one_iff d hd]
  unfold dimQuantum geometricGap
  constructor <;> intro h <;> linarith

/-- `d = 3` has no quantum. -/
theorem dimQuantum_three : dimQuantum 3 = 0 :=
  (dimQuantum_eq_zero_iff (by norm_num)).mpr (Or.inr rfl)

theorem dimQuantum_two : dimQuantum 2 = 0 :=
  (dimQuantum_eq_zero_iff (by norm_num)).mpr (Or.inl rfl)

/-- From `d = 4` the quantum is positive. -/
theorem dimQuantum_pos {d : ℕ} (hd : 4 ≤ d) : 0 < dimQuantum d :=
  geometricGap_pos_of_four_le d hd

/-- The quantum grows strictly with `d`. -/
theorem dimQuantum_strictMonoOn {d₀ d₁ : ℕ} (h₀ : 4 ≤ d₀) (h : d₀ < d₁) :
    dimQuantum d₀ < dimQuantum d₁ :=
  geometricGap_strictMonoOn_ge_four (show 4 ≤ d₀ from h₀) (show 4 ≤ d₁ by omega) h

/-- `δ(4)` is the minimum on `d ≥ 4`. -/
theorem dimQuantum_four_le {d : ℕ} (hd : 4 ≤ d) : dimQuantum 4 ≤ dimQuantum d :=
  geometricGap_four_le d hd

/-- No `d` reaches `δ_∞`. -/
theorem dimQuantum_lt_deltaInf {d : ℕ} (hd : 4 ≤ d) : dimQuantum d < deltaInf :=
  geometricGap_lt_deltaInf d hd

/-- The quantum tends to `δ_∞ > 0`. -/
theorem dimQuantum_tendsto : Tendsto dimQuantum atTop (𝓝 deltaInf) :=
  tendsto_geometricGap

/-- **The dimensional quantum.** Zero only at `d = 2, 3`, positive and increasing from `d = 4`,
below and tending to `δ_∞ > 0`. -/
theorem dimQuantum_certificate :
    dimQuantum 2 = 0 ∧ dimQuantum 3 = 0 ∧
    (∀ d, 4 ≤ d → 0 < dimQuantum d) ∧
    (∀ d, 4 ≤ d → dimQuantum 4 ≤ dimQuantum d) ∧
    (∀ d, 4 ≤ d → dimQuantum d < deltaInf) ∧
    0 < deltaInf ∧ Tendsto dimQuantum atTop (𝓝 deltaInf) :=
  ⟨dimQuantum_two, dimQuantum_three, fun _ => dimQuantum_pos, fun _ => dimQuantum_four_le,
    fun _ => dimQuantum_lt_deltaInf, deltaInf_pos, dimQuantum_tendsto⟩

end DimensionalQuantum

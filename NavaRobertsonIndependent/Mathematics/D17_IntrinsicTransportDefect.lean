/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D2_Robertson
public import NavaRobertsonIndependent.Mathematics.D7_Niven

/-!
# D17 — The intrinsic defect of a position–transport dynamics

A dynamics provides a Robertson–Schrödinger evaluation and identifies its saturation with the
spectral condition of `(T_d, P_d)`. From `d = 4` Niven forbids that equality, so the quadratic
defect is strictly positive. No observer appears in the definitions or hypotheses.

## Main results

- `IntrinsicDefect.intrinsicDefect_pos_iff` : the defect is positive iff no saturation.
- `IntrinsicDefect.PositionTransport.defect_pos` : for `d ≥ 4` the defect is positive.
-/

@[expose] public noncomputable section

namespace IntrinsicDefect

open Robertson1929

/-- The intrinsic defect `σ_A² σ_B² − (cov² + comm²)`. -/
def intrinsicDefect (S : SchrodingerEvaluation) : ℝ :=
  S.sigmaA ^ 2 * S.sigmaB ^ 2 -
    (S.covariance ^ 2 + S.commutator ^ 2)

/-- The intrinsic defect is nonnegative. -/
theorem intrinsicDefect_nonneg (S : SchrodingerEvaluation) :
    0 ≤ intrinsicDefect S := by
  unfold intrinsicDefect
  linarith [S.quadratic_bound]

/-- The defect vanishes iff the inequality saturates. -/
theorem intrinsicDefect_eq_zero_iff (S : SchrodingerEvaluation) :
    intrinsicDefect S = 0 ↔ SchrodingerSaturated S := by
  unfold intrinsicDefect SchrodingerSaturated
  constructor <;> intro h <;> linarith

/-- No saturation iff the defect is positive. -/
theorem intrinsicDefect_pos_iff (S : SchrodingerEvaluation) :
    0 < intrinsicDefect S ↔ ¬ SchrodingerSaturated S := by
  have hnonneg := intrinsicDefect_nonneg S
  rw [← intrinsicDefect_eq_zero_iff]
  constructor
  · exact ne_of_gt
  · intro hne
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- A dynamics realizing the spectral geometry of `(T_d, P_d)`: its saturation is the
saturation of the path. -/
structure PositionTransport (d : ℕ) where
  evaluation : SchrodingerEvaluation
  saturated_iff_path :
    SchrodingerSaturated evaluation ↔
      Real.cos (Real.pi / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4

/-- The defect of the dynamics. -/
def PositionTransport.defect {d : ℕ} (D : PositionTransport d) : ℝ :=
  intrinsicDefect D.evaluation

/-- For `d ≥ 4` no such dynamics saturates. -/
theorem PositionTransport.not_saturated {d : ℕ} (D : PositionTransport d)
    (hd : 4 ≤ d) : ¬ SchrodingerSaturated D.evaluation := by
  intro hsat
  exact Gnomon.not_saturated_of_four_le d hd
    (D.saturated_iff_path.mp hsat)

/-- **Intrinsic defect.** For `d ≥ 4` every such dynamics has positive defect. -/
theorem PositionTransport.defect_pos {d : ℕ} (D : PositionTransport d)
    (hd : 4 ≤ d) : 0 < D.defect := by
  exact (intrinsicDefect_pos_iff D.evaluation).2 (D.not_saturated hd)

/-- The positivity is uniform over all realizations in `d ≥ 4`. -/
theorem intrinsicDefect_pos_of_four_le :
    ∀ (d : ℕ), 4 ≤ d → ∀ D : PositionTransport d, 0 < D.defect := by
  intro d hd D
  exact D.defect_pos hd

end IntrinsicDefect

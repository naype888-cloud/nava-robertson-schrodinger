/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!
# D14 — The excess below the Szegő limit

The excess `C_∞ − C_Nava(d)` is positive, largest at `d = 4`, strictly decreasing and tends to
`0`: monotonicity (`D9`) and the Szegő limit (`D8`), read from the side of the remainder.

## Main results

- `Gnomon.gapExcess_pos`, `Gnomon.gapExcess_strictAnti`, `Gnomon.gapExcess_le_four`,
  `Gnomon.gapExcess_tendsto_zero`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Gnomon

/-- The excess `C_∞ − C_Nava(d)`. -/
noncomputable def gapExcess (d : ℕ) : ℝ := CoherenceConstantInf - CoherenceConstant d

/-- The excess is positive: `C_Nava(d)` never reaches `C_∞`. -/
theorem gapExcess_pos (d : ℕ) (hd : 4 ≤ d) : 0 < gapExcess d := by
  unfold gapExcess
  linarith [CoherenceConstant_lt_CoherenceConstantInf d hd]

/-- The excess is strictly decreasing. -/
theorem gapExcess_strictAnti {a b : ℕ} (ha : 4 ≤ a) (hb : 4 ≤ b) (hab : a < b) :
    gapExcess b < gapExcess a := by
  unfold gapExcess
  linarith [CoherenceConstant_strictMonoOn_ge_four ha hb hab]

/-- On `d ≥ 4` the excess is largest at `d = 4`. -/
theorem gapExcess_le_four (d : ℕ) (hd : 4 ≤ d) :
    gapExcess d ≤ gapExcess 4 := by
  unfold gapExcess
  linarith [CoherenceConstant_four_le d hd]

/-- The excess tends to `0`. -/
theorem gapExcess_tendsto_zero :
    Tendsto (fun d : ℕ => gapExcess d) atTop (𝓝 0) := by
  unfold gapExcess
  have h : Tendsto (fun d : ℕ => CoherenceConstantInf - CoherenceConstant d) atTop (𝓝
      (CoherenceConstantInf - CoherenceConstantInf)) :=
    tendsto_CoherenceConstant.const_sub CoherenceConstantInf
  simpa using h

end Gnomon

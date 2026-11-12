/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant

/-!
# D55 — The saturating region is `d ≤ 3`

On each axis `H_d = ℂ^d`, the Robertson bound for the pair `(T_d, P_d)` is reached with
equality exactly for `d ≤ 3`; from `d = 4` the defect is strictly positive. So the region
that saturates is not one dimension but all of `2 ≤ d ≤ 3`, and its complement is `4 ≤ d`.

On the cube, an axis coordinate `v` with `|v| ≤ 3` lies in the saturating region. The box
`[-3, 3]³` has `7³ = 343` sites.

Only `d ≥ 2` is treated: `defectGram` is defined through `T_d, P_d`, which do not commute
from `d = 2`.

## Main results

- `SaturatingRegion.defectGram_eq_zero_iff_le_three` : for `2 ≤ d`, defect `0 ↔ d ≤ 3`.
- `SaturatingRegion.defectGram_pos_iff_four_le` : for `2 ≤ d`, defect `> 0 ↔ 4 ≤ d`.
- `SaturatingRegion.defectGram_dichotomy` : for `2 ≤ d`, defect is `0` or `> 0`, never both.
- `SaturatingRegion.coordinate_saturates_iff` : for a coordinate `v` with `2 ≤ |v|`,
  `|v| ≤ 3` iff the defect at `|v|` is `0`.
- `SaturatingRegion.card_core` : `[-3, 3]³` has `343` sites.
-/

@[expose] public noncomputable section

open GramStep

namespace SaturatingRegion

/-- For `2 ≤ d`, the Gram defect is `0` exactly when `d ≤ 3`. -/
theorem defectGram_eq_zero_iff_le_three {d : ℕ} (hd : 2 ≤ d) :
    defectGram d = 0 ↔ d ≤ 3 := by
  rw [gramStep_gram_eq_zero_iff hd]
  omega

/-- For `2 ≤ d`, the Gram defect is positive exactly when `4 ≤ d`. -/
theorem defectGram_pos_iff_four_le {d : ℕ} (hd : 2 ≤ d) :
    0 < defectGram d ↔ 4 ≤ d := by
  refine ⟨fun h => ?_, gramStep_gram_pos⟩
  by_contra h4
  have h0 : defectGram d = 0 := (defectGram_eq_zero_iff_le_three hd).mpr (by omega)
  exact absurd h0 h.ne'

/-- For `2 ≤ d`, the Gram defect is either `0` or positive, and not both. -/
theorem defectGram_dichotomy {d : ℕ} (hd : 2 ≤ d) :
    (defectGram d = 0 ∧ d ≤ 3) ∨ (0 < defectGram d ∧ 4 ≤ d) := by
  by_cases h : d ≤ 3
  · exact Or.inl ⟨(defectGram_eq_zero_iff_le_three hd).mpr h, h⟩
  · exact Or.inr ⟨gramStep_gram_pos (by omega), by omega⟩

/-- A coordinate `v` with `2 ≤ |v|` lies in the saturating region exactly when `|v| ≤ 3`. -/
theorem coordinate_saturates_iff {v : ℤ} (hv : 2 ≤ v.natAbs) :
    defectGram v.natAbs = 0 ↔ |v| ≤ 3 := by
  rw [defectGram_eq_zero_iff_le_three hv, Int.abs_eq_natAbs]
  omega

/-- The box `[-3, 3]³` has `7³ = 343` sites. -/
theorem card_core :
    (Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3).card = 343 := by
  simp [Finset.card_product]

end SaturatingRegion

end

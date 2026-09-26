/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!
# D24 — The gap between `d = 4` and the Szegő limit

`C_Nava` is strictly increasing from `d = 4` (`D9`) and tends to `C_∞ = √(π²/3 − 2)` (`D8`).
The gap `Δ = C_∞ − C_Nava(4) = δ_∞ − δ(4)` depends only on `π`: it is positive, below `δ_∞`,
bounds the rise of the chain from `d = 4`, and is its limit.

## Main results

- `GapFourAsymptote.gapFourInf_pos_lt_deltaInf` : `0 < Δ < δ_∞`.
- `GapFourAsymptote.rise_lt_gapFourInf` : `δ(d) − δ(4) < Δ` for `d ≥ 4`.
- `GapFourAsymptote.rise_tendsto_gapFourInf` : `C_Nava(d) − C_Nava(4) → Δ`.
-/

@[expose] public noncomputable section

namespace GapFourAsymptote

open Gnomon Filter

/-- The gap `C_∞ − C_Nava(4)`. -/
def gapFourInf : ℝ := CoherenceConstantInf - CoherenceConstant 4

/-- `Δ = δ_∞ − δ(4)`. -/
theorem gapFourInf_eq_deltaInf_sub_geometricGap_four :
    gapFourInf = deltaInf - geometricGap 4 := by
  unfold gapFourInf deltaInf geometricGap
  ring

/-- `Δ > 0`. -/
theorem gapFourInf_pos : 0 < gapFourInf := by
  have h := CoherenceConstant_lt_CoherenceConstantInf 4 (le_refl 4)
  unfold gapFourInf
  linarith

/-- `Δ < δ_∞`, since `δ(4) > 0`. -/
theorem gapFourInf_lt_deltaInf : gapFourInf < deltaInf := by
  rw [gapFourInf_eq_deltaInf_sub_geometricGap_four]
  linarith [geometricGap_pos_of_four_le 4 (le_refl 4)]

/-- For `d ≥ 4`, `δ(d) − δ(4) < Δ`. -/
theorem rise_lt_gapFourInf (d : ℕ) (hd : 4 ≤ d) :
    geometricGap d - geometricGap 4 < gapFourInf := by
  have h := geometricGap_lt_deltaInf d hd
  rw [gapFourInf_eq_deltaInf_sub_geometricGap_four]
  linarith

/-- `C_Nava(d) − C_Nava(4) → Δ`. -/
theorem rise_tendsto_gapFourInf :
    Tendsto (fun d : ℕ => CoherenceConstant d - CoherenceConstant 4) atTop (nhds gapFourInf) := by
  unfold gapFourInf
  exact tendsto_CoherenceConstant.sub_const (CoherenceConstant 4)

/-- `0 < Δ < δ_∞`. -/
theorem gapFourInf_pos_lt_deltaInf :
    0 < gapFourInf ∧ gapFourInf < deltaInf :=
  ⟨gapFourInf_pos, gapFourInf_lt_deltaInf⟩

end GapFourAsymptote

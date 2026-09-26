/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D2_Robertson

/-!
# D7 — Niven: saturation only at `d ∈ {2, 3}`

Robertson–Schrödinger saturates on the fundamental mode of the path iff
`cos²(π/(d+1)) = (d−1)/4`. This holds iff `d = 2` or `d = 3`: `d = 4` by an explicit algebraic
contradiction, `d ≥ 5` by the cosine bound `ArithmeticChecks.R3_cos_sq_lt`.

## Main results

- `Gnomon.saturation_iff` : `cos²(π/(d+1)) = (d−1)/4 ↔ d = 2 ∨ d = 3`.
- `Gnomon.not_saturated_of_four_le` : no saturation for `d ≥ 4`.
-/

@[expose] public section

open Real

namespace Gnomon

/-- `d = 2` saturates: `cos²(π/3) = 1/4`. -/
theorem seed_d2 : Real.cos (π / 3) ^ 2 = 1 / 4 := by
  rw [Real.cos_pi_div_three]; norm_num

/-- `d = 3` saturates: `cos²(π/4) = 1/2`. -/
theorem seed_d3 : Real.cos (π / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four]
  rw [div_pow, sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_num

/-- `d = 4` does not saturate: `cos²(π/5) ≠ 3/4`. -/
theorem not_saturated_d4 : Real.cos (π / 5) ^ 2 ≠ 3 / 4 := by
  rw [Real.cos_pi_div_five]
  intro h
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs, hnn, h]

/-- **Niven.** For `d ≥ 2`, `cos²(π/(d+1)) = (d−1)/4 ↔ d ∈ {2, 3}`. -/
theorem saturation_iff (d : ℕ) (hd : 2 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨h2, h3⟩ := hne
    rcases Nat.lt_or_ge d 5 with h5 | h5
    · have hd4 : d = 4 := by omega
      subst hd4
      have hc : ((4 : ℕ) : ℝ) + 1 = 5 := by norm_num
      rw [hc] at h
      have h34 : (((4 : ℕ) : ℝ) - 1) / 4 = 3 / 4 := by norm_num
      rw [h34] at h
      exact not_saturated_d4 h
    · exact absurd h (ne_of_lt (ArithmeticChecks.R3_cos_sq_lt d h5))
  · rintro (rfl | rfl)
    · have hc : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
      rw [hc, seed_d2]; norm_num
    · have hc : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
      rw [hc, seed_d3]; norm_num

/-- For `d ≥ 4` saturation is impossible. -/
theorem not_saturated_of_four_le (d : ℕ) (hd : 4 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 := by
  intro h
  have hsem : d = 2 ∨ d = 3 := (saturation_iff d (by omega)).mp h
  omega

/-- The only saturating dimensions are `d = 2` and `d = 3`. -/
theorem niven_seeds (d : ℕ) (hd : 2 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 → d = 2 ∨ d = 3 :=
  (saturation_iff d hd).mp

theorem not_seed_of_four_le (d : ℕ) (hd : 4 ≤ d) :
    ¬ (d = 2 ∨ d = 3) := by
  omega

end Gnomon

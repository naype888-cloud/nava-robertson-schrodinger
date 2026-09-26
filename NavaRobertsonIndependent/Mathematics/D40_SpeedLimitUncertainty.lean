/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D38_GroupVelocity

/-!
# D40 — The speed limit excludes minimum uncertainty

A state at the speed limit of `D38`, `velocity d ψ = 1`, has maximal tension. For `d ≥ 4`
Robertson–Schrödinger is strict at every such state (`D21`), so no state moves at the speed
limit with minimum uncertainty, and every minimum-uncertainty state moves strictly slower.

## Main results

- `GroupVelocity.surplus_pos_of_velocity_eq_one` : at the speed limit the surplus is positive.
- `GroupVelocity.velocity_lt_one_of_surplus_eq_zero` : minimum-uncertainty states move at
  less than one site per unit of time.
-/

@[expose] public section

open TransportPosition NRSInequality NearMaxTension

namespace GroupVelocity

variable {d : ℕ}

/-- At the speed limit the tension is maximal. -/
theorem tension_eq_of_velocity_eq_one (hd : 2 ≤ d) {ψ : Hd d} (h : velocity d ψ = 1) :
    tension d ψ = 2 / ((d : ℝ) - 1) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [velocity] at h
  field_simp
  linarith

/-- **Speed limit and uncertainty.** For `d ≥ 4`, a unit state at the speed limit satisfies
Robertson–Schrödinger strictly. -/
theorem surplus_pos_of_velocity_eq_one (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (h : velocity d ψ = 1) : 0 < surplus d ψ := by
  have ht := tension_eq_of_velocity_eq_one (by omega) h
  have hs := strict_inequality_of_maxTension hd ψ hψ ht
  rw [commutatorConstant_half_sq (by omega)] at hs
  rw [surplus_eq, ht]
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have : (2 / ((d : ℝ) - 1)) ^ 2 / 4 = 1 / ((d : ℝ) - 1) ^ 2 := by field_simp; ring
  linarith

/-- For `d ≥ 4`, a minimum-uncertainty unit state moves strictly slower than the cone. -/
theorem velocity_lt_one_of_surplus_eq_zero (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (h0 : surplus d ψ = 0) : velocity d ψ < 1 :=
  lt_of_le_of_ne ((le_abs_self _).trans (abs_velocity_le (by omega) ψ hψ))
    fun h => (surplus_pos_of_velocity_eq_one hd ψ hψ h).ne' h0

end GroupVelocity

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D44_VelocityBand

/-!
# D44b — The band in one sentence

On `H_d`, `d ≥ 4`, speed has a ceiling and a free zone below it, and between the two a toll.

* **Ceiling.** No unit state moves faster than the cone speed `1` (`D38`), and the maximal current
  state reaches it.
* **Free zone.** Some minimum-uncertainty state moves exactly at `v*(d)`, strictly below the
  ceiling (`D44`).
* **Toll.** Every unit state with speed in `Ϙ(d) = (v*(d), 1]` carries a Robertson–Schrödinger
  surplus (`D44`). In particular the state that reaches the ceiling carries one, so the
  Mandelstam–Tamm and Cramér–Rao ratio there is below `1` (`D41`): the ceiling is never reached
  for free.

## Main results

- `BandSentence.band_sentence` : ceiling, free zone and toll in one statement.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality NearMaxTension EigenvectorSaturation GroupVelocity
  VelocityBand

namespace BandSentence

variable {d : ℕ}

/-- **The band in one sentence.** For `d ≥ 4`: no unit state is faster than `1`; some
minimum-uncertainty state moves exactly at `v*(d) < 1`; every unit state with speed in `Ϙ(d)`
carries a surplus; and the maximal current state moves at `1`, carries a surplus, and misses the
Mandelstam–Tamm and Cramér–Rao bound. -/
theorem band_sentence (hd : 4 ≤ d) :
    (∀ ψ : Hd d, ‖ψ‖ = 1 → |velocity d ψ| ≤ 1) ∧
    (∃ ψ : Hd d, ‖ψ‖ = 1 ∧ surplus d ψ = 0 ∧ |velocity d ψ| = threshold d) ∧
    threshold d < 1 ∧
    (∀ ψ : Hd d, ‖ψ‖ = 1 → |velocity d ψ| ∈ Ϙ d → 0 < surplus d ψ) ∧
    |velocity d (maxCurrentState d)| = 1 ∧
    0 < surplus d (maxCurrentState d) ∧
    mtRatio d (maxCurrentState d) < 1 := by
  have h2 : 2 ≤ d := by omega
  refine ⟨fun ψ hψ => abs_velocity_le h2 ψ hψ, exists_saturated_threshold (by omega),
    by linarith [koppa_pos hd, show ϙ d = 1 - threshold d from rfl],
    fun ψ hψ hv => surplus_pos_of_mem_band h2 ψ hψ hv, ?_, ?_, mtRatio_maxCurrentState_lt_one hd⟩
  · rw [velocity_maxCurrentState h2, abs_one]
  · refine lt_of_le_of_ne (gramDefectAt_nonneg _ _ _) fun h => ?_
    exact (surplus_maxCurrentState_eq_zero_iff h2).1 h.symm |>.elim (by omega) (by omega)

end BandSentence

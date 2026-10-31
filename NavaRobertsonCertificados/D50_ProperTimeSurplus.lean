/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D44_VelocityBand

/-!
# D50 — Proper time on one axis is the square root of the surplus

Nothing is added to `H_d`. The interval of the uncertainty vector is the Gram defect of the pair
`(T_d, P_d)`, which is the Robertson–Schrödinger `surplus`; its square root is the proper time.
Every bound below is a rename of a statement already proved.

* `τ² ≥ 0` is Robertson–Schrödinger (`gramDefectAt_nonneg`).
* `τ² > 0` on the band `Ϙ(d)` is `D44`.
* At the maximal current state `τ² = defectGram d`, positive from `d = 4` on and zero exactly at
  `d = 2, 3` (`D44`, `D20`).
* Near the maximal current state `τ²` stays within the band width (`D23d`).

## Main results

- `ProperTime.properTime_sq` : `τ² = surplus`.
- `ProperTime.properTime_pos_of_mem_band` : `0 < τ` for every unit state with speed in `Ϙ(d)`.
- `ProperTime.properTime_maxCurrentState_pos` : `0 < τ` at the maximal current state, `d ≥ 4`.
- `ProperTime.properTime_maxCurrentState_eq_zero_iff` : `τ = 0 ↔ d = 2 ∨ d = 3`.
- `ProperTime.properTime_band` : the distance of `τ²` to `defectGram d`, from `D23d`.
-/

@[expose] public noncomputable section

open Real TransportPosition NRSInequality NearMaxTension EigenvectorSaturation GramStep
open GroupVelocity BandWidth VelocityBand

namespace ProperTime

variable {d : ℕ}

/-- The proper time of a state on one axis: the square root of the Robertson–Schrödinger
surplus of `(T_d, P_d)`. -/
def properTime (d : ℕ) (ψ : Hd d) : ℝ := √(surplus d ψ)

theorem properTime_sq (ψ : Hd d) : properTime d ψ ^ 2 = surplus d ψ :=
  Real.sq_sqrt (gramDefectAt_nonneg _ _ _)

theorem properTime_nonneg (ψ : Hd d) : 0 ≤ properTime d ψ := Real.sqrt_nonneg _

/-- **Proper time is positive in the band.** -/
theorem properTime_pos_of_mem_band (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (hv : |velocity d ψ| ∈ Ϙ d) : 0 < properTime d ψ :=
  Real.sqrt_pos.mpr (surplus_pos_of_mem_band hd ψ hψ hv)

/-- At the maximal current state the proper time is the square root of the Gram defect. -/
theorem properTime_maxCurrentState (hd : 2 ≤ d) :
    properTime d (maxCurrentState d) = √(defectGram d) := by
  rw [properTime, surplus_maxCurrentState hd]

/-- **No proper time at the speed limit for `d = 2, 3`; some from `d = 4` on.** -/
theorem properTime_maxCurrentState_eq_zero_iff (hd : 2 ≤ d) :
    properTime d (maxCurrentState d) = 0 ↔ d = 2 ∨ d = 3 := by
  rw [← surplus_maxCurrentState_eq_zero_iff hd, properTime,
    Real.sqrt_eq_zero (gramDefectAt_nonneg _ _ _)]

theorem properTime_maxCurrentState_pos (hd : 4 ≤ d) : 0 < properTime d (maxCurrentState d) := by
  refine lt_of_le_of_ne (properTime_nonneg _) fun h => ?_
  have := (properTime_maxCurrentState_eq_zero_iff (by omega)).mp h.symm
  omega

/-- **The band of the proper time** (`D23d`): `τ²` is within the tension deficit of `defectGram`. -/
theorem properTime_band (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    gapK d * (properTime d ψ ^ 2 - defectGram d) ^ 2 ≤
      2048 * (2 / ((d : ℝ) - 1) - tension d ψ) := by
  rw [properTime_sq]
  exact surplus_band hd ψ hψ

end ProperTime

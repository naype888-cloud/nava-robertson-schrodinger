/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
public import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
public import NavaRobertsonIndependent.Mathematics.D37f_LightCone

/-!
# D56 — Necessary conditions for mass: `c`, `ℓ`, `C_N > 1`

Mass needs three things at once.

* `c`, the ruler: transport moves at most one position per step
  (`LightCone.lightCone`) and exactly one is reached (`LightCone.lightCone_edge_ne_zero`).
* `ℓ`, a fixed positive step size. It is a parameter here, `0 < ℓ`, and it is not tied to
  the physical Planck step in this file.
* `C_N > 1`: the coherence limit of `d` lies strictly above the saturated value `1`.

These are **necessary, not sufficient**: the photon satisfies all three and has no mass,
because it is the carrier and not the state. This file proves the necessary direction and
what it forces on `d`: nothing below `d = 4` has mass. Sufficiency is left open.

## Main results

- `MassNecessary.MassNecessaryConditions` : the three conditions at dimension `d`, step `ℓ`.
- `MassNecessary.one_lt_CoherenceConstant_iff` : for `2 ≤ d`, `1 < C_N(d) ↔ 4 ≤ d`.
- `MassNecessary.massNecessaryConditions_iff` : for `2 ≤ d` and `0 < ℓ`, the three
  conditions hold iff `4 ≤ d`.
- `MassNecessary.defectGram_eq_zero_of_not_massNecessary` : if they fail, the defect is `0`.
- `MassNecessary.massSq_band_of_massNecessary` : under the three conditions,
  `0 < massSq 4 ≤ massSq d < π²/3 − 3`, where `massSq d = C_N(d)² − 1`.
  The expression is written out and agrees with `massSq` of the fibre-surgery repository.
- `MassNecessary.defectGram_eq_massSq_of_massNecessary` : the defect of the fibre is the mass
  gap: `defectGram d = massSq d / (d − 1)² > 0`.
-/

@[expose] public noncomputable section

open Gnomon GramStep TransportPosition LightCone

namespace MassNecessary

/-- The three necessary conditions for mass at dimension `d` and step size `ℓ`: transport is
bounded by one position per step and attains it, the step is positive, and the coherence limit
exceeds one. -/
structure MassNecessaryConditions (d : ℕ) (ℓ : ℝ) : Prop where
  speedLimit : ∀ (k : ℕ) (i j : Fin d), k < distPath i j → (Td d ^ k) i j = 0
  speedAttained : ∀ (k : ℕ) (i j : Fin d), j.val = i.val + k → (Td d ^ k) i j ≠ 0
  stepPositive : 0 < ℓ
  coherenceAboveOne : 1 < CoherenceConstant d

/-- For `2 ≤ d`, `C_N(d) > 1` exactly from `d = 4`. -/
theorem one_lt_CoherenceConstant_iff {d : ℕ} (hd : 2 ≤ d) :
    1 < CoherenceConstant d ↔ 4 ≤ d := by
  constructor
  · intro h
    by_contra h4
    have hle : d = 2 ∨ d = 3 := by omega
    exact absurd ((CoherenceConstant_eq_one_iff d hd).mpr hle) h.ne'
  · intro h4
    have hsq := one_lt_CoherenceConstantSq d h4
    rw [CoherenceConstant]
    exact (Real.lt_sqrt (by norm_num)).mpr (by linarith)

/-- For `2 ≤ d` and a positive step, the three conditions hold exactly when `4 ≤ d`. -/
theorem massNecessaryConditions_iff {d : ℕ} {ℓ : ℝ} (hd : 2 ≤ d) (hℓ : 0 < ℓ) :
    MassNecessaryConditions d ℓ ↔ 4 ≤ d := by
  constructor
  · intro h
    exact (one_lt_CoherenceConstant_iff hd).mp h.coherenceAboveOne
  · intro h4
    exact ⟨fun k i j hk => lightCone k i j hk,
      fun k i j hij => lightCone_edge_ne_zero hd k i j hij, hℓ,
      (one_lt_CoherenceConstant_iff hd).mpr h4⟩

/-- If the three conditions fail at a positive step, the Gram defect vanishes: no mass. -/
theorem defectGram_eq_zero_of_not_massNecessary {d : ℕ} {ℓ : ℝ} (hd : 2 ≤ d) (hℓ : 0 < ℓ)
    (h : ¬ MassNecessaryConditions d ℓ) : defectGram d = 0 := by
  rw [gramStep_gram_eq_zero_iff hd]
  have h4 : ¬ 4 ≤ d := fun h4 => h ((massNecessaryConditions_iff hd hℓ).mpr h4)
  omega

/-- **The squared mass band.** Under the three necessary conditions, `d ≥ 4` and
`massSq d = C_N(d)² − 1` satisfies `0 < massSq 4 ≤ massSq d < π²/3 − 3`. -/
theorem massSq_band_of_massNecessary {d : ℕ} {ℓ : ℝ} (hd : 2 ≤ d)
    (h : MassNecessaryConditions d ℓ) :
    0 < CoherenceConstantSq 4 - 1 ∧ CoherenceConstantSq 4 - 1 ≤ CoherenceConstantSq d - 1 ∧
      CoherenceConstantSq d - 1 < Real.pi ^ 2 / 3 - 3 := by
  have h4 : 4 ≤ d := (one_lt_CoherenceConstant_iff hd).mp h.coherenceAboveOne
  refine ⟨by linarith [one_lt_CoherenceConstantSq 4 le_rfl], ?_, ?_⟩
  · have := CoherenceConstantSq_strictMonoOn_ge_four.monotoneOn (by simp) (by simpa using h4) h4
    linarith
  · have h1 := CoherenceConstant_lt_CoherenceConstantInf d h4
    have h0 : 0 ≤ CoherenceConstant d := Real.sqrt_nonneg _
    have h2 : CoherenceConstant d ^ 2 < CoherenceConstantInf ^ 2 := by nlinarith
    have h3 : CoherenceConstantInf ^ 2 = Real.pi ^ 2 / 3 - 2 := by
      unfold CoherenceConstantInf
      rw [Real.sq_sqrt]
      nlinarith [Real.pi_gt_three]
    have hsq : CoherenceConstantSq d = CoherenceConstant d ^ 2 := by
      unfold CoherenceConstant
      rw [Real.sq_sqrt]
      linarith [one_lt_CoherenceConstantSq d h4]
    rw [hsq]
    linarith

/-- **One defect.** Under the three necessary conditions the Gram defect of the fibre is
positive and equals `massSq d / (d − 1)²`, with `massSq d = C_N(d)² − 1`: the defect of the
fibre and the mass gap of `d ≥ 4` are the same quantity. -/
theorem defectGram_eq_massSq_of_massNecessary {d : ℕ} {ℓ : ℝ} (hd : 2 ≤ d)
    (h : MassNecessaryConditions d ℓ) :
    0 < defectGram d ∧ defectGram d = (CoherenceConstantSq d - 1) / ((d : ℝ) - 1) ^ 2 := by
  have h4 : 4 ≤ d := (one_lt_CoherenceConstant_iff hd).mp h.coherenceAboveOne
  exact ⟨gramStep_gram_pos h4, gramStep_gram hd⟩

end MassNecessary

end

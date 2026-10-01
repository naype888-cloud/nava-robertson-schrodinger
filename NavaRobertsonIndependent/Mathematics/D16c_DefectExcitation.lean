/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16b_GaussBonnetBridge
public import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum

/-!
# D16c — The elementary excitation of the transported defect

`D16` puts a quantum on each of the `2g` cycles of `Σ_g`; `D16b` turns the defect into total
curvature. The elementary excitation is the step `g → g + 1`, which adds two cycles.

* With quantum `q` per cycle, the defect rises by `2q` and the total curvature falls by `4π`
  (`defectWith_step`, `curvature_step`). The curvature quantum is topological and the same for
  every `q`; the defect quantum is algebraic. For `q ≠ 0` the defect fixes the curvature with
  coupling `2π/q` (`totalCurvature_of_defectWith`), which is `D16b` at `q = δ_∞`.
* Defects are discrete: two genera differ by at least one step `2q` (`defectWith_gap`).
* At dimension `d` the quantum is `δ(d)` (`D25`). The step `2δ(d)` vanishes exactly at
  `d = 2, 3` (`dimStep_eq_zero_iff`): there the defect is `0` on every surface while the
  curvature still jumps (`blind_at_saturation`). From `d = 4` the step is positive, below
  `2δ_∞` (`dimStep_pos_lt`), and the defect determines the curvature.

Not here: propagation of the excitation inside the cone of `D37f`/`D37g`, its spin and its
mass. By `D28`/`D28b` the path carries no local curvature, so the excitation is a change of
`b₁`, global, not a site state. `HGaussBonnet` stays a declared hypothesis.

## Main results

- `DefectExcitation.defectWith_step`, `DefectExcitation.curvature_step` : the two quanta.
- `DefectExcitation.totalCurvature_of_defectWith` : curvature from the defect, `q ≠ 0`.
- `DefectExcitation.defectWith_gap` : no excitation below one step.
- `DefectExcitation.blind_at_saturation`, `DefectExcitation.dimStep_pos_lt` : `d = 2, 3`
  against `d ≥ 4`.
-/

@[expose] public noncomputable section

open Real Gnomon DimensionalQuantum

namespace DefectExcitation

/-- The defect of `Σ_g` with quantum `q` on each of its `2g` cycles. -/
def defectWith (q : ℝ) (g : ℕ) : ℝ :=
  cycleDefectSum (2 * g) fun _ => q

theorem defectWith_eq (q : ℝ) (g : ℕ) : defectWith q g = 2 * g * q := by
  rw [defectWith, cycleDefectSum_of_constant _ _ q fun _ => rfl]
  push_cast
  ring

/-- `D16` is the case `q = δ_∞`. -/
theorem defectWith_deltaInf (g : ℕ) : defectWith deltaInf g = closedSurfaceDefect g := rfl

/-- One step adds `2q` to the defect. -/
theorem defectWith_step (q : ℝ) (g : ℕ) : defectWith q (g + 1) - defectWith q g = 2 * q := by
  rw [defectWith_eq, defectWith_eq]
  push_cast
  ring

/-- Two different genera differ by at least one step. -/
theorem defectWith_gap {q : ℝ} (hq : 0 ≤ q) {g₁ g₂ : ℕ} (h : g₁ ≠ g₂) :
    2 * q ≤ |defectWith q g₁ - defectWith q g₂| := by
  rw [defectWith_eq, defectWith_eq, show 2 * (g₁ : ℝ) * q - 2 * g₂ * q =
    2 * q * ((g₁ : ℝ) - g₂) by ring, abs_mul, abs_of_nonneg (by linarith)]
  have hz : (1 : ℤ) ≤ |(g₁ : ℤ) - g₂| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast h))
  have h1 : (1 : ℝ) ≤ |(g₁ : ℝ) - g₂| := by exact_mod_cast hz
  nlinarith

namespace HGaussBonnet

variable (H : Gnomon.HGaussBonnet)

/-- One step lowers the total curvature by `4π`, whatever the quantum. -/
theorem curvature_step (g : ℕ) : H.totalCurvature (g + 1) - H.totalCurvature g = -(4 * π) := by
  rw [H.gauss_bonnet, H.gauss_bonnet, eulerChar_eq, eulerChar_eq]
  push_cast
  ring

/-- With `R = 2K`, one step lowers `∫R dA` by `8π`. -/
theorem scalar_step (g : ℕ) : H.scalarIntegral (g + 1) - H.scalarIntegral g = -(8 * π) := by
  unfold Gnomon.HGaussBonnet.scalarIntegral
  linarith [curvature_step H g]

/-- For `q ≠ 0` the defect fixes the curvature, with coupling `2π/q`. -/
theorem totalCurvature_of_defectWith {q : ℝ} (hq : q ≠ 0) (g : ℕ) :
    H.totalCurvature g = 4 * π - (2 * π / q) * defectWith q g := by
  rw [H.gauss_bonnet, eulerChar_eq, defectWith_eq]
  field_simp
  ring

/-- At `d = 2, 3` the defect is `0` on every surface, but the curvature still jumps. -/
theorem blind_at_saturation {d : ℕ} (hd : d = 2 ∨ d = 3) :
    (∀ g, defectWith (dimQuantum d) g = 0) ∧ H.totalCurvature 1 ≠ H.totalCurvature 0 := by
  have h0 : dimQuantum d = 0 := (dimQuantum_eq_zero_iff (by omega)).mpr hd
  refine ⟨fun g => by rw [defectWith_eq, h0, mul_zero], fun h => ?_⟩
  have := curvature_step H 0
  simp only [zero_add] at this
  linarith [pi_pos]

end HGaussBonnet

/-- The step at dimension `d` vanishes exactly at `d = 2, 3`. -/
theorem dimStep_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) : 2 * dimQuantum d = 0 ↔ d = 2 ∨ d = 3 := by
  rw [← dimQuantum_eq_zero_iff hd]
  constructor <;> intro h <;> linarith

/-- From `d = 4` the step is positive and below the asymptotic step `2δ_∞`. -/
theorem dimStep_pos_lt {d : ℕ} (hd : 4 ≤ d) :
    0 < 2 * dimQuantum d ∧ 2 * dimQuantum d < 2 * deltaInf :=
  ⟨by linarith [dimQuantum_pos hd], by linarith [dimQuantum_lt_deltaInf hd]⟩

end DefectExcitation

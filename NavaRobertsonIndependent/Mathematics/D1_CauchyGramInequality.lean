/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Complex.Norm

/-!
# D1 — Cauchy–Schwarz as a Gram defect

For two vectors `x`, `y` of a complex inner product space the Gram determinant
`gramDefectC x y = ‖x‖² ‖y‖² − |⟪x, y⟫|²` is nonnegative: this is Cauchy–Schwarz. Written in
the real and imaginary parts of `⟪x, y⟫` it is the Robertson–Schrödinger inequality (`D2`).

## Main results

- `gramDefectC_nonneg` : the Gram defect is nonnegative.
- `robertsonSchrodinger_from_gram` : Robertson–Schrödinger in real and imaginary coordinates.
- `robertsonSchrodinger_saturated_iff_gram_zero` : saturation iff the Gram defect vanishes.
-/

@[expose] public noncomputable section

namespace CauchyGram

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The squared norm of a fluctuation vector. -/
def varianceC (x : H) : ℝ := ‖x‖ ^ 2

/-- The Gram determinant of two vectors. -/
def gramDefectC (x y : H) : ℝ :=
  varianceC x * varianceC y - ‖@inner ℂ H _ x y‖ ^ 2

/-- **Cauchy–Schwarz as a Gram defect.** The Gram determinant is nonnegative. -/
theorem gramDefectC_nonneg (x y : H) : 0 ≤ gramDefectC x y := by
  have hxy : ‖@inner ℂ H _ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hleft : 0 ≤ ‖x‖ * ‖y‖ - ‖@inner ℂ H _ x y‖ := sub_nonneg.mpr hxy
  have hright : 0 ≤ ‖x‖ * ‖y‖ + ‖@inner ℂ H _ x y‖ :=
    add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  calc
    0 ≤ (‖x‖ * ‖y‖ - ‖@inner ℂ H _ x y‖) *
        (‖x‖ * ‖y‖ + ‖@inner ℂ H _ x y‖) := mul_nonneg hleft hright
    _ = gramDefectC x y := by simp [gramDefectC, varianceC, pow_two]; ring

/-- Cauchy–Schwarz is saturated iff the Gram defect vanishes. -/
theorem gramDefectC_eq_zero_iff (x y : H) :
    gramDefectC x y = 0 ↔ ‖@inner ℂ H _ x y‖ = ‖x‖ * ‖y‖ := by
  have hxy : ‖@inner ℂ H _ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hi : 0 ≤ ‖@inner ℂ H _ x y‖ := norm_nonneg _
  have hp : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  constructor
  · intro hzero
    simp only [gramDefectC, varianceC, pow_two] at hzero
    nlinarith
  · intro heq
    unfold gramDefectC varianceC
    rw [heq]
    ring

/-- The real part of the inner product of two fluctuation vectors. -/
def covarianceC (x y : H) : ℝ := (@inner ℂ H _ x y).re

/-- The imaginary part of the inner product; for operator fluctuations it is the commutator
term. -/
def commutatorCoordinateC (x y : H) : ℝ := 2 * (@inner ℂ H _ x y).im

/-- Robertson–Schrödinger is the positivity of the Gram defect in real and imaginary
coordinates. -/
theorem robertsonSchrodinger_from_gram (x y : H) :
    covarianceC x y ^ 2 + (commutatorCoordinateC x y / 2) ^ 2 ≤
      varianceC x * varianceC y := by
  have hgram := gramDefectC_nonneg x y
  have hnorm :
      ‖@inner ℂ H _ x y‖ ^ 2 =
        (@inner ℂ H _ x y).re ^ 2 + (@inner ℂ H _ x y).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hbase : ‖@inner ℂ H _ x y‖ ^ 2 ≤ varianceC x * varianceC y :=
    sub_nonneg.mp hgram
  rw [hnorm] at hbase
  simpa [covarianceC, commutatorCoordinateC] using hbase

/-- Abstract Robertson–Schrödinger saturation. -/
def RSSaturated (x y : H) : Prop :=
  covarianceC x y ^ 2 + (commutatorCoordinateC x y / 2) ^ 2 =
    varianceC x * varianceC y

/-- Robertson–Schrödinger is saturated iff the Gram defect vanishes. -/
theorem robertsonSchrodinger_saturated_iff_gram_zero (x y : H) :
    RSSaturated x y ↔ gramDefectC x y = 0 := by
  have hnorm :
      ‖@inner ℂ H _ x y‖ ^ 2 =
        (@inner ℂ H _ x y).re ^ 2 + (@inner ℂ H _ x y).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [RSSaturated, covarianceC, commutatorCoordinateC, gramDefectC]
  rw [show (2 * (@inner ℂ H _ x y).im / 2) ^ 2 =
      (@inner ℂ H _ x y).im ^ 2 by ring]
  rw [← hnorm]
  constructor <;> intro h <;> nlinarith

end CauchyGram

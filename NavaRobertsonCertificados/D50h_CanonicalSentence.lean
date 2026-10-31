/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50g_WordDefect
public import NavaRobertsonCertificados.D49k_RobertsonDeterminantCanonicalAxes

/-!
# D50h — Words that do not commute: each along its vertex, and time comes out

Two words `A`, `B` that do not commute do not go on a diagonal: each goes along its own axis with
its own orthogonal `P_d`, because that is the first step the algebra allows (`D4`). These are the
canonical axes of `D49k`: the fluctuation vectors of different axes are orthogonal, and `Σ` is block
diagonal, one `2 × 2` block per word, with no product structure of the state assumed.

Time comes out of exactly these blocks: the block of the word `i` carries
`τ_i² = g_i`, the Gram surplus of its pair `(T_i, P_i)` (`D50c`), and `det Σ / |det Ω|` is the
product of the blocks. Commuting words on a diagonal are the other case (`D50g`).

## Main results

- `CanonicalSentence.defect_eq_cubeDefect` : the `g_i` of `D49k` is the `τ_i²` of `D50c`.
- `CanonicalSentence.log_ratio_canonical` : `log (det Σ / |det Ω|) = Σ_i log (1 + g_i/ω_i²)`: the
  sentence adds the words.
- `CanonicalSentence.ratio_ge_one_add_sum` : `det Σ / |det Ω| ≥ 1 + Σ_i g_i/ω_i²`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS CauchyGram RobertsonDeterminant RobertsonDeterminant3D
  AxisDefectEntangled DeterminantEqualityRelation CanonicalAxes WordDefect ProperTimeAxis

namespace CanonicalSentence

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- **The defect of a word of `D49k` is the squared proper time of its axis.** -/
theorem defect_eq_cubeDefect (Φ : H3D dx dy dz) (i : Fin 3) :
    defect Φ i = cubeDefect dx dy dz Φ i := by
  fin_cases i <;>
    simp [defect, fluct, pairs, cubeDefect, properTimeAxis_sq]

/-- **The defect of a sentence on canonical axes is the sum of the defects of its words**, in the
`D50g` sense, for the three axes. -/
theorem wordDefect_bodyDiagonal (Φ : H3D dx dy dz) :
    wordDefect (cubeDefect dx dy dz Φ) [0, 1, 2] = ∑ i, defect Φ i := by
  simp [Fin.sum_univ_three, defect_eq_cubeDefect, add_assoc]

variable (horth : ∀ s t (i j : Fin 3), i ≠ j → inner ℂ (fluct Φ (s, i)) (fluct Φ (t, j)) = 0)
include horth

/-- **The blocks add their times**: on canonical axes the logarithm of `det Σ / |det Ω|` is the
sum over the words of `log (1 + g_i/ω_i²)`. -/
theorem log_ratio_canonical (h0 : omega Φ 0 ≠ 0) (h1 : omega Φ 1 ≠ 0) (h2 : omega Φ 2 ≠ 0) :
    Real.log ((covMatrix (pairs dx dy dz) Φ).det / |(imMatrix (pairs dx dy dz) Φ).det|) =
      ∑ i, Real.log (1 + defect Φ i / omega Φ i ^ 2) := by
  have hΩ : |(imMatrix (pairs dx dy dz) Φ).det| ≠ 0 := by
    rw [abs_det_imMatrix_pairs]; positivity
  have g : ∀ i, 0 ≤ defect Φ i := fun i => gramDefectC_nonneg _ _
  have pos : ∀ i, 0 < 1 + defect Φ i / omega Φ i ^ 2 := fun i => by
    have := g i; positivity
  rw [det_ratio_canonical horth h0 h1 h2, mul_div_assoc, div_self hΩ, mul_one,
    Real.log_mul (mul_pos (pos 0) (pos 1)).ne' (pos 2).ne',
    Real.log_mul (pos 0).ne' (pos 1).ne', Fin.sum_univ_three]

/-- **First order**: the excess of the sentence is at least the sum of the excesses of its words. -/
theorem ratio_ge_one_add_sum (h0 : omega Φ 0 ≠ 0) (h1 : omega Φ 1 ≠ 0) (h2 : omega Φ 2 ≠ 0) :
    1 + ∑ i, defect Φ i / omega Φ i ^ 2 ≤
      (covMatrix (pairs dx dy dz) Φ).det / |(imMatrix (pairs dx dy dz) Φ).det| := by
  have hΩ : |(imMatrix (pairs dx dy dz) Φ).det| ≠ 0 := by
    rw [abs_det_imMatrix_pairs]; positivity
  have x : ∀ i, 0 ≤ defect Φ i / omega Φ i ^ 2 := fun i =>
    div_nonneg (gramDefectC_nonneg _ _) (sq_nonneg _)
  rw [det_ratio_canonical horth h0 h1 h2, mul_div_assoc, div_self hΩ, mul_one, Fin.sum_univ_three]
  have a := x 0
  have b := x 1
  have c := x 2
  nlinarith [mul_nonneg a b, mul_nonneg a c, mul_nonneg b c, mul_nonneg (mul_nonneg a b) c]

end CanonicalSentence

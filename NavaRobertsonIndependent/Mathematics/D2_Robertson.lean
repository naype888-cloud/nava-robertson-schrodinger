/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D1_CauchyGramInequality
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.IntervalCases

/-!
# D2 — The Robertson inequality (1929)

Robertson's inequality for two observables at a unit state, in its linear form (`Evaluation`,
`|⟨[A, B]⟩|/2 ≤ σ_A σ_B`) and in the quadratic Robertson–Schrödinger form
(`SchrodingerEvaluation`, with covariance). The quadratic bound is not assumed: every pair of
vectors of a complex inner product space gives a `SchrodingerEvaluation` whose bound is the
Gram defect of `D1` (`CauchyGram.schrodingerEvaluationOfGram`).

## Main results

- `Robertson1929.schrodingerFloor_le_mul` : the Robertson–Schrödinger floor is at most
  `σ_A σ_B`.
- `CauchyGram.schrodingerEvaluationOfGram` : Cauchy–Schwarz gives Robertson–Schrödinger.
- `ArithmeticChecks` : five arithmetic lemmas used for the cosine bound and for Niven (`D7`).
-/

@[expose] public section

namespace Robertson1929

universe u

/-- Robertson's inequality evaluated at a unit state: deviations `sigmaA`, `sigmaB` and
`commutatorMean = ⟪ψ, [A, B] ψ⟫`. -/
structure Evaluation (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  state : H
  norm_state : ‖state‖ = 1
  sigmaA : ℝ
  sigmaB : ℝ
  commutatorMean : ℂ
  sigmaA_nonneg : 0 ≤ sigmaA
  sigmaB_nonneg : 0 ≤ sigmaB
  commutator_le : ‖commutatorMean‖ / 2 ≤ sigmaA * sigmaB

/-- Saturation of Robertson's bound. -/
def Saturated {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : Evaluation H) : Prop :=
  R.sigmaA * R.sigmaB = ‖R.commutatorMean‖ / 2

/-- An evaluation at maximal tension: the state attains the norm of the commutator. -/
structure MaxTension (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] extends Evaluation H where
  commutatorNorm : ℝ
  commutatorNorm_nonneg : 0 ≤ commutatorNorm
  attains_norm :
    ‖toEvaluation.commutatorMean‖ = commutatorNorm

/-- At maximal tension Robertson's bound is the norm of the commutator. -/
theorem MaxTension.bound_of_norm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : MaxTension H) :
    R.commutatorNorm / 2 ≤ R.sigmaA * R.sigmaB := by
  rw [← R.attains_norm]
  exact R.commutator_le

/-! ## Robertson–Schrödinger: the quadratic form -/

/-- The Robertson–Schrödinger evaluation: covariance and commutator squared are bounded by the
product of the variances. -/
structure SchrodingerEvaluation where
  sigmaA : ℝ
  sigmaB : ℝ
  covariance : ℝ
  commutator : ℝ
  sigmaA_nonneg : 0 ≤ sigmaA
  sigmaB_nonneg : 0 ≤ sigmaB
  quadratic_bound : covariance ^ 2 + commutator ^ 2 ≤ sigmaA ^ 2 * sigmaB ^ 2

/-- The Robertson–Schrödinger floor `√(cov² + comm²)`. -/
noncomputable def schrodingerFloor (S : SchrodingerEvaluation) : ℝ :=
  Real.sqrt (S.covariance ^ 2 + S.commutator ^ 2)

/-- Robertson–Schrödinger saturation. -/
def SchrodingerSaturated (S : SchrodingerEvaluation) : Prop :=
  S.sigmaA ^ 2 * S.sigmaB ^ 2 = S.covariance ^ 2 + S.commutator ^ 2

theorem schrodingerSaturated_iff (S : SchrodingerEvaluation) :
    SchrodingerSaturated S ↔
      S.sigmaA ^ 2 * S.sigmaB ^ 2 =
        S.covariance ^ 2 + S.commutator ^ 2 := by
  rfl

/-- The floor is positive iff the covariance or the commutator term is nonzero. -/
theorem schrodingerFloor_pos_iff (S : SchrodingerEvaluation) :
    0 < schrodingerFloor S ↔ S.covariance ≠ 0 ∨ S.commutator ≠ 0 := by
  rw [schrodingerFloor, Real.sqrt_pos]
  constructor
  · intro h
    by_contra hz
    push Not at hz
    simp [hz.1, hz.2] at h
  · rintro (hcov | hcomm)
    · nlinarith [sq_pos_of_ne_zero hcov, sq_nonneg S.commutator]
    · nlinarith [sq_nonneg S.covariance, sq_pos_of_ne_zero hcomm]

/-- The quadratic bound gives the linear bound on `σ_A σ_B`. -/
theorem schrodingerFloor_le_mul (S : SchrodingerEvaluation) :
    schrodingerFloor S ≤ S.sigmaA * S.sigmaB := by
  have hsum : 0 ≤ S.covariance ^ 2 + S.commutator ^ 2 := by positivity
  have hprod_nonneg : 0 ≤ S.sigmaA * S.sigmaB :=
    mul_nonneg S.sigmaA_nonneg S.sigmaB_nonneg
  have hsqrt_sq :
      schrodingerFloor S ^ 2 = S.covariance ^ 2 + S.commutator ^ 2 := by
    simpa [schrodingerFloor] using Real.sq_sqrt hsum
  have hprod_sq :
      S.sigmaA ^ 2 * S.sigmaB ^ 2 = (S.sigmaA * S.sigmaB) ^ 2 := by
    ring
  have hcota := S.quadratic_bound
  rw [hprod_sq] at hcota
  nlinarith

/-- The linear bound holds, and its negation does not. -/
theorem schrodinger_anchor (S : SchrodingerEvaluation) :
    schrodingerFloor S ≤ S.sigmaA * S.sigmaB ∧
    ¬ (schrodingerFloor S ≤ S.sigmaA * S.sigmaB ∧
      ¬ schrodingerFloor S ≤ S.sigmaA * S.sigmaB) := by
  refine ⟨schrodingerFloor_le_mul S, ?_⟩
  intro h
  exact h.2 h.1

end Robertson1929

/-! ## Five arithmetic lemmas

Used by Niven (`D7`): `R3` bounds the cosine for `d ≥ 5`; `R5` says that a strictly positive
bound `c ≤ α β` forbids either factor to vanish. -/

open Real Finset

namespace ArithmeticChecks

/-- The telescoping term, exact in `ℚ`. -/
theorem R1b_term (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) / k ^ 2 - 1 / (k * (k + 1)) = 1 / (k ^ 2 * (k + 1)) := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- `Σ_{k=2..N} 1/(k(k+1)) = 1/2 − 1/(N+1)`. -/
theorem R1a_telescope (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, (1 : ℚ) / (k * (k + 1)) = 1 / 2 - 1 / (N + 1) := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · simp
        norm_num
    · rw [Finset.sum_Icc_succ_top (by omega), ih h]
      have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
      have hn2 : ((n : ℚ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem R1d_term_pos (k : ℕ) (hk : 2 ≤ k) :
    (0 : ℚ) < 1 / (k ^ 2 * (k + 1)) := by
  have : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  positivity

/-- `(3 + √5)/8 ≠ 3/4`, since otherwise `5 = 9`. -/
theorem R2_five_ne_nine : (3 + Real.sqrt 5) / 8 ≠ 3 / 4 := by
  intro h
  have h3 : Real.sqrt 5 = 3 := by linarith
  have h5 : (5 : ℝ) = 9 := by
    have := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
    rw [h3] at this
    linarith [this]
  norm_num at h5

/-- For `d ≥ 5`, `cos²(π/(d+1)) < (d−1)/4`. -/
theorem R3_cos_sq_lt (d : ℕ) (hd : 5 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 < (d - 1 : ℝ) / 4 := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hx_pos : 0 < π / ((d : ℝ) + 1) := by positivity
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hcos_lt : Real.cos (π / (d + 1)) < 1 := by
    have hy : π / ((d : ℝ) + 1) ≤ π := by
      rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hy hx_pos
    simpa using h
  have hcos_nonneg : 0 ≤ Real.cos (π / ((d : ℝ) + 1)) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos]
    · rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
  have hcos_le : Real.cos (π / (d + 1)) ^ 2 < 1 := by
    nlinarith [hcos_nonneg, hcos_lt]
  have hfloor : (1 : ℝ) ≤ ((d : ℝ) - 1) / 4 := by
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  linarith

theorem R4a_seven_terms :
    (3 : ℚ) / 2 < ∑ k ∈ Finset.range 7, (1 : ℚ) / (k + 1) ^ 2 := by
  norm_num [Finset.sum_range_succ]

theorem R4_three_lt_pi : (3 : ℝ) < π := Real.pi_gt_three

/-- If `0 < c ≤ α β`, neither factor vanishes. -/
theorem R5_factors_ne_zero (var_A var_B cota_robertson : ℝ)
    (h_robertson : cota_robertson ≤ var_A * var_B)
    (h_cota_positiva : 0 < cota_robertson) :
    var_A ≠ 0 ∧ var_B ≠ 0 := by
  constructor
  · intro hA
    rw [hA, zero_mul] at h_robertson
    linarith
  · intro hB
    rw [hB, mul_zero] at h_robertson
    linarith

end ArithmeticChecks

/-! ## Cauchy–Schwarz gives Robertson–Schrödinger -/

noncomputable section

namespace CauchyGram

/-- Every pair of vectors of a complex inner product space gives a `SchrodingerEvaluation`; its
quadratic bound is `gramDefectC_nonneg`. -/
def schrodingerEvaluationOfGram {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) :
    Robertson1929.SchrodingerEvaluation where
  sigmaA := ‖x‖
  sigmaB := ‖y‖
  covariance := covarianceC x y
  commutator := commutatorCoordinateC x y / 2
  sigmaA_nonneg := norm_nonneg x
  sigmaB_nonneg := norm_nonneg y
  quadratic_bound := by
    have h := robertsonSchrodinger_from_gram x y
    simpa [varianceC] using h

/-- The floor of the Gram evaluation is at most the product of the norms. -/
theorem schrodingerFloor_schrodingerEvaluationOfGram_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) :
    Robertson1929.schrodingerFloor (schrodingerEvaluationOfGram x y) ≤ ‖x‖ * ‖y‖ := by
  have h := Robertson1929.schrodingerFloor_le_mul (schrodingerEvaluationOfGram x y)
  simpa [schrodingerEvaluationOfGram] using h

end CauchyGram

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D46_ConeInBand
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Poincaré 1911 — the necessity of the quantum

Poincaré's 1911 impossibility argument, formalized at its honest core. The mean energy of a
quantized oscillator at inverse temperature `β`, with level spacing `ε`, is Planck's law
`ε / (e^{βε} − 1)`; the mean energy of a classical (Boltzmann, continuous) oscillator is
`1 / β` (Rayleigh–Jeans). These two can never agree: `e^x − 1 ≠ x` for every `x > 0`.
No continuous Boltzmann statistics reproduces Planck's law.

## Main results

- `Poincare1911.quantum_partition` : `∑' e^{−βnε} = (1 − e^{−βε})⁻¹`.
- `Poincare1911.quantum_energy_sum` : `∑' nε e^{−βnε} = ε e^{−βε} / (1 − e^{−βε})²`.
- `Poincare1911.quantum_mean_energy` : the Planck mean energy `= ε / (e^{βε} − 1)`.
- `Poincare1911.classical_mean_energy` : the classical mean energy `= 1 / β`.
- `Poincare1911.exp_sub_one_ne` : `e^x − 1 ≠ x` for `x > 0` (the impossibility).
- `Poincare1911.quantum_ne_classical` : the quantum and classical means never agree.
- `Poincare1911.planck_lt_rayleigh_jeans` : pointwise, Planck is strictly below
  Rayleigh–Jeans.
-/

@[expose] public noncomputable section

namespace Poincare1911

open Real

variable {β ε : ℝ}

/-! ## 1. The quantum oscillator: exact geometric sums -/

private theorem quantum_summand_eq :
    (fun n : ℕ => (n : ℝ) * ε * exp (-β * (n : ℝ) * ε))
      = fun n : ℕ => ε * ((n : ℝ) * exp (-(β * ε)) ^ n) := by
  funext n
  rw [show -β * (n : ℝ) * ε = (n : ℝ) * (-(β * ε)) by ring, exp_nat_mul]
  ring

/-- The partition sum: `∑' e^{−βnε} = (1 − e^{−βε})⁻¹`. -/
theorem quantum_partition (hβ : 0 < β) (hε : 0 < ε) :
    ∑' n : ℕ, exp (-β * (n : ℝ) * ε) = (1 - exp (-(β * ε)))⁻¹ := by
  have hβε : 0 < β * ε := mul_pos hβ hε
  have hn : ‖exp (-(β * ε))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (neg_lt_zero.mpr hβε)
  have hc : (fun n : ℕ => exp (-β * (n : ℝ) * ε)) = fun n : ℕ => exp (-(β * ε)) ^ n := by
    funext n
    rw [show -β * (n : ℝ) * ε = (n : ℝ) * (-(β * ε)) by ring, exp_nat_mul]
  rw [hc, (hasSum_geometric_of_norm_lt_one hn).tsum_eq]

/-- The energy sum: `∑' nε e^{−βnε} = ε e^{−βε} / (1 − e^{−βε})²`. -/
theorem quantum_energy_sum (hβ : 0 < β) (hε : 0 < ε) :
    ∑' n : ℕ, (n : ℝ) * ε * exp (-β * (n : ℝ) * ε)
      = ε * exp (-(β * ε)) / (1 - exp (-(β * ε))) ^ 2 := by
  have hβε : 0 < β * ε := mul_pos hβ hε
  have hn : ‖exp (-(β * ε))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (neg_lt_zero.mpr hβε)
  rw [quantum_summand_eq,
    (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left ε |>.tsum_eq, ← mul_div_assoc]

/-- **Planck's mean energy**: the Gibbs average of `Eₙ = nε` over the geometric weights
`e^{−βnε}` equals `ε / (e^{βε} − 1)`. -/
theorem quantum_mean_energy (hβ : 0 < β) (hε : 0 < ε) :
    (∑' n : ℕ, (n : ℝ) * ε * exp (-β * (n : ℝ) * ε))
      / (∑' n : ℕ, exp (-β * (n : ℝ) * ε)) = ε / (exp (β * ε) - 1) := by
  have hβε : 0 < β * ε := mul_pos hβ hε
  have h1 : (1 : ℝ) - exp (-(β * ε)) ≠ 0 := by
    have h2 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hβε)
    have h3 := exp_pos (-(β * ε))
    linarith
  have h2 : exp (β * ε) ≠ 0 := ne_of_gt (exp_pos _)
  rw [quantum_energy_sum hβ hε, quantum_partition hβ hε, exp_neg]
  field_simp

/-! ## 2. The classical oscillator: equipartition -/

/-- **Equipartition**: the Boltzmann average of `E` over the continuous weights `e^{−βE}`
on `[0, ∞)` equals `1 / β`. -/
theorem classical_mean_energy (hβ : 0 < β) :
    (∫ E in Set.Ioi (0 : ℝ), E * exp (-β * E)) / (∫ E in Set.Ioi (0 : ℝ), exp (-β * E))
      = β⁻¹ := by
  have hnum : ∫ E in Set.Ioi (0 : ℝ), E * exp (-β * E) = (β ^ 2)⁻¹ := by
    calc ∫ E in Set.Ioi (0 : ℝ), E * exp (-β * E)
        = ∫ E in Set.Ioi (0 : ℝ), E ^ (1 : ℝ) * exp (-β * E ^ (1 : ℝ)) := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun E hE =>
            by simp only [Real.rpow_one]
      _ = β ^ (-(1 + 1) / (1 : ℝ)) * (1 / (1 : ℝ)) * Gamma ((1 + 1) / (1 : ℝ)) :=
          integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := β)
            (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hβ
      _ = (β ^ 2)⁻¹ := by
          rw [show (1 + 1 : ℝ) / (1 : ℝ) = 1 + 1 by norm_num,
            Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
            show (1 : ℝ) / (1 : ℝ) = 1 by norm_num, mul_one, mul_one, mul_one,
            show -(1 + 1) / (1 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hβ.le,
            Real.rpow_two]
  have hden : ∫ E in Set.Ioi (0 : ℝ), exp (-β * E) = β⁻¹ := by
    calc ∫ E in Set.Ioi (0 : ℝ), exp (-β * E)
        = ∫ E in Set.Ioi (0 : ℝ), exp (-β * E ^ (1 : ℝ)) := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun E hE =>
            by simp only [Real.rpow_one]
      _ = β ^ (-1 / (1 : ℝ)) * Gamma (1 / (1 : ℝ) + 1) :=
          integral_exp_neg_mul_rpow (p := 1) (b := β) (by norm_num : (0 : ℝ) < 1) hβ
      _ = β⁻¹ := by
          rw [show (-1 : ℝ) / (1 : ℝ) = -1 by norm_num, Real.rpow_neg_one,
            show (1 : ℝ) / (1 : ℝ) + 1 = 1 + 1 by norm_num,
            Real.Gamma_add_one one_ne_zero, Real.Gamma_one, mul_one, mul_one]
  rw [hnum, hden]
  have hb : β ≠ 0 := ne_of_gt hβ
  field_simp [hb]

/-! ## 3. The impossibility -/

/-- **The impossibility (Poincaré, 1911).** For every `x > 0`, `e^x − 1 ≠ x`: the exponential
is never linear on a positive interval. This is exactly the obstruction that prevents any
classical (Rayleigh–Jeans) value `1/β` from agreeing with Planck's law `ε / (e^{βε} − 1)`. -/
theorem exp_sub_one_ne (x : ℝ) (hx : 0 < x) : exp x - 1 ≠ x := by
  have h := add_one_lt_exp hx.ne'
  intro he
  linarith

/-- **Planck is strictly below Rayleigh–Jeans**, pointwise: since `e^{βε} − 1 > βε`,
`ε / (e^{βε} − 1) < 1 / β`. -/
theorem planck_lt_rayleigh_jeans (hβ : 0 < β) (hε : 0 < ε) :
    ε / (exp (β * ε) - 1) < β⁻¹ := by
  have h := add_one_lt_exp (mul_ne_zero hβ.ne' hε.ne')
  have he : 0 < exp (β * ε) - 1 := by
    have h1 : (1 : ℝ) < exp (β * ε) := one_lt_exp_iff.mpr (mul_pos hβ hε)
    linarith
  have hb' : β⁻¹ * (exp (β * ε) - 1) = (exp (β * ε) - 1) / β := by
    rw [div_eq_mul_inv, mul_comm]
  rw [div_lt_iff₀ he, hb', lt_div_iff₀ hβ]
  linarith

/-- **No continuous Boltzmann statistics reproduces Planck's law.** For every `β > 0` and
`ε > 0`, the quantum mean energy differs from the classical one. -/
theorem quantum_ne_classical (hβ : 0 < β) (hε : 0 < ε) :
    ε / (exp (β * ε) - 1) ≠ β⁻¹ :=
  (planck_lt_rayleigh_jeans hβ hε).ne

end Poincare1911

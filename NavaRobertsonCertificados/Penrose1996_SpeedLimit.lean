/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Penrose 1996 — the time–energy relation is a bound, not a lifetime

Penrose estimates the collapse time of a spatial superposition as `τ = ħ / ΔE` (Diósi–Penrose;
tested underground by Donadi et al., Nat. Phys. 17, 74 (2021)), reading the time–energy
relation as the lifetime of an unstable state. Unitary dynamics gives a bound instead. In the
spectral form of a finite-dimensional state (`ħ = 1`), with weights `p_k` on the energies `E_k`,
the survival amplitude is `A(t) = ∑ p_k e^{−i E_k t}` and its energy spread is `ΔE`.

* `‖A(t)‖ ≥ 1 − ΔE² t² / 2`, so no state becomes orthogonal before `√2 / ΔE`; at Penrose's
  time `1 / ΔE` the amplitude is still at least `1/2`.
* Two equal branches: `‖A(t)‖ = |cos (ΔE t)|`, orthogonal exactly at `π / (2 ΔE)`
  (Mandelstam–Tamm saturated) and back to `1` with period `π / ΔE`. Unitary evolution never
  decays: a collapse at rate `ΔE / ħ` needs non-unitary dynamics.

## Main results

- `Penrose1996.one_sub_le_norm_amplitude` : `1 − ΔE² t² / 2 ≤ ‖A(t)‖`.
- `Penrose1996.speed_limit` : `A(t) = 0` forces `2 ≤ ΔE² t²`.
- `Penrose1996.half_le_norm_amplitude` : `‖A(t)‖ ≥ 1/2` up to Penrose's time `1 / ΔE`.
- `Penrose1996.twoBranch_norm_amplitude` : two branches, `‖A(t)‖ = |cos (ΔE t)|`.
- `Penrose1996.twoBranch_orthogonal`, `twoBranch_ne_zero` : first orthogonal at `π / (2 ΔE)`.
- `Penrose1996.twoBranch_periodic` : `‖A(t + π / ΔE)‖ = ‖A(t)‖`: no decay.
-/

@[expose] public noncomputable section

namespace Penrose1996

open Complex

variable {n : ℕ} (p E : Fin n → ℝ)

/-- The survival amplitude `A(t) = ∑ p_k e^{−i E_k t}` (`ħ = 1`). -/
def amplitude (t : ℝ) : ℂ := ∑ k, (p k : ℂ) * exp (↑(-(E k * t)) * I)

/-- The mean energy `⟨E⟩ = ∑ p_k E_k`. -/
def mean : ℝ := ∑ k, p k * E k

/-- The energy variance `ΔE² = ∑ p_k (E_k − ⟨E⟩)²`. -/
def var : ℝ := ∑ k, p k * (E k - mean p E) ^ 2

/-- Removing the mean phase leaves `∑ p_k cos ((E_k − ⟨E⟩) t)`. -/
theorem re_amplitude (t : ℝ) : (exp (↑(mean p E * t) * I) * amplitude p E t).re
    = ∑ k, p k * Real.cos ((E k - mean p E) * t) := by
  rw [amplitude, Finset.mul_sum, re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, ← exp_add, ← add_mul, ← ofReal_add, re_ofReal_mul, exp_ofReal_mul_I_re,
    show mean p E * t + -(E k * t) = -((E k - mean p E) * t) by ring, Real.cos_neg]

/-- **The quantum speed limit**: `1 − ΔE² t² / 2 ≤ ‖A(t)‖`. -/
theorem one_sub_le_norm_amplitude (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) (t : ℝ) :
    1 - var p E * t ^ 2 / 2 ≤ ‖amplitude p E t‖ := by
  have h : 1 - var p E * t ^ 2 / 2 = ∑ k, p k * (1 - ((E k - mean p E) * t) ^ 2 / 2) := by
    rw [var, mul_div_assoc, Finset.sum_mul]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
  calc 1 - var p E * t ^ 2 / 2
      ≤ ∑ k, p k * Real.cos ((E k - mean p E) * t) := h ▸ Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos) (hp k)
    _ = (exp (↑(mean p E * t) * I) * amplitude p E t).re := (re_amplitude p E t).symm
    _ ≤ ‖exp (↑(mean p E * t) * I) * amplitude p E t‖ := re_le_norm _
    _ = ‖amplitude p E t‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]

/-- **No orthogonality before `√2 / ΔE`**: `A(t) = 0` forces `2 ≤ ΔE² t²`. -/
theorem speed_limit (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) {t : ℝ}
    (h0 : amplitude p E t = 0) : 2 ≤ var p E * t ^ 2 := by
  have := one_sub_le_norm_amplitude p E hp h1 t
  rw [h0, norm_zero] at this
  linarith

/-- **At Penrose's time the state survives**: for `ΔE² t² ≤ 1`, `‖A(t)‖ ≥ 1/2`. -/
theorem half_le_norm_amplitude (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) {t : ℝ}
    (ht : var p E * t ^ 2 ≤ 1) : 1 / 2 ≤ ‖amplitude p E t‖ :=
  le_trans (by linarith) (one_sub_le_norm_amplitude p E hp h1 t)

/-! ## Two equal branches -/

/-- The weights of two equal branches. -/
def half : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem twoBranch_var (E₀ E₁ : ℝ) : var half ![E₀, E₁] = ((E₁ - E₀) / 2) ^ 2 := by
  simp [var, mean, half, Fin.sum_univ_two]
  ring

theorem twoBranch_norm_amplitude (E₀ E₁ t : ℝ) :
    ‖amplitude half ![E₀, E₁] t‖ = |Real.cos ((E₁ - E₀) / 2 * t)| := by
  have h : amplitude half ![E₀, E₁] t
      = exp (↑(-((E₀ + E₁) / 2 * t)) * I) * Complex.cos ↑((E₁ - E₀) / 2 * t) := by
    simp only [amplitude, half, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Complex.cos, mul_add, ← exp_add, mul_div_assoc']
    push_cast
    ring_nf
  rw [h, norm_mul, norm_exp_ofReal_mul_I, one_mul, ← ofReal_cos, norm_real, Real.norm_eq_abs]

/-- **First orthogonality at `π / (2 ΔE)`**: Mandelstam–Tamm is saturated. -/
theorem twoBranch_orthogonal {E₀ E₁ : ℝ} (h : E₀ ≠ E₁) :
    amplitude half ![E₀, E₁] (Real.pi / (2 * |(E₁ - E₀) / 2|)) = 0 := by
  have hd : |(E₁ - E₀) / 2| ≠ 0 := abs_ne_zero.mpr (by intro h'; apply h; linarith)
  rw [← norm_eq_zero, twoBranch_norm_amplitude, ← Real.cos_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi / (2 * |(E₁ - E₀) / 2|))]
  field_simp
  simp

theorem twoBranch_ne_zero {E₀ E₁ t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < Real.pi / (2 * |(E₁ - E₀) / 2|)) : amplitude half ![E₀, E₁] t ≠ 0 := by
  rw [← norm_ne_zero_iff, twoBranch_norm_amplitude, ← Real.cos_abs, abs_mul, abs_of_nonneg ht0]
  refine abs_ne_zero.mpr (Real.cos_pos_of_mem_Ioo ⟨by nlinarith [abs_nonneg ((E₁ - E₀) / 2),
    Real.pi_pos], ?_⟩).ne'
  rcases (abs_nonneg ((E₁ - E₀) / 2)).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; positivity
  · rw [lt_div_iff₀ (by positivity)] at ht
    linarith

/-- **No decay**: the two-branch amplitude has period `π / ΔE` in modulus. -/
theorem twoBranch_periodic {E₀ E₁ : ℝ} (h : E₀ ≠ E₁) (t : ℝ) :
    ‖amplitude half ![E₀, E₁] (t + Real.pi / |(E₁ - E₀) / 2|)‖
      = ‖amplitude half ![E₀, E₁] t‖ := by
  have hd : (E₁ - E₀) / 2 ≠ 0 := by intro h'; apply h; linarith
  rw [twoBranch_norm_amplitude, twoBranch_norm_amplitude, mul_add]
  rcases abs_cases ((E₁ - E₀) / 2) with ⟨ha, -⟩ | ⟨ha, -⟩
  · rw [ha, mul_div_cancel₀ _ hd, Real.cos_add_pi, abs_neg]
  · rw [ha, show (E₁ - E₀) / 2 * (Real.pi / -((E₁ - E₀) / 2)) = -Real.pi by field_simp,
      ← sub_eq_add_neg, Real.cos_sub_pi, abs_neg]

end Penrose1996

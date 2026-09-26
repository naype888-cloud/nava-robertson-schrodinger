/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The cosecant- and cotangent-squared identities

This file proves the classical identity
$$\sum_{k=1}^{N-1} \csc^2\!\left(\frac{k\pi}{N}\right) = \frac{N^2 - 1}{3},$$
stated over `Real.sin` as `∑ k ∈ Finset.Ico 1 N, (Real.sin (k * π / N))⁻¹ ^ 2 = (N ^ 2 - 1) / 3`.

It also derives the cotangent identities
$$\sum_{k=1}^{N-1} \cot^2\!\left(\frac{k\pi}{N}\right)
    = \frac{(N-1)(N-2)}{3}$$
and
$$\sum_{k=1}^{m} \cot^2\!\left(\frac{k\pi}{2m+1}\right)
    = \frac{m(2m-1)}{3}.$$

The proof goes through the Chebyshev polynomial of the second kind `U (N-1)`, whose roots are
exactly `cos (k * π / N)` for `k = 1, …, N-1`. Since `U (N-1)` splits over `ℝ`, its logarithmic
derivative at a point `x` equals `∑ 1 / (x - z)` over the roots `z`; evaluating this at `x = 1`
and `x = -1` and combining via `1 / (1 - z ^ 2) = (1/2) (1 / (1 - z) + 1 / (1 + z))` gives
`∑ 1 / (1 - z ^ 2) = (N ^ 2 - 1) / 3`. Rewriting `1 - cos ^ 2 = sin ^ 2`
yields the cosecant statement. The full cotangent sum follows termwise from
`cot² x = csc² x - 1`. For the odd denominator `N = 2m + 1`, the involution
`k ↦ N - k` pairs the `2m` terms into two equal halves because
`cot² (π - x) = cot² x`.

## Main statements

* `Polynomial.Chebyshev.sum_one_div_one_sub_sq_roots_U_real`: `∑ 1 / (1 - z ^ 2)` over the real
  roots of `U (n)` equals `((n + 1) ^ 2 - 1) / 3`.
* `Real.sum_inv_sin_sq_pi_mul_div`: the cosecant-squared identity.
* `Real.sum_cot_sq_pi_mul_div`: the full cotangent-squared identity.
* `Real.sum_cot_sq_pi_mul_div_two_mul_add_one`: the half-sum identity for odd denominators.

## References

The cosecant identity is classical, going back to Cauchy's *Cours d'analyse* (1821). The odd
cotangent half-sum is the arithmetic core of the elementary evaluation of
`∑ 1 / k ^ 2 = π ^ 2 / 6` given in M. Aigner and G. M. Ziegler, *Proofs from THE BOOK*,
Chapter "π²/6".
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev Real

noncomputable section

namespace Polynomial.Chebyshev

/-! ## `U n` splits over `ℝ` -/

/-- The Chebyshev polynomial of the second kind `U n` splits over `ℝ`: all `n` of its roots are
real (they are `cos ((k + 1) * π / (n + 1))` for `k < n`). -/
theorem splits_U_real (n : ℕ) : (U ℝ n).Splits := by
  rw [splits_iff_card_roots]
  cases n with
  | zero => simp [U_zero]
  | succ m =>
    set N := m + 1 with hN
    have hdeg : (U ℝ N).natDegree = N := natDegree_U_natCast (R := ℝ) N
    rw [roots_U_real N]
    have hinj :
        Set.InjOn (fun k : ℕ ↦ cos ((k + 1) * π / (N + 1))) (Finset.range N) :=
      (Finset.range N).nodup_map_iff_injOn.mp (roots_U_real_nodup N)
    have hcard :
        ((Finset.range N).image fun k : ℕ ↦
            cos ((k + 1) * π / (N + 1))).card = N := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    show (Multiset.card _) = _
    rw [hdeg]
    exact hcard

/-! ## Derivative of `U n` at `±1` -/

private theorem derivative_U_natCast_eval_one (n : ℕ) :
    (derivative (U ℝ (n : ℤ))).eval (1 : ℝ) =
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n : ℝ) / 3 := by
  have h := derivative_U_eval_one (R := ℝ) (n : ℤ)
  push_cast at h
  linarith

private theorem derivative_U_natCast_eval_neg_one (n : ℕ) :
    (derivative (U ℝ (n : ℤ))).eval (-1 : ℝ) =
      -((-1 : ℝ) ^ n) *
        (((n : ℝ) + 2) * ((n : ℝ) + 1) * (n : ℝ) / 3) := by
  have hfun :
      (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x)) =
        fun x ↦ (-1 : ℝ) ^ n * (U ℝ (n : ℤ)).eval x := by
    funext x
    rw [U_eval_neg (R := ℝ) n x, Int.cast_negOnePow_natCast]
  have hL : HasDerivAt (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x))
      (-(derivative (U ℝ (n : ℤ))).eval (-1)) 1 := by
    have h := (U ℝ (n : ℤ)).hasDerivAt (-1 : ℝ)
    have hc := h.comp 1 (hasDerivAt_id' 1).neg
    rw [mul_neg_one] at hc
    exact hc
  have hR : HasDerivAt
      (fun x : ℝ ↦ (-1 : ℝ) ^ n * (U ℝ (n : ℤ)).eval x)
      ((-1 : ℝ) ^ n * (derivative (U ℝ (n : ℤ))).eval 1) 1 :=
    ((U ℝ (n : ℤ)).hasDerivAt (1 : ℝ)).const_mul _
  have heq : HasDerivAt (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x))
      ((-1 : ℝ) ^ n * (derivative (U ℝ (n : ℤ))).eval 1) 1 :=
    hfun ▸ hR
  have hder := HasDerivAt.unique hL heq
  have hUd1 := derivative_U_natCast_eval_one n
  rw [hUd1] at hder
  linarith

/-! ## Sums of `1 / (1 - z)`, `1 / (1 + z)`, `1 / (1 - z ^ 2)` over the roots of `U n` -/

/-- `∑ 1 / (1 - z)` over the real roots `z` of `U n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_sub_roots_U_real (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hsplit : (U ℝ (n : ℤ)).Splits := splits_U_real n
  have hne : (U ℝ (n : ℤ)).eval (1 : ℝ) ≠ 0 := by
    rw [U_eval_one]; positivity
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hne
  have hU1 : (U ℝ (n : ℤ)).eval (1 : ℝ) = (n : ℝ) + 1 := by
    simp [U_eval_one]
  have hUd := derivative_U_natCast_eval_one n
  have hratio :
      (derivative (U ℝ (n : ℤ))).eval (1 : ℝ) / (U ℝ (n : ℤ)).eval (1 : ℝ) =
        (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
    rw [hUd, hU1]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [this]; ring
  rw [← hratio, hlog]

/-- `∑ 1 / (1 + z)` over the real roots `z` of `U n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_add_roots_U_real (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hsplit : (U ℝ (n : ℤ)).Splits := splits_U_real n
  have hU : (U ℝ (n : ℤ)).eval (-1 : ℝ) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) := by
    rw [U_eval_neg_one (R := ℝ) (n : ℤ), Int.cast_negOnePow_natCast]
    push_cast; ring
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hpow : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hne : (U ℝ (n : ℤ)).eval (-1 : ℝ) ≠ 0 := by
    rw [hU]; exact mul_ne_zero hpow hn1
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hne
  have hUd := derivative_U_natCast_eval_neg_one n
  have hratio :
      (derivative (U ℝ (n : ℤ))).eval (-1 : ℝ) / (U ℝ (n : ℤ)).eval (-1 : ℝ) =
        -((((n : ℝ) + 1) ^ 2 - 1) / 3) := by
    rw [hUd, hU]
    field_simp [hpow, hn1]; ring
  have hmap :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (-1 - z)).sum =
        -((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum := by
    have hpt :
        ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (-1 - z)) =
          (U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ -((1 : ℝ) / (1 + z)) := by
      refine Multiset.map_congr rfl fun z _ => ?_
      have : (-1 - z : ℝ) = -(1 + z) := by ring
      rw [this, div_neg]
    rw [hpt, Multiset.sum_map_neg]
  have : -((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum =
      -((((n : ℝ) + 1) ^ 2 - 1) / 3) := by
    rwa [← hmap, ← hlog]
  linarith

private theorem abs_root_U_real_lt_one {n : ℕ} {z : ℝ}
    (hz : z ∈ (U ℝ (n : ℤ)).roots) (hn : 1 ≤ n) : |z| < 1 := by
  have hroots := roots_U_real n
  rw [hroots, Finset.mem_val, Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hklt : k < n := Finset.mem_range.mp hk
  have hθpos : 0 < (k + 1 : ℝ) * π / (n + 1) := by positivity
  have hθlt : (k + 1 : ℝ) * π / (n + 1) < π := by
    have : (k + 1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hklt
    calc
      (k + 1 : ℝ) * π / (n + 1) ≤ n * π / (n + 1) := by gcongr
      _ < π := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [pi_pos]
  have hsin : 0 < sin ((k + 1 : ℝ) * π / (n + 1)) :=
    sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hpyth := sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))
  have hsq : cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 < 1 := by
    nlinarith [mul_pos hsin hsin]
  exact (sq_lt_one_iff_abs_lt_one _).mp hsq

/-- `∑ 1 / (1 - z ^ 2)` over the real roots `z` of `U n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_sub_sq_roots_U_real (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have h1 := sum_one_div_one_sub_roots_U_real n hn
  have h2 := sum_one_div_one_add_roots_U_real n hn
  have hpoint (z : ℝ) (hz : z ∈ (U ℝ (n : ℤ)).roots) :
      (1 : ℝ) / (1 - z ^ 2) =
        (1 / 2 : ℝ) * ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z)) := by
    have habs := abs_root_U_real_lt_one hz hn
    have hz1 : z ≠ 1 := by
      intro h; rw [h, abs_one] at habs; linarith
    have hzm1 : z ≠ -1 := by
      intro h; rw [h, abs_neg, abs_one] at habs; linarith
    have hden : (1 - z ^ 2 : ℝ) ≠ 0 := by
      intro h
      have : z ^ 2 = 1 := by linarith
      have : |z| = 1 := (sq_eq_one_iff.mp this).elim (by intro; simp [*]) (by intro; simp [*])
      linarith [habs]
    have hz1' : (1 - z : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hzm : (1 + z : ℝ) ≠ 0 := by
      intro h; exact hzm1 (by linarith)
    field_simp [hz1', hzm, hden]
    ring
  have hdecomp :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
        (1 / 2 : ℝ) *
          (((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 - z)).sum +
            ((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 + z)).sum) := by
    classical
    calc
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum
          = ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦
              (1 / 2 : ℝ) * ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z))).sum := by
            refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz => hpoint z hz)
      _ = (1 / 2 : ℝ) *
            ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦
              ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z))).sum := by
            simp [Multiset.sum_map_mul_left]
      _ = (1 / 2 : ℝ) *
            (((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 - z)).sum +
              ((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 + z)).sum) := by
            simp [Multiset.sum_map_add]
  rw [hdecomp, h1, h2]
  ring

end Polynomial.Chebyshev

/-! ## The cosecant-squared identity -/

/-- **The cosecant-squared identity.**
`∑_{k=1}^{N-1} csc²(kπ/N) = (N² - 1) / 3`, stated over `Real.sin`. -/
theorem Real.sum_inv_sin_sq_pi_mul_div (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 =
      ((N : ℝ) ^ 2 - 1) / 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hsum := Polynomial.Chebyshev.sum_one_div_one_sub_sq_roots_U_real n hn
  classical
  have hinj :
      Set.InjOn (fun k : ℕ ↦ Real.cos ((k + 1) * π / (n + 1))) (Finset.range n) :=
    (Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n)
  have hfin :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
        ∑ k ∈ Finset.range n,
          (1 : ℝ) / (1 - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) := by
    rw [Polynomial.Chebyshev.roots_U_real n, Finset.image_val_of_injOn hinj, Multiset.map_map]
    rfl
  have hsin :
      ∑ k ∈ Finset.range n,
          (1 : ℝ) / (1 - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) =
        ∑ k ∈ Finset.range n, (Real.sin ((k + 1 : ℝ) * π / (n + 1)))⁻¹ ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have h1 : (1 : ℝ) - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 =
        Real.sin ((k + 1 : ℝ) * π / (n + 1)) ^ 2 := by
      linarith [sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))]
    rw [h1, one_div, inv_pow]
  have himg :
      Finset.Ico 1 (n + 1) = (Finset.range n).image (fun k ↦ k + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [himg, Finset.sum_image (fun x _ y _ h => by simpa using h)]
  push_cast
  rw [← hsin, ← hfin]
  exact hsum

/-! ## The cotangent-squared identities -/

/-- **The full cotangent-squared identity.**
`∑_{k=1}^{N-1} cot²(kπ/N) = (N-1)(N-2)/3`.

This is the cosecant-squared identity with `1` subtracted from each of its `N - 1` terms,
using `cot² x = csc² x - 1`. -/
theorem Real.sum_cot_sq_pi_mul_div (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, Real.cot ((k : ℝ) * π / N) ^ 2 =
      ((N : ℝ) - 1) * ((N : ℝ) - 2) / 3 := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ico 1 N) :
      Real.cot ((k : ℝ) * π / N) ^ 2 =
        (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 - 1 := by
    have hk' := Finset.mem_Ico.mp hk
    have hkpos : 0 < k := by omega
    have hklt : k < N := by omega
    have hNpos : (0 : ℝ) < N := by positivity
    have hθpos : 0 < (k : ℝ) * π / N := by positivity
    have hθlt : (k : ℝ) * π / N < π := by
      rw [div_lt_iff₀ hNpos]
      have hklt' : (k : ℝ) < N := by exact_mod_cast hklt
      nlinarith [pi_pos]
    have hsin : Real.sin ((k : ℝ) * π / N) ≠ 0 :=
      ne_of_gt (sin_pos_of_pos_of_lt_pi hθpos hθlt)
    rw [Real.cot_eq_cos_div_sin]
    field_simp [hsin]
    nlinarith [Real.sin_sq_add_cos_sq ((k : ℝ) * π / N)]
  calc
    ∑ k ∈ Finset.Ico 1 N, Real.cot ((k : ℝ) * π / N) ^ 2 =
        ∑ k ∈ Finset.Ico 1 N,
          ((Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 - 1) := by
      exact Finset.sum_congr rfl hpoint
    _ = (∑ k ∈ Finset.Ico 1 N,
          (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2) -
        ∑ _k ∈ Finset.Ico 1 N, (1 : ℝ) := by
      rw [Finset.sum_sub_distrib]
    _ = ((N : ℝ) - 1) * ((N : ℝ) - 2) / 3 := by
      rw [Real.sum_inv_sin_sq_pi_mul_div N hN]
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      push_cast
      ring

/-- **The cotangent-squared identity for an odd denominator.**
`∑_{k=1}^{m} cot²(kπ/(2m+1)) = m(2m-1)/3`.

Split the full sum at `m + 1`. The change of variables `k ↦ 2m + 1 - k` sends its upper
half to its lower half, and `cot² (π - x) = cot² x` makes the two sums equal. -/
theorem Real.sum_cot_sq_pi_mul_div_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico 1 (m + 1),
        Real.cot ((k : ℝ) * π / (2 * m + 1)) ^ 2 =
      (m : ℝ) * (2 * (m : ℝ) - 1) / 3 := by
  let N := 2 * m + 1
  let f : ℕ → ℝ := fun k => Real.cot ((k : ℝ) * π / N) ^ 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hfull := Real.sum_cot_sq_pi_mul_div N hN
  have hsplit :
      (∑ k ∈ Finset.Ico 1 (m + 1), f k) +
          ∑ k ∈ Finset.Ico (m + 1) N, f k =
        ∑ k ∈ Finset.Ico 1 N, f k :=
    Finset.sum_Ico_consecutive f (by omega) (by dsimp [N]; omega)
  have hsymm (k : ℕ) (hk : k ∈ Finset.Ico (m + 1) N) : f (N - k) = f k := by
    have hk' := Finset.mem_Ico.mp hk
    have hkN : k ≤ N := by omega
    have hangle :
        ((N - k : ℕ) : ℝ) * π / N = π - (k : ℝ) * π / N := by
      rw [Nat.cast_sub hkN]
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      field_simp [hN0]
    dsimp [f]
    rw [hangle]
    simp [Real.cot_eq_cos_div_sin, Real.sin_pi_sub, Real.cos_pi_sub]
    ring
  have himage :
      (Finset.Ico (m + 1) N).image (fun k => N - k) = Finset.Ico 1 (m + 1) := by
    dsimp [N]
    rw [Nat.Ico_image_const_sub_eq_Ico (by omega)]
    congr <;> omega
  have hinj : Set.InjOn (fun k => N - k) (Finset.Ico (m + 1) N) := by
    intro a ha b hb hab
    have ha' := Finset.mem_Ico.mp ha
    have hb' := Finset.mem_Ico.mp hb
    dsimp [N] at ha' hb' hab ⊢
    omega
  have hupper :
      (∑ k ∈ Finset.Ico (m + 1) N, f k) =
        ∑ k ∈ Finset.Ico 1 (m + 1), f k := by
    rw [← himage, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun k hk => (hsymm k hk).symm
  rw [hupper] at hsplit
  rw [← hsplit] at hfull
  dsimp [f, N] at hfull ⊢
  push_cast at hfull
  nlinarith

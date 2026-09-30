/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.Poincare1911_QuantumNecessity
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Dirac 1928 — the minimal dimension of the gamma matrices

The algebraic verdict of the Dirac episode, by the standard trace argument. Let
`γ₀, …, γ₃ ∈ Matₙ(ℂ)` satisfy `{γ_μ, γ_ν} = 2η_μν · 1`, `η = diag(1, −1, −1, −1)`.

Conjugation by `γ_k` multiplies a word in the generators by `(−1)^m`, where `m` counts the
letters different from `k`; whenever `m` is odd the word is traceless. Pairing the 16 ordered
monomials against their reverses isolates each coefficient, so the monomials are linearly
independent in every nonzero representation. Hence `16 ≤ n²`: no `2 × 2` gamma matrices exist,
and the minimal complex dimension is 4.

## Main results

- `Dirac1928.trace_word_eq_zero` : a word with an odd count of letters `≠ k` is traceless.
- `Dirac1928.monomial_linearIndependent` : the 16 ordered monomials are independent.
- `Dirac1928.four_le_dim` : every nonzero representation has `4 ≤ n`.
- `Dirac1928.no_dirac_two_by_two` : there are no `2 × 2` gamma matrices.
- `Dirac1928.isLeast_dim` : Dirac's `4 × 4` matrices attain the bound; the minimum is 4.
-/

@[expose] public noncomputable section

namespace Dirac1928

open Matrix

variable {n : ℕ} (γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ)

/-- The diagonal of the Minkowski form `η = diag(1, −1, −1, −1)`. -/
def eta (μ : Fin 4) : ℂ := if μ = 0 then 1 else -1

/-- The Clifford relation `{γ_μ, γ_ν} = 2η_μν · 1`. -/
def CliffordRelation : Prop :=
  ∀ μ ν, γ μ * γ ν + γ ν * γ μ = (if μ = ν then 2 * eta μ else 0) • (1 : Matrix _ _ ℂ)

/-- The word `γ_{l₀} ⋯ γ_{l_k}`. -/
def word (l : List (Fin 4)) : Matrix (Fin n) (Fin n) ℂ := (l.map γ).prod

/-- The ordered monomial `γ_{i₁} ⋯ γ_{i_k}`, `i₁ < ⋯ < i_k` the elements of `s`. -/
def monomial (s : Finset (Fin 4)) : Matrix (Fin n) (Fin n) ℂ :=
  word γ ((List.finRange 4).filter (· ∈ s))

theorem word_append (l₁ l₂ : List (Fin 4)) : word γ (l₁ ++ l₂) = word γ l₁ * word γ l₂ := by
  simp [word]

theorem eta_ne_zero (μ : Fin 4) : eta μ ≠ 0 := by unfold eta; split_ifs <;> norm_num

variable {γ} (hγ : CliffordRelation γ)
include hγ

theorem gamma_sq (μ : Fin 4) : γ μ * γ μ = eta μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := hγ μ μ
  simp only [↓reduceIte] at h
  rw [← two_smul ℂ, mul_smul] at h
  exact smul_right_injective _ two_ne_zero h

theorem anticomm {μ ν : Fin 4} (h : μ ≠ ν) : γ μ * γ ν = -(γ ν * γ μ) :=
  eq_neg_of_add_eq_zero_left <| by simpa [h] using hγ μ ν

/-- Moving `γ_k` across a word costs one sign per letter different from `k`. -/
theorem gamma_mul_word (k : Fin 4) (l : List (Fin 4)) :
    γ k * word γ l = (-1 : ℂ) ^ l.countP (· ≠ k) • (word γ l * γ k) := by
  induction l with
  | nil => simp [word]
  | cons a l ih =>
    simp only [word, List.map_cons, List.prod_cons] at ih ⊢
    by_cases h : a = k
    · subst h
      rw [List.countP_cons_of_neg (by simp), ← mul_assoc, gamma_sq hγ, ih]
      simp only [smul_mul_assoc, mul_assoc, gamma_sq hγ, Matrix.mul_smul, mul_one, smul_smul,
        one_mul]
      rw [← mul_assoc, ← mul_pow]
      simp
    · rw [List.countP_cons_of_pos (by simpa using h), ← mul_assoc, anticomm hγ (Ne.symm h),
        neg_mul, mul_assoc, ih]
      simp [pow_succ, mul_assoc]

/-- **A word with an odd number of letters different from `k` is traceless**: conjugation by
`γ_k` flips its sign. -/
theorem trace_word_eq_zero (k : Fin 4) {l : List (Fin 4)} (hl : Odd (l.countP (· ≠ k))) :
    (word γ l).trace = 0 := by
  have h := congrArg trace (congrArg (· * γ k) (gamma_mul_word hγ k l))
  simp only [hl.neg_one_pow, neg_one_smul, neg_mul, trace_neg] at h
  rw [mul_assoc, trace_mul_comm] at h
  simp only [mul_assoc, gamma_sq hγ, Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul] at h
  simpa [eta_ne_zero] using CharZero.eq_neg_self_iff.mp h

/-- A word followed by its reverse collapses to a nonzero scalar. -/
theorem word_append_reverse (l : List (Fin 4)) :
    word γ (l ++ l.reverse) = (l.map eta).prod • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  induction l with
  | nil => simp [word]
  | cons a l ih =>
    rw [show a :: l ++ (a :: l).reverse = [a] ++ (l ++ l.reverse) ++ [a] by simp,
      word_append, word_append, ih]
    simp [word, gamma_sq hγ, smul_smul, mul_comm]

omit hγ in
/-- Two distinct subsets of `Fin 4` are separated by some `k` with odd total count. -/
theorem exists_odd_count (s t : Finset (Fin 4)) (h : s ≠ t) : ∃ k : Fin 4,
    Odd (((List.finRange 4).filter (· ∈ s)).countP (· ≠ k) +
      ((List.finRange 4).filter (· ∈ t)).countP (· ≠ k)) := by
  revert s t; decide +kernel

/-- **The 16 ordered monomials are linearly independent** in every nonzero representation:
pairing with the reversed monomial isolates each coefficient. -/
theorem monomial_linearIndependent (hn : 0 < n) :
    LinearIndependent ℂ (monomial γ) := by
  refine Fintype.linearIndependent_iff.mpr fun c hc b => ?_
  set L := (List.finRange 4).filter (· ∈ b)
  have key := congrArg (fun M => (word γ L.reverse * M).trace) hc
  simp only [Finset.mul_sum, mul_smul_comm, trace_sum, trace_smul, mul_zero, trace_zero,
    smul_eq_mul] at key
  rw [Finset.sum_eq_single b (fun s _ hs => ?_) (by simp)] at key
  · have hL := word_append_reverse hγ L.reverse
    rw [List.reverse_reverse] at hL
    rw [show monomial γ b = word γ L from rfl, ← word_append, hL, trace_smul, trace_one,
      Fintype.card_fin, smul_eq_mul] at key
    simpa [eta_ne_zero, hn.ne'] using key
  · obtain ⟨k, hk⟩ := exists_odd_count b s (Ne.symm hs)
    rw [monomial, ← word_append, trace_word_eq_zero hγ k (by
      rwa [List.countP_append, List.countP_reverse]), mul_zero]

/-- **Every nonzero representation of the Dirac algebra has dimension at least 4.** -/
theorem four_le_dim (hn : 0 < n) : 4 ≤ n := by
  have h := (monomial_linearIndependent hγ hn).fintype_card_le_finrank
  simp only [Fintype.card_finset, Fintype.card_fin, Module.finrank_matrix,
    Module.finrank_self, mul_one] at h
  nlinarith

omit hγ in
/-- **Dirac's algebraic bottleneck: there are no `2 × 2` gamma matrices.** -/
theorem no_dirac_two_by_two (γ : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    ¬ CliffordRelation γ :=
  fun hγ => absurd (four_le_dim hγ two_pos) (by norm_num)

/-! ## The Dirac representation attains the bound -/

/-- Dirac's `4 × 4` gamma matrices in the standard representation, over `ℤ[i]`. -/
def diracGammaZ : Fin 4 → Matrix (Fin 4) (Fin 4) GaussianInt :=
  let i : GaussianInt := ⟨0, 1⟩
  ![!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0],
    !![0, 0, 0, -i; 0, 0, i, 0; 0, i, 0, 0; -i, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]]

omit hγ in
theorem diracGammaZ_clifford (μ ν : Fin 4) :
    diracGammaZ μ * diracGammaZ ν + diracGammaZ ν * diracGammaZ μ
      = Matrix.diagonal fun _ => if μ = ν then 2 * (if μ = 0 then 1 else -1) else 0 := by
  revert μ ν; decide +kernel

/-- Dirac's gamma matrices in `Mat₄(ℂ)`. -/
def diracGamma (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  GaussianInt.toComplex.mapMatrix (diracGammaZ μ)

omit hγ in
theorem diracGamma_clifford : CliffordRelation diracGamma := by
  intro μ ν
  have h := congrArg GaussianInt.toComplex.mapMatrix (diracGammaZ_clifford μ ν)
  simp only [map_add, map_mul, RingHom.mapMatrix_apply, diagonal_map (map_zero _)] at h
  simp only [diracGamma, RingHom.mapMatrix_apply]
  rw [h, smul_one_eq_diagonal]
  congr 1
  funext
  split_ifs <;> subst_vars <;> simp [eta, *, map_ofNat]

omit hγ in
/-- **The minimal complex dimension of the Dirac algebra is 4.** -/
theorem isLeast_dim :
    IsLeast {n | 0 < n ∧ ∃ γ : Fin 4 → Matrix (Fin n) (Fin n) ℂ, CliffordRelation γ} 4 :=
  ⟨⟨by norm_num, diracGamma, diracGamma_clifford⟩, fun _ ⟨hn, _, hγ⟩ => four_le_dim hγ hn⟩

end Dirac1928

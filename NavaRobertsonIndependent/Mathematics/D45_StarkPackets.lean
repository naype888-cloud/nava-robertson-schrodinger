/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D38_GroupVelocity

/-!
# D45 — Stark packets: minimum uncertainty in motion

In the gauge `ψⱼ = (−i)ʲ φⱼ`, `φ` real, the equation `(T_d − iλ P_d) ψ = μ ψ` with
`λ = (d − 1)/(ρ_d z)` is the recurrence `φⱼ₊₁ = φⱼ₋₁ + (2(c₀ − j)/z) φⱼ`, `φ₋₁ = φ_d = 0`: a
discrete Wannier–Stark packet of centre `c₀`. It is solved from each end and glued at a site
`g`; the only condition is that the Casoratian of the two halves vanishes there. Every glued
packet saturates Robertson–Schrödinger and moves at `v = 4 ⟨(j − c₀)²⟩ / (ρ_d z)`.

## Main results

- `StarkPacket.seq_pos` : each half is positive up to the centre.
- `StarkPacket.glue_rec` : a glued packet solves the recurrence on `0, …, d − 1`.
-/

@[expose] public noncomputable section

open Complex TransportPosition NRSInequality EigenvectorSaturation NearMaxTension GroupVelocity

namespace StarkPacket

/-! ## A. One half of the packet -/

/-- The solution from the left end: `A₋₁ = 0`, `A₀ = 1`, `Aᵢ₊₁ = Aᵢ₋₁ + (2(c − i)/z) Aᵢ`. -/
def seq (z c : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * c / z
  | i + 2 => seq z c i + 2 * (c - (i + 1 : ℕ)) / z * seq z c (i + 1)

@[simp] lemma seq_zero (z c : ℝ) : seq z c 0 = 1 := rfl

lemma seq_one (z c : ℝ) : seq z c 1 = 2 * (c - (0 : ℕ)) / z * seq z c 0 := by
  simp [seq]

lemma seq_add_two (z c : ℝ) (i : ℕ) :
    seq z c (i + 2) = seq z c i + 2 * (c - (i + 1 : ℕ)) / z * seq z c (i + 1) := rfl

/-- Up to the centre, each half is positive. -/
lemma seq_pos {z c : ℝ} (hz : 0 < z) {t : ℕ} (hc : (t : ℝ) - 1 < c) :
    ∀ i ≤ t, 0 < seq z c i := by
  have key : ∀ i, i + 1 ≤ t → 0 < seq z c i ∧ 0 < seq z c (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h
      have : (1 : ℝ) ≤ t := by exact_mod_cast h
      exact ⟨one_pos, div_pos (by linarith) hz⟩
    | succ i ih =>
      intro h
      have : ((i + 2 : ℕ) : ℝ) ≤ t := by exact_mod_cast h
      have : 0 < 2 * (c - (i + 1 : ℕ)) / z := div_pos (by push_cast at *; linarith) hz
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact ⟨h2, by rw [seq_add_two]; positivity⟩
  intro i hi
  rcases i with _ | i
  · exact one_pos
  · exact (key i hi).2

lemma continuous_seq (z : ℝ) (i : ℕ) : Continuous fun c => seq z c i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ => exact continuous_const
    | 1, _ => simp only [seq]; fun_prop
    | i + 2, ih =>
      have := ih i (by omega)
      have := ih (i + 1) (by omega)
      simp only [seq_add_two]
      fun_prop

/-! ## B. Gluing the two halves -/

variable (d g : ℕ) (z c₀ : ℝ)

/-- The left half. -/
def left (j : ℕ) : ℝ := seq z c₀ j

/-- The right half, solved from the site `d − 1`, with centre `d − 1 − c₀`. -/
def right (j : ℕ) : ℝ := seq z ((d : ℝ) - 1 - c₀) (d - 1 - j)

/-- The packet: the left half up to `g`, the right half from `g`. -/
def phi (j : ℕ) : ℝ :=
  if j ≤ g then left z c₀ j * right d z c₀ g else right d z c₀ j * left z c₀ g

/-- The Casoratian of the two halves at `g`. -/
def casoratian : ℝ :=
  left z c₀ g * right d z c₀ (g + 1) - left z c₀ (g + 1) * right d z c₀ g

variable {d g z c₀}

lemma left_rec (j : ℕ) :
    left z c₀ (j + 1) - (if 0 < j then left z c₀ (j - 1) else 0) =
      2 * (c₀ - j) / z * left z c₀ j := by
  rcases j with _ | j
  · simp [left, seq]
  · simp only [left, Nat.succ_pos, ite_true, Nat.add_sub_cancel, seq_add_two]
    push_cast
    ring

lemma right_rec {j : ℕ} (hj0 : 0 < j) (hj : j < d) :
    (if j + 1 < d then right d z c₀ (j + 1) else 0) - right d z c₀ (j - 1) =
      2 * (c₀ - j) / z * right d z c₀ j := by
  obtain ⟨i, rfl⟩ : ∃ i, d = j + 1 + i := ⟨d - j - 1, by omega⟩
  rcases i with _ | i
  · simp only [right, add_zero, lt_self_iff_false, ite_false,
      show j + 1 - 1 - (j - 1) = 1 by omega, show j + 1 - 1 - j = 0 by omega, seq_one]
    simp [seq]
    ring
  · simp only [right, show j + 1 < j + 1 + (i + 1) by omega, ite_true,
      show j + 1 + (i + 1) - 1 - (j + 1) = i by omega,
      show j + 1 + (i + 1) - 1 - (j - 1) = i + 2 by omega,
      show j + 1 + (i + 1) - 1 - j = i + 1 by omega, seq_add_two]
    push_cast
    ring

lemma phi_of_le {j : ℕ} (h : j ≤ g) : phi d g z c₀ j = left z c₀ j * right d z c₀ g := by
  simp [phi, h]

lemma phi_of_lt {j : ℕ} (h : g < j) : phi d g z c₀ j = right d z c₀ j * left z c₀ g := by
  simp [phi, show ¬ j ≤ g by omega]

/-- **Gluing.** If the Casoratian vanishes, the packet solves the recurrence at every site. -/
theorem glue_rec (hg : g + 1 < d) (hW : casoratian d g z c₀ = 0) {j : ℕ} (hj : j < d) :
    (if j + 1 < d then phi d g z c₀ (j + 1) else 0) -
        (if 0 < j then phi d g z c₀ (j - 1) else 0) =
      2 * (c₀ - j) / z * phi d g z c₀ j := by
  have hW' : right d z c₀ (g + 1) * left z c₀ g = left z c₀ (g + 1) * right d z c₀ g := by
    unfold casoratian at hW
    linarith
  have hl := left_rec (z := z) (c₀ := c₀) j
  rcases le_or_gt j g with h | h
  · have hp : phi d g z c₀ (j + 1) = left z c₀ (j + 1) * right d z c₀ g := by
      rcases Nat.lt_or_ge j g with h' | h'
      · exact phi_of_le (by omega)
      · rw [le_antisymm h h', phi_of_lt (by omega), hW']
    simp only [show j + 1 < d by omega, ↓reduceIte, hp, phi_of_le h]
    by_cases h0 : 0 < j
    · simp only [h0, ↓reduceIte, phi_of_le (show j - 1 ≤ g by omega)] at hl ⊢
      linear_combination right d z c₀ g * hl
    · simp only [h0, ↓reduceIte] at hl ⊢
      linear_combination right d z c₀ g * hl
  · have hr := right_rec (z := z) (c₀ := c₀) (show 0 < j by omega) hj
    have hm : phi d g z c₀ (j - 1) = right d z c₀ (j - 1) * left z c₀ g := by
      rcases Nat.lt_or_ge g (j - 1) with h' | h'
      · exact phi_of_lt h'
      · rw [phi_of_le h', show j - 1 = g by omega, mul_comm]
    simp only [show 0 < j by omega, ↓reduceIte, hm, phi_of_lt h]
    by_cases h1 : j + 1 < d
    · simp only [h1, ↓reduceIte, phi_of_lt (show g < j + 1 by omega)] at hr ⊢
      linear_combination left z c₀ g * hr
    · simp only [h1, ↓reduceIte] at hr ⊢
      linear_combination left z c₀ g * hr

end StarkPacket

end

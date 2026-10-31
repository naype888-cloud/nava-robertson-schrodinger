/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50f_ProperTimeBand

/-!
# D50g — Commuting words: the diagonal

Two words `A`, `B` that commute are two words on a diagonal: their steps add and the order does not
matter (a face diagonal is two words, a body diagonal three). Here the bookkeeping of that case: a
word is a list of axis steps, the cost of a word is the sum of the costs `δ k` of its letters, and
it depends only on how many times each axis occurs.

This is the commuting case and it is a definition, not a theorem about the flow. Time does not come
from here: it comes from the words that do not commute, each along its own vertex with its own
orthogonal `P_d` (`D50h`), where `τ_i²` is the Gram surplus of the pair `(T_i, P_i)` (`D50c`).

## Main results

- `WordDefect.wordDefect_append` : the defect of a concatenation is the sum of the defects.
- `WordDefect.wordDefect_perm` : the orders of a diagonal (`2` of a face, `3! = 6` of a body, as in
  Physlib #1987) all cost the same.
- `WordDefect.wordDefect_eq_sum_count` : `Σ_k (number of letters k) · δ_k`.
- `WordDefect.cubeDefect_pos_of_band` : on the cube, speeds in `Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)` give a
  positive defect on each axis, for every unit state.
- `WordDefect.wordProperTime_pos_of_band` : every non-empty word has a positive proper time.
- `WordDefect.faceDiagonal`, `WordDefect.bodyDiagonal` : two and three words on a diagonal.
-/

@[expose] public noncomputable section

open TransportPosition GroupVelocity VelocityBand PathGraph3DNRS ProperTimeAxis

namespace WordDefect

section General

variable {κ : Type*}

/-- The defect of a word: the sum of the defects `δ k` of its letters. -/
def wordDefect (δ : κ → ℝ) (w : List κ) : ℝ := (w.map δ).sum

@[simp] theorem wordDefect_nil (δ : κ → ℝ) : wordDefect δ [] = 0 := rfl

@[simp] theorem wordDefect_cons (δ : κ → ℝ) (a : κ) (w : List κ) :
    wordDefect δ (a :: w) = δ a + wordDefect δ w := by
  simp [wordDefect]

theorem wordDefect_append (δ : κ → ℝ) (w v : List κ) :
    wordDefect δ (w ++ v) = wordDefect δ w + wordDefect δ v := by
  simp [wordDefect]

/-- **Commuting words: every order costs the same.** The `2` orders of a face diagonal and the
`3! = 6` orders of a body diagonal (`card_twoStepWords_fiber`, `card_threeStepWords_fiber` of
Physlib #1987) are permutations of one word, and a permutation does not change the cost. -/
theorem wordDefect_perm (δ : κ → ℝ) {w v : List κ} (h : w.Perm v) :
    wordDefect δ w = wordDefect δ v := by
  simp only [wordDefect]
  exact (h.map δ).sum_eq

theorem wordDefect_nonneg {δ : κ → ℝ} (h : ∀ k, 0 ≤ δ k) (w : List κ) : 0 ≤ wordDefect δ w := by
  induction w with
  | nil => simp
  | cons a w ih => rw [wordDefect_cons]; exact add_nonneg (h a) ih

/-- A letter of the word costs at most the whole word. -/
theorem le_wordDefect {δ : κ → ℝ} (h : ∀ k, 0 ≤ δ k) {w : List κ} {a : κ} (ha : a ∈ w) :
    δ a ≤ wordDefect δ w := by
  induction w with
  | nil => simp at ha
  | cons b w ih =>
    rw [wordDefect_cons]
    rcases List.mem_cons.mp ha with rfl | hm
    · linarith [wordDefect_nonneg h w]
    · linarith [ih hm, h b]

theorem wordDefect_pos {δ : κ → ℝ} (h : ∀ k, 0 < δ k) {w : List κ} (hw : w ≠ []) :
    0 < wordDefect δ w := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w hw
  exact lt_of_lt_of_le (h a) (le_wordDefect (fun k => (h k).le) ha)

/-- The defect depends only on the multiplicities of the letters. -/
theorem wordDefect_eq_sum_count [Fintype κ] [DecidableEq κ] (δ : κ → ℝ) (w : List κ) :
    wordDefect δ w = ∑ k, (w.count k : ℝ) * δ k := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [wordDefect_cons, ih]
    have h : ∀ k, (((a :: w).count k : ℕ) : ℝ) * δ k =
        (w.count k : ℝ) * δ k + (if k = a then δ k else 0) := by
      intro k
      by_cases hk : k = a
      · subst hk; simp; ring
      · simp [hk, Ne.symm hk]
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a]
    simp [add_comm]

end General

section Cube

variable {dx dy dz : ℕ}

/-- The defect of each axis of the cube: `τ_x²`, `τ_y²`, `τ_z²` of `D50c`. -/
def cubeDefect (dx dy dz : ℕ) (Φ : H3D dx dy dz) : Fin 3 → ℝ :=
  ![properTimeAxis (eX dx dy dz) Φ ^ 2, properTimeAxis (eY dx dy dz) Φ ^ 2,
    properTimeAxis (eZ dx dy dz) Φ ^ 2]

/-- The proper time of a word of the cube: the square root of the sum of the defects. -/
def wordProperTime (dx dy dz : ℕ) (Φ : H3D dx dy dz) (w : List (Fin 3)) : ℝ :=
  √(wordDefect (cubeDefect dx dy dz Φ) w)

theorem cubeDefect_nonneg (Φ : H3D dx dy dz) (k : Fin 3) : 0 ≤ cubeDefect dx dy dz Φ k := by
  fin_cases k <;> simp [cubeDefect] <;> positivity

theorem wordProperTime_sq (Φ : H3D dx dy dz) (w : List (Fin 3)) :
    wordProperTime dx dy dz Φ w ^ 2 = wordDefect (cubeDefect dx dy dz Φ) w :=
  Real.sq_sqrt (wordDefect_nonneg (cubeDefect_nonneg Φ) w)

/-- **A letter does not exceed its word**: the proper time of the word is at least that of each of
its steps. -/
theorem le_wordProperTime_sq (Φ : H3D dx dy dz) {w : List (Fin 3)} {a : Fin 3} (ha : a ∈ w) :
    cubeDefect dx dy dz Φ a ≤ wordProperTime dx dy dz Φ w ^ 2 := by
  rw [wordProperTime_sq]
  exact le_wordDefect (cubeDefect_nonneg Φ) ha

/-- **On the cube, a speed in the band on each axis gives a positive defect on each axis**, for
every unit state. -/
theorem cubeDefect_pos_of_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy)
    (hbz : |velocityZ Φ| ∈ Ϙ dz) (k : Fin 3) : 0 < cubeDefect dx dy dz Φ k := by
  have a := properTimeAxis_pos_of_band hx (eX dx dy dz) hΦ hbx
  have b := properTimeAxis_pos_of_band hy (eY dx dy dz) hΦ hby
  have c := properTimeAxis_pos_of_band hz (eZ dx dy dz) hΦ hbz
  fin_cases k <;> simp [cubeDefect] <;> positivity

/-- **Every non-empty word has a positive proper time.** -/
theorem wordProperTime_pos_of_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy)
    (hbz : |velocityZ Φ| ∈ Ϙ dz) {w : List (Fin 3)} (hw : w ≠ []) :
    0 < wordProperTime dx dy dz Φ w :=
  Real.sqrt_pos.mpr
    (wordDefect_pos (cubeDefect_pos_of_band hx hy hz hΦ hbx hby hbz) hw)

/-- **A face diagonal `xy` costs two defects.** -/
theorem faceDiagonal (Φ : H3D dx dy dz) :
    wordDefect (cubeDefect dx dy dz Φ) [0, 1] =
      properTimeAxis (eX dx dy dz) Φ ^ 2 + properTimeAxis (eY dx dy dz) Φ ^ 2 := by
  simp [cubeDefect]

/-- **A body diagonal `xyz` costs three defects.** -/
theorem bodyDiagonal (Φ : H3D dx dy dz) :
    wordDefect (cubeDefect dx dy dz Φ) [0, 1, 2] =
      properTimeAxis (eX dx dy dz) Φ ^ 2 + properTimeAxis (eY dx dy dz) Φ ^ 2 +
        properTimeAxis (eZ dx dy dz) Φ ^ 2 := by
  simp [cubeDefect, add_assoc]

end Cube

end WordDefect

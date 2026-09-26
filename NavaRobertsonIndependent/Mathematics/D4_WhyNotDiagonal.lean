/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D3_PathGraph

/-!
# D4 — Why not a diagonal step

`T_d` moves by minimal steps of the path (`D3`). A diagonal step, changing several coordinates
at once, is never an alternative:

1. on a cube `Fin dx × Fin dy × Fin dz` the orthogonal step has length `1`, the double
   diagonal `√2`, the triple diagonal `√3`, so the orthogonal step is strictly shortest;
2. with a single axis (`dy = dz = 1`) the diagonal relations are empty: a diagonal presupposes
   two axes.

## Main results

- `OrthogonalStep.minimal_adjacency_is_orthogonal` : no diagonal step is as short as an
  orthogonal one.
- `DiagonalNeedsTwoAxes.no_diagonal_of_one_axis` : with one axis there is no diagonal step.
-/

@[expose] public noncomputable section

namespace PathGraph3D

/-- A site of the cube: a product of three rows. -/
abbrev Site3D (dx dy dz : ℕ) := Fin dx × Fin dy × Fin dz

/-- Orthogonal adjacency: one coordinate changes, by a minimal step. -/
def Adj3D {dx dy dz : ℕ} (p q : Site3D dx dy dz) : Prop :=
  (TransportPosition.MinStep p.1 q.1 ∧ p.2 = q.2) ∨
    (p.1 = q.1 ∧ TransportPosition.MinStep p.2.1 q.2.1 ∧ p.2.2 = q.2.2) ∨
    (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ TransportPosition.MinStep p.2.2 q.2.2)

end PathGraph3D

/-! ## 1. Pythagoras: the orthogonal step is strictly shortest -/

namespace OrthogonalStep

open PathGraph3D
open TransportPosition

/-- Euclidean distance between two sites, coordinates cast to `ℝ`. -/
noncomputable def dist3D {dx dy dz : ℕ} (p q : Site3D dx dy dz) : ℝ :=
  Real.sqrt (
    ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 +
    ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
    ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2)

/-- Two coordinates at a minimal step differ by `±1`. -/
theorem minStep_sq_diff_eq_one {d : ℕ} {i j : Fin d} (h : MinStep i j) :
    ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 1 := by
  rcases h with h | h
  · have hij : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hij]; ring
  · have hji : (i.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hji]; ring

theorem eq_sq_diff_eq_zero {d : ℕ} {i j : Fin d} (h : i = j) :
    ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 0 := by
  rw [h]; ring

/-! ### Orthogonal step: length `1` -/

theorem dist3D_eq_one_of_Adj3D
    {dx dy dz : ℕ} {p q : Site3D dx dy dz} (h : Adj3D p q) :
    dist3D p q = 1 := by
  unfold dist3D
  rcases h with ⟨hx, hyz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 :=
      eq_sq_diff_eq_zero (congrArg Prod.fst hyz)
    have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 :=
      eq_sq_diff_eq_zero (congrArg Prod.snd hyz)
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [minStep_sq_diff_eq_one hx, hy0, hz0]; ring
    rw [hsum, Real.sqrt_one]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hz
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [hx0, minStep_sq_diff_eq_one hy, hz0]; ring
    rw [hsum, Real.sqrt_one]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hy
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [hx0, hy0, minStep_sq_diff_eq_one hz]; ring
    rw [hsum, Real.sqrt_one]

/-! ### Double diagonal: length `√2` -/

/-- A diagonal step in two axes; the third coordinate is fixed. -/
def DoubleDiagonal {dx dy dz : ℕ} (p q : Site3D dx dy dz) : Prop :=
  (MinStep p.1 q.1 ∧ MinStep p.2.1 q.2.1 ∧ p.2.2 = q.2.2) ∨
  (MinStep p.1 q.1 ∧ p.2.1 = q.2.1 ∧ MinStep p.2.2 q.2.2) ∨
  (p.1 = q.1 ∧ MinStep p.2.1 q.2.1 ∧ MinStep p.2.2 q.2.2)

theorem dist3D_eq_sqrt_two_of_doubleDiagonal
    {dx dy dz : ℕ} {p q : Site3D dx dy dz} (h : DoubleDiagonal p q) :
    dist3D p q = Real.sqrt 2 := by
  unfold dist3D
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hz
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [minStep_sq_diff_eq_one hx, minStep_sq_diff_eq_one hy, hz0]; ring
    rw [hsum]
  · have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hy
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [minStep_sq_diff_eq_one hx, hy0, minStep_sq_diff_eq_one hz]; ring
    rw [hsum]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [hx0, minStep_sq_diff_eq_one hy, minStep_sq_diff_eq_one hz]; ring
    rw [hsum]

/-! ### Triple diagonal: length `√3` -/

/-- A diagonal step in all three axes. -/
def TripleDiagonal {dx dy dz : ℕ} (p q : Site3D dx dy dz) : Prop :=
  MinStep p.1 q.1 ∧ MinStep p.2.1 q.2.1 ∧ MinStep p.2.2 q.2.2

theorem dist3D_eq_sqrt_three_of_tripleDiagonal
    {dx dy dz : ℕ} {p q : Site3D dx dy dz} (h : TripleDiagonal p q) :
    dist3D p q = Real.sqrt 3 := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold dist3D
  have hsum :
      ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
          ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 3 := by
    rw [minStep_sq_diff_eq_one hx, minStep_sq_diff_eq_one hy,
      minStep_sq_diff_eq_one hz]; ring
  rw [hsum]

/-! ### The orthogonal step is shortest -/

theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ), h2]

theorem one_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ), h3]

/-- The orthogonal step is strictly shorter than a double diagonal. -/
theorem dist_orthogonal_lt_doubleDiagonal
    {dx dy dz : ℕ} {p q p' q' : Site3D dx dy dz}
    (hOrt : Adj3D p q) (hDiag : DoubleDiagonal p' q') :
    dist3D p q < dist3D p' q' := by
  rw [dist3D_eq_one_of_Adj3D hOrt, dist3D_eq_sqrt_two_of_doubleDiagonal hDiag]
  exact one_lt_sqrt_two

/-- The orthogonal step is strictly shorter than a triple diagonal. -/
theorem dist_orthogonal_lt_tripleDiagonal
    {dx dy dz : ℕ} {p q p' q' : Site3D dx dy dz}
    (hOrt : Adj3D p q) (hDiag : TripleDiagonal p' q') :
    dist3D p q < dist3D p' q' := by
  rw [dist3D_eq_one_of_Adj3D hOrt, dist3D_eq_sqrt_three_of_tripleDiagonal hDiag]
  exact one_lt_sqrt_three

/-- No diagonal step is as short as an orthogonal step. -/
theorem minimal_adjacency_is_orthogonal
    {dx dy dz : ℕ} {p q p' q' : Site3D dx dy dz}
    (hOrt : Adj3D p q)
    (hDiag : DoubleDiagonal p' q' ∨ TripleDiagonal p' q') :
    dist3D p q < dist3D p' q' := by
  rcases hDiag with hD | hD
  · exact dist_orthogonal_lt_doubleDiagonal hOrt hD
  · exact dist_orthogonal_lt_tripleDiagonal hOrt hD

end OrthogonalStep

/-! ## 2. With one axis, the diagonal relations are empty -/

namespace DiagonalNeedsTwoAxes

open PathGraph3D
open OrthogonalStep

/-- `Fin 1` has no minimal step. -/
theorem not_minStep_fin_one (i j : Fin 1) :
    ¬ TransportPosition.MinStep i j := by
  unfold TransportPosition.MinStep
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- With one axis there is no double diagonal. -/
theorem not_doubleDiagonal_of_one_axis
    {dx : ℕ} (p q : Site3D dx 1 1) : ¬ DoubleDiagonal p q := by
  unfold DoubleDiagonal
  rintro (⟨_, hy, _⟩ | ⟨_, _, hz⟩ | ⟨_, hy, _⟩)
  · exact not_minStep_fin_one p.2.1 q.2.1 hy
  · exact not_minStep_fin_one p.2.2 q.2.2 hz
  · exact not_minStep_fin_one p.2.1 q.2.1 hy

/-- With one axis there is no triple diagonal. -/
theorem not_tripleDiagonal_of_one_axis
    {dx : ℕ} (p q : Site3D dx 1 1) : ¬ TripleDiagonal p q := by
  unfold TripleDiagonal
  rintro ⟨_, hy, _⟩
  exact not_minStep_fin_one p.2.1 q.2.1 hy

/-- With one axis there is no diagonal step at all. -/
theorem no_diagonal_of_one_axis
    {dx : ℕ} (p q : Site3D dx 1 1) :
    ¬ (DoubleDiagonal p q ∨ TripleDiagonal p q) := by
  rintro (h | h)
  · exact not_doubleDiagonal_of_one_axis p q h
  · exact not_tripleDiagonal_of_one_axis p q h

end DiagonalNeedsTwoAxes

end

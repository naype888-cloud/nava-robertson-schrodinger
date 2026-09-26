/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D3_PathGraph
public import NavaRobertsonIndependent.Mathematics.D7_Niven

/-!
# D13 — The first combinatorial rupture is `d = 4`

Saturation of Robertson–Schrödinger on the path fails exactly when the path acquires its first
interior edge, an edge between two non-terminal vertices, and both happen at `d = 4`. The
spectral side is Niven (`D7`); the combinatorial side uses no spectral equation.

## Main results

- `FirstRupture.hasInteriorEdge_iff_four_le` : the path has an interior edge iff `4 ≤ d`.
- `FirstRupture.hasInteriorEdge_iff_pathRupture` : interior edge iff no saturation.
- `FirstRupture.isFirstRupture_iff_eq_four` : the first rupture is `d = 4`.
-/

@[expose] public section

namespace FirstRupture

open SimpleGraph

/-- The saturation equation of the path, as a predicate (`Gnomon.saturation_iff`). -/
def PathSaturation (d : ℕ) : Prop :=
  Real.cos (Real.pi / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4

/-- Rupture: the saturation equation fails. -/
def PathRupture (d : ℕ) : Prop := ¬ PathSaturation d

/-- For `d ≥ 2`, rupture holds iff `4 ≤ d`. -/
theorem pathRupture_iff_four_le (d : ℕ) (hd : 2 ≤ d) :
    PathRupture d ↔ 4 ≤ d := by
  unfold PathRupture PathSaturation
  rw [Gnomon.saturation_iff d hd]
  omega

/-- `d = 4` is a rupture. -/
theorem pathRupture_four : PathRupture 4 := by
  exact (pathRupture_iff_four_le 4 (by norm_num)).2 (by norm_num)

/-- A non-terminal vertex of the path. -/
def InteriorVertex {d : ℕ} (i : Fin d) : Prop :=
  0 < i.val ∧ i.val + 1 < d

/-- Two non-terminal vertices are adjacent. -/
def HasInteriorEdge (d : ℕ) : Prop :=
  ∃ i j : Fin d,
    InteriorVertex i ∧ InteriorVertex j ∧
      (SimpleGraph.pathGraph d).Adj i j

/-- The path has an interior edge iff `4 ≤ d`; pure combinatorics. -/
theorem hasInteriorEdge_iff_four_le (d : ℕ) :
    HasInteriorEdge d ↔ 4 ≤ d := by
  constructor
  · rintro ⟨i, j, hi, hj, hadj⟩
    rcases hi with ⟨hi0, hiend⟩
    rcases hj with ⟨hj0, hjend⟩
    rw [SimpleGraph.pathGraph_adj] at hadj
    rcases hadj with hij | hji <;> omega
  · intro hd
    let i : Fin d := ⟨1, by omega⟩
    let j : Fin d := ⟨2, by omega⟩
    refine ⟨i, j, ?_, ?_, ?_⟩
    · simp [InteriorVertex, i]
      omega
    · simp [InteriorVertex, j]
      omega
    · rw [SimpleGraph.pathGraph_adj]
      exact Or.inl rfl

/-- For `d ≥ 2`, an interior edge exists iff saturation fails. -/
theorem hasInteriorEdge_iff_pathRupture (d : ℕ) (hd : 2 ≤ d) :
    HasInteriorEdge d ↔ PathRupture d := by
  exact (hasInteriorEdge_iff_four_le d).trans
    (pathRupture_iff_four_le d hd).symm

/-- `d` is a rupture and no smaller admissible dimension is. -/
def IsFirstRupture (d : ℕ) : Prop :=
  2 ≤ d ∧ PathRupture d ∧
    ∀ n : ℕ, 2 ≤ n → PathRupture n → d ≤ n

/-- The first rupture is `d = 4`. -/
theorem isFirstRupture_iff_eq_four (d : ℕ) :
    IsFirstRupture d ↔ d = 4 := by
  constructor
  · rintro ⟨hd2, hdR, hmin⟩
    have h4d : 4 ≤ d := (pathRupture_iff_four_le d hd2).1 hdR
    have hd4 : d ≤ 4 := hmin 4 (by norm_num) pathRupture_four
    omega
  · rintro rfl
    refine ⟨by norm_num, pathRupture_four, ?_⟩
    intro n hn2 hnR
    exact (pathRupture_iff_four_le n hn2).1 hnR

end FirstRupture

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50j_DiagonalWords

/-!
# D50k — The sum of the times of a word, for every state

`D50g` adds the times `τ_a²` of the letters of a word, and `D50f` bounds each of them for every
unit state `Φ` of the open cube by the tension deficit of its axis:
`gapK d · (τ_a² − defectGram d)² ≤ 2048 (2/(d−1) − ⟨K⟩_Φ)`. Here the two together: for every word,
the sum of its times is within the sum of the tension deficits of its letters of the sum of the
rest values `defectGram d_a`, and it is exactly that sum when every axis of the word has maximal
tension.

## Main results

- `WordDefectBand.cube_axis_band` : `|τ_a² − defectGram d_a| ≤ ε_a` for the three axes.
- `WordDefectBand.wordDefect_band` : `|Σ_{a ∈ w} τ_a² − Σ_{a ∈ w} defectGram d_a| ≤ Σ_{a ∈ w} ε_a`.
- `WordDefectBand.wordDefect_eq_of_maxTension` : with maximal tension on the three axes, the sum
  of the times of the word is the sum of the `defectGram`.
-/

@[expose] public noncomputable section

open TransportPosition NearMaxTension PathGraph3DNRS BandWidth SpectralExtremal ProperTimeAxis
  ProperTimeBand WordDefect GramStep

namespace WordDefectBand

section General

variable {κ : Type*}

/-- If each letter is within `ε k` of `g k`, the word is within the sum of the `ε`. -/
theorem abs_wordDefect_sub_le {δ g ε : κ → ℝ} (h : ∀ k, |δ k - g k| ≤ ε k) (w : List κ) :
    |wordDefect δ w - wordDefect g w| ≤ wordDefect ε w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [wordDefect_cons, wordDefect_cons, wordDefect_cons]
    calc |δ a + wordDefect δ w - (g a + wordDefect g w)|
        = |(δ a - g a) + (wordDefect δ w - wordDefect g w)| := by ring_nf
      _ ≤ |δ a - g a| + |wordDefect δ w - wordDefect g w| := abs_add_le _ _
      _ ≤ ε a + wordDefect ε w := add_le_add (h a) ih

theorem wordDefect_zero (w : List κ) : wordDefect (0 : κ → ℝ) w = 0 := by
  induction w with
  | nil => simp
  | cons a w ih => rw [wordDefect_cons, ih]; simp

end General

section Cube

variable {dx dy dz : ℕ}

/-- The value of the time of an axis at saturation: `defectGram d`. -/
def cubeGram (dx dy dz : ℕ) : Fin 3 → ℝ := ![defectGram dx, defectGram dy, defectGram dz]

/-- The width of the band of an axis: `√(2048 · deficit / gapK)`. -/
def cubeEps (dx dy dz : ℕ) (Φ : H3D dx dy dz) : Fin 3 → ℝ :=
  ![√(2048 * (2 / ((dx : ℝ) - 1) - tensionG (TX dx dy dz) (PX dx dy dz) Φ) / gapK dx),
    √(2048 * (2 / ((dy : ℝ) - 1) - tensionG (TY dx dy dz) (PY dx dy dz) Φ) / gapK dy),
    √(2048 * (2 / ((dz : ℝ) - 1) - tensionG (TZ dx dy dz) (PZ dx dy dz) Φ) / gapK dz)]

theorem abs_le_of_band {d : ℕ} (hd : 2 ≤ d) {x D : ℝ} (h : gapK d * x ^ 2 ≤ 2048 * D) :
    |x| ≤ √(2048 * D / gapK d) := by
  apply Real.abs_le_sqrt
  rw [le_div_iff₀ (gapK_pos hd)]
  linarith

/-- **The time of each axis of the cube is within its band of `defectGram d`**, for every unit
state. -/
theorem cube_axis_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (k : Fin 3) :
    |cubeDefect dx dy dz Φ k - cubeGram dx dy dz k| ≤ cubeEps dx dy dz Φ k := by
  obtain ⟨bx, by', bz⟩ := properTime_cube_band hx hy hz hΦ
  fin_cases k
  · simpa [cubeDefect, cubeGram, cubeEps] using abs_le_of_band hx bx
  · simpa [cubeDefect, cubeGram, cubeEps] using abs_le_of_band hy by'
  · simpa [cubeDefect, cubeGram, cubeEps] using abs_le_of_band hz bz

/-- **The sum of the times of a word, for every unit state of the open cube**, is within the sum of
the widths of its letters of the sum of the `defectGram`. -/
theorem wordDefect_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (w : List (Fin 3)) :
    |wordDefect (cubeDefect dx dy dz Φ) w - wordDefect (cubeGram dx dy dz) w| ≤
      wordDefect (cubeEps dx dy dz Φ) w :=
  abs_wordDefect_sub_le (cube_axis_band hx hy hz hΦ) w

/-- **With maximal tension on the three axes the sum of the times of a word is the sum of the
`defectGram`.** -/
theorem wordDefect_eq_of_maxTension (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    {Φ : H3D dx dy dz} (hΦ : ‖Φ‖ = 1)
    (tx : tensionG (TX dx dy dz) (PX dx dy dz) Φ = 2 / ((dx : ℝ) - 1))
    (ty : tensionG (TY dx dy dz) (PY dx dy dz) Φ = 2 / ((dy : ℝ) - 1))
    (tz : tensionG (TZ dx dy dz) (PZ dx dy dz) Φ = 2 / ((dz : ℝ) - 1)) (w : List (Fin 3)) :
    wordDefect (cubeDefect dx dy dz Φ) w = wordDefect (cubeGram dx dy dz) w := by
  have e : cubeEps dx dy dz Φ = 0 := by
    funext k
    fin_cases k <;> simp [cubeEps, tx, ty, tz]
  have h := wordDefect_band hx hy hz hΦ w
  have h0 : wordDefect (cubeEps dx dy dz Φ) w = 0 := by
    rw [e]; exact wordDefect_zero w
  rw [h0] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end Cube

end WordDefectBand

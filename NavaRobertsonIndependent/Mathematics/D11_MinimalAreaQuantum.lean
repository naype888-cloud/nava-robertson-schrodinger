/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D10_Certificate

/-!
# D11 — The minimal area quantum

`geometricGap 4` is the first positive gap of the tail `d ≥ 4`, and its square
`areaQuantum = δ(4)²` is the first area quantum. By monotonicity (`D9`) no resolution area
`δ(d)²`, `d ≥ 4`, is below it. The statement is dimensionless; multiplying by any nonnegative
scale preserves the bound.

## Main results

- `MinimalAreaQuantum.areaQuantum_pos` : `δ(4)² > 0`.
- `MinimalAreaQuantum.areaQuantum_le_resolutionArea` : `δ(4)² ≤ δ(d)²` for `d ≥ 4`.
- `MinimalAreaQuantum.areaCertificate` : the certificate is inhabited.
-/

@[expose] public noncomputable section

namespace MinimalAreaQuantum

open Gnomon

/-- The area quantum `δ(4)²` of the tail `d ≥ 4`. -/
def areaQuantum : ℝ :=
  geometricGap 4 ^ 2

/-- The minimal square, the same quantity as `areaQuantum`. -/
def minimalSquare : ℝ :=
  areaQuantum

/-- The resolution area `δ(d)²`. -/
def resolutionArea (d : ℕ) : ℝ :=
  geometricGap d ^ 2

/-- `minimalSquare = areaQuantum`. -/
theorem minimalSquare_eq_areaQuantum :
    minimalSquare = areaQuantum := by
  rfl

/-- The minimal square is the resolution area of `H_4`. -/
theorem minimalSquare_eq_resolutionArea_four :
    minimalSquare = resolutionArea 4 := by
  rfl

/-- The area quantum is the resolution area of `H_4`. -/
theorem areaQuantum_eq_resolutionArea_four :
    areaQuantum = resolutionArea 4 := by
  rfl

/-- The area quantum is positive. -/
theorem areaQuantum_pos : 0 < areaQuantum := by
  unfold areaQuantum
  have hδ : 0 < geometricGap 4 :=
    geometricGap_pos_of_four_le 4 (by omega)
  positivity

/-- The minimal square is positive. -/
theorem minimalSquare_pos : 0 < minimalSquare := by
  simpa [minimalSquare] using areaQuantum_pos

/-- Every resolution area in `d ≥ 4` is at least the area quantum. -/
theorem areaQuantum_le_resolutionArea (d : ℕ) (hd : 4 ≤ d) :
    areaQuantum ≤ resolutionArea d := by
  unfold areaQuantum resolutionArea
  exact geometricGap_sq_four_le d hd

/-- Every resolution area in `d ≥ 4` is at least the minimal square. -/
theorem minimalSquare_le_resolutionArea (d : ℕ) (hd : 4 ≤ d) :
    minimalSquare ≤ resolutionArea d := by
  simpa [minimalSquare] using areaQuantum_le_resolutionArea d hd

/-- No resolution area in `d ≥ 4` is below the area quantum. -/
theorem not_resolutionArea_lt_areaQuantum
    (d : ℕ) (hd : 4 ≤ d) :
    ¬ resolutionArea d < areaQuantum := by
  exact not_lt.mpr (areaQuantum_le_resolutionArea d hd)

/-- No resolution area in `d ≥ 4` is below the minimal square. -/
theorem not_resolutionArea_lt_minimalSquare
    (d : ℕ) (hd : 4 ≤ d) :
    ¬ resolutionArea d < minimalSquare := by
  simpa [minimalSquare] using not_resolutionArea_lt_areaQuantum d hd

/-- A threshold below the minimal square is below every resolution area in `d ≥ 4`. -/
theorem lt_resolutionArea_of_lt_minimalSquare
    (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : ε < minimalSquare) :
    ε < resolutionArea d :=
  lt_of_lt_of_le hε (minimalSquare_le_resolutionArea d hd)

/-- A nonnegative scale preserves the bound. -/
theorem scaled_areaQuantum_le
    (scale : ℝ) (hesc : 0 ≤ scale) (d : ℕ) (hd : 4 ≤ d) :
    scale * areaQuantum ≤ scale * resolutionArea d :=
  mul_le_mul_of_nonneg_left (areaQuantum_le_resolutionArea d hd) hesc

/-- A nonnegative scale preserves the bound, for the minimal square. -/
theorem scaled_minimalSquare_le
    (scale : ℝ) (hesc : 0 ≤ scale) (d : ℕ) (hd : 4 ≤ d) :
    scale * minimalSquare ≤ scale * resolutionArea d :=
by
  simpa [minimalSquare] using scaled_areaQuantum_le scale hesc d hd

/-- A positive scale keeps the area quantum positive. -/
theorem scaled_areaQuantum_pos
    (scale : ℝ) (hesc : 0 < scale) :
    0 < scale * areaQuantum :=
  mul_pos hesc areaQuantum_pos

/-- A positive scale keeps the minimal square positive. -/
theorem scaled_minimalSquare_pos
    (scale : ℝ) (hesc : 0 < scale) :
    0 < scale * minimalSquare :=
by
  simpa [minimalSquare] using scaled_areaQuantum_pos scale hesc

/-- The certificate of the area quantum. -/
structure AreaCertificate where
  quantum_pos : 0 < areaQuantum
  quantum_le : ∀ d : ℕ, 4 ≤ d → areaQuantum ≤ resolutionArea d
  not_lt_quantum : ∀ d : ℕ, 4 ≤ d → ¬ resolutionArea d < areaQuantum
  scaled_quantum_le :
    ∀ scale : ℝ, 0 ≤ scale →
      ∀ d : ℕ, 4 ≤ d →
        scale * areaQuantum ≤ scale * resolutionArea d

theorem areaCertificate :
    Nonempty AreaCertificate :=
  ⟨{ quantum_pos := areaQuantum_pos
     quantum_le := areaQuantum_le_resolutionArea
     not_lt_quantum := not_resolutionArea_lt_areaQuantum
     scaled_quantum_le := scaled_areaQuantum_le }⟩

end MinimalAreaQuantum

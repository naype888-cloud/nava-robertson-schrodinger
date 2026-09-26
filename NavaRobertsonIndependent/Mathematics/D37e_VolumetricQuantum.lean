/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D11_MinimalAreaQuantum
public import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle

/-!
# D37e — The volumetric quantum

Each axis carries its dimensional quantum `δ(d) = C_Nava(d) − 1` (`D25`), with
`θ_NRS(d) = arccos (1 / (1 + δ(d)))`. The volumetric quantum of the cube is
`𝒱(dx, dy, dz) = δ(dx) δ(dy) δ(dz)`; adding sites never cancels it.

## Main results

- `VolumetricQuantum.volQuantum_eq_zero_iff` : `𝒱 = 0` iff some axis has `2` or `3` sites.
- `VolumetricQuantum.volQuantum_certificate` : from `4 × 4 × 4`, `δ(4)³ ≤ 𝒱 < δ_∞³`, strictly
  increasing in each axis.
- `VolumetricQuantum.volQuantum_four_sq` : `𝒱(4, 4, 4)² = (δ(4)²)³`, the area quantum of `D11`.
-/

@[expose] public noncomputable section

open Real Gnomon DimensionalQuantum MinimalAreaQuantum NRSAngle NRSInequality

namespace VolumetricQuantum

/-- The linear quantum of an axis fixes its NRS angle: `θ_NRS(d) = arccos (1 / (1 + δ(d)))`. -/
theorem angleNRS_eq_dimQuantum {d : ℕ} (hd : 2 ≤ d) :
    angleNRS d = arccos (1 / (1 + dimQuantum d)) := by
  rw [angleNRS_eq hd, dimQuantum, ← CoherenceConstant_eq_one_add_geometricGap]

theorem dimQuantum_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ dimQuantum d := geometricGap_nonneg hd

/-- The linear quantum at the first rupture, in closed form. -/
theorem dimQuantum_four : dimQuantum 4 = Real.sqrt ((99 - 42 * Real.sqrt 5) / 5) - 1 := by
  rw [dimQuantum, geometricGap, CoherenceConstant, CoherenceConstantSq_four_eq]

/-- **The volumetric quantum** of the cube `dx × dy × dz`. -/
def volQuantum (dx dy dz : ℕ) : ℝ := dimQuantum dx * dimQuantum dy * dimQuantum dz

variable {dx dy dz : ℕ}

theorem volQuantum_nonneg (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    0 ≤ volQuantum dx dy dz :=
  mul_nonneg (mul_nonneg (dimQuantum_nonneg hx) (dimQuantum_nonneg hy)) (dimQuantum_nonneg hz)

/-- **It vanishes only at a seed axis.** -/
theorem volQuantum_eq_zero_iff (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    volQuantum dx dy dz = 0 ↔
      (dx = 2 ∨ dx = 3) ∨ (dy = 2 ∨ dy = 3) ∨ (dz = 2 ∨ dz = 3) := by
  rw [volQuantum, mul_eq_zero, mul_eq_zero, dimQuantum_eq_zero_iff hx,
    dimQuantum_eq_zero_iff hy, dimQuantum_eq_zero_iff hz, or_assoc]

theorem volQuantum_pos (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    0 < volQuantum dx dy dz :=
  mul_pos (mul_pos (dimQuantum_pos hx) (dimQuantum_pos hy)) (dimQuantum_pos hz)

/-- **Floor.** With at least `4` sites per axis, the volumetric quantum is at least `δ(4)³`. -/
theorem volQuantum_floor (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    dimQuantum 4 ^ 3 ≤ volQuantum dx dy dz := by
  have h4 := (dimQuantum_pos (le_refl 4)).le
  have ax := dimQuantum_four_le hx; have ay := dimQuantum_four_le hy
  have az := dimQuantum_four_le hz
  rw [volQuantum, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul ax ay h4 (h4.trans ax)) az h4
    (mul_nonneg (h4.trans ax) (h4.trans ay))

/-- **Ceiling.** It stays strictly below `δ_∞³`, which no cube reaches. -/
theorem volQuantum_lt_ceiling (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    volQuantum dx dy dz < deltaInf ^ 3 := by
  have px := (dimQuantum_pos hx).le; have py := (dimQuantum_pos hy).le
  have tx := dimQuantum_lt_deltaInf hx; have ty := dimQuantum_lt_deltaInf hy
  have tz := dimQuantum_lt_deltaInf hz
  rw [volQuantum, pow_three, ← mul_assoc]
  exact mul_lt_mul'' (mul_lt_mul'' tx ty px py) tz (mul_nonneg px py) (dimQuantum_pos hz).le

/-- On the cube `d × d × d` the volumetric quantum is `δ(d)³`. -/
theorem volQuantum_cube (d : ℕ) : volQuantum d d d = dimQuantum d ^ 3 := by
  rw [volQuantum]; ring

/-- **At the first rupture** `4 × 4 × 4`: `𝒱 = (√((99 − 42√5)/5) − 1)³`. -/
theorem volQuantum_four :
    volQuantum 4 4 4 = (Real.sqrt ((99 - 42 * Real.sqrt 5) / 5) - 1) ^ 3 := by
  rw [volQuantum_cube, dimQuantum_four]

/-- Volume and area quanta at the first rupture: `𝒱(4,4,4)² = (area quantum)³`. -/
theorem volQuantum_four_sq :
    volQuantum 4 4 4 ^ 2 = areaQuantum ^ 3 := by
  rw [volQuantum_cube, areaQuantum, dimQuantum]; ring

/-- Adding sites along `x` strictly enlarges the volumetric quantum. -/
theorem volQuantum_strictMono_x {dx' : ℕ} (hx : 4 ≤ dx) (h : dx < dx') (hy : 4 ≤ dy)
    (hz : 4 ≤ dz) : volQuantum dx dy dz < volQuantum dx' dy dz := by
  unfold volQuantum
  have := dimQuantum_strictMonoOn hx h
  have p := mul_pos (dimQuantum_pos hy) (dimQuantum_pos hz)
  nlinarith [mul_lt_mul_of_pos_right this p]

theorem volQuantum_strictMono_y {dy' : ℕ} (hx : 4 ≤ dx) (hy : 4 ≤ dy) (h : dy < dy')
    (hz : 4 ≤ dz) : volQuantum dx dy dz < volQuantum dx dy' dz := by
  unfold volQuantum
  have := dimQuantum_strictMonoOn hy h
  have p := mul_pos (dimQuantum_pos hx) (dimQuantum_pos hz)
  nlinarith [mul_lt_mul_of_pos_right this p]

theorem volQuantum_strictMono_z {dz' : ℕ} (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz)
    (h : dz < dz') : volQuantum dx dy dz < volQuantum dx dy dz' := by
  unfold volQuantum
  have := dimQuantum_strictMonoOn hz h
  have p := mul_pos (dimQuantum_pos hx) (dimQuantum_pos hy)
  nlinarith [mul_lt_mul_of_pos_right this p]

/-- **Certificate of the volumetric quantum.** Zero only at a seed axis; from `4 × 4 × 4` on,
positive, at least `δ(4)³`, strictly below `δ_∞³`, strictly increasing in each axis. -/
theorem volQuantum_certificate (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    0 < volQuantum dx dy dz ∧
      dimQuantum 4 ^ 3 ≤ volQuantum dx dy dz ∧
      volQuantum dx dy dz < deltaInf ^ 3 :=
  ⟨volQuantum_pos hx hy hz, volQuantum_floor hx hy hz,
    volQuantum_lt_ceiling hx hy hz⟩

end VolumetricQuantum

end

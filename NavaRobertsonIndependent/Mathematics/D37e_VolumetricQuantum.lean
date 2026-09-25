import NavaRobertsonIndependent.Mathematics.D11_MinimalAreaQuantum
import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle

/-!
# D37e — The volumetric quantum of three-dimensional uncertainty

Each axis of the cube `dx × dy × dz` (`D37`) carries its own dimensional quantum
`δ(d) = C_Nava(d) − 1` (`cuantoDim`, `D25`); the NRS angle of the axis is
`θ_NRS(d) = arccos (1 / (1 + δ(d)))` (`anguloNRS_eq_cuanto`). The area quantum of `D11` is
`δ(4)²`. The **volumetric quantum** of the cube is the product over its three axes,

  `𝒱(dx, dy, dz) = δ(dx) · δ(dy) · δ(dz)`.

* It vanishes exactly when some axis has `2` or `3` sites (`cuantoVolumetrico_eq_cero_iff`):
  the only way to cancel it is to lower an axis to a seed, never to add sites.
* With at least `4` sites on every axis it is strictly positive, bounded below by
  `δ(4)³` (attained at `4 × 4 × 4`, `cuantoVolumetrico_piso`) and strictly below `δ_∞³`
  (`cuantoVolumetrico_techo`), and strictly increasing in each axis
  (`cuantoVolumetrico_strictMono_x/y/z`).
* At the first rupture it is `(√((99 − 42√5)/5) − 1)³` (`cuantoVolumetrico_cuatro`), and its
  square is the cube of the area quantum of `D11` (`cuantoVolumetrico_cuatro_sq`).
-/

noncomputable section

open Real Gnomon CuantoDimensional CuantoMinimoArea AnguloNRS NavaRobertsonSchrodingerEDUI

namespace CuantoVolumetrico

/-- The linear quantum of an axis fixes its NRS angle: `θ_NRS(d) = arccos (1 / (1 + δ(d)))`. -/
theorem anguloNRS_eq_cuanto {d : ℕ} (hd : 2 ≤ d) :
    anguloNRS d = arccos (1 / (1 + cuantoDim d)) := by
  rw [anguloNRS_eq hd, cuantoDim, ← CoherenceConstant_eq_one_add_geometricGap]

theorem cuantoDim_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ cuantoDim d := geometricGap_nonneg hd

/-- The linear quantum at the first rupture, in closed form. -/
theorem cuantoDim_cuatro : cuantoDim 4 = Real.sqrt ((99 - 42 * Real.sqrt 5) / 5) - 1 := by
  rw [cuantoDim, geometricGap, CoherenceConstant, CoherenceConstantSq_four_eq]

/-- **The volumetric quantum** of the cube `dx × dy × dz`. -/
def cuantoVolumetrico (dx dy dz : ℕ) : ℝ := cuantoDim dx * cuantoDim dy * cuantoDim dz

variable {dx dy dz : ℕ}

theorem cuantoVolumetrico_nonneg (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    0 ≤ cuantoVolumetrico dx dy dz :=
  mul_nonneg (mul_nonneg (cuantoDim_nonneg hx) (cuantoDim_nonneg hy)) (cuantoDim_nonneg hz)

/-- **It vanishes only at a seed axis.** -/
theorem cuantoVolumetrico_eq_cero_iff (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    cuantoVolumetrico dx dy dz = 0 ↔
      (dx = 2 ∨ dx = 3) ∨ (dy = 2 ∨ dy = 3) ∨ (dz = 2 ∨ dz = 3) := by
  rw [cuantoVolumetrico, mul_eq_zero, mul_eq_zero, cuantoDim_eq_cero_iff hx,
    cuantoDim_eq_cero_iff hy, cuantoDim_eq_cero_iff hz, or_assoc]

theorem cuantoVolumetrico_pos (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    0 < cuantoVolumetrico dx dy dz :=
  mul_pos (mul_pos (cuantoDim_pos hx) (cuantoDim_pos hy)) (cuantoDim_pos hz)

/-- **Floor.** With at least `4` sites per axis, the volumetric quantum is at least `δ(4)³`. -/
theorem cuantoVolumetrico_piso (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    cuantoDim 4 ^ 3 ≤ cuantoVolumetrico dx dy dz := by
  have h4 := (cuantoDim_pos (le_refl 4)).le
  have ax := cuantoDim_piso hx; have ay := cuantoDim_piso hy; have az := cuantoDim_piso hz
  rw [cuantoVolumetrico, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul ax ay h4 (h4.trans ax)) az h4
    (mul_nonneg (h4.trans ax) (h4.trans ay))

/-- **Ceiling.** It stays strictly below `δ_∞³`, which no cube reaches. -/
theorem cuantoVolumetrico_techo (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    cuantoVolumetrico dx dy dz < deltaInf ^ 3 := by
  have px := (cuantoDim_pos hx).le; have py := (cuantoDim_pos hy).le
  have tx := cuantoDim_techo hx; have ty := cuantoDim_techo hy; have tz := cuantoDim_techo hz
  rw [cuantoVolumetrico, pow_three, ← mul_assoc]
  exact mul_lt_mul'' (mul_lt_mul'' tx ty px py) tz (mul_nonneg px py) (cuantoDim_pos hz).le

/-- On the cube `d × d × d` the volumetric quantum is `δ(d)³`. -/
theorem cuantoVolumetrico_cubo (d : ℕ) : cuantoVolumetrico d d d = cuantoDim d ^ 3 := by
  rw [cuantoVolumetrico]; ring

/-- **At the first rupture** `4 × 4 × 4`: `𝒱 = (√((99 − 42√5)/5) − 1)³`. -/
theorem cuantoVolumetrico_cuatro :
    cuantoVolumetrico 4 4 4 = (Real.sqrt ((99 - 42 * Real.sqrt 5) / 5) - 1) ^ 3 := by
  rw [cuantoVolumetrico_cubo, cuantoDim_cuatro]

/-- Volume and area quanta at the first rupture: `𝒱(4,4,4)² = (area quantum)³`. -/
theorem cuantoVolumetrico_cuatro_sq :
    cuantoVolumetrico 4 4 4 ^ 2 = cuantoCuanticoElemental ^ 3 := by
  rw [cuantoVolumetrico_cubo, cuantoCuanticoElemental, cuantoDim]; ring

/-- Adding sites along `x` strictly enlarges the volumetric quantum. -/
theorem cuantoVolumetrico_strictMono_x {dx' : ℕ} (hx : 4 ≤ dx) (h : dx < dx') (hy : 4 ≤ dy)
    (hz : 4 ≤ dz) : cuantoVolumetrico dx dy dz < cuantoVolumetrico dx' dy dz := by
  unfold cuantoVolumetrico
  have := cuantoDim_strictMono hx h
  have p := mul_pos (cuantoDim_pos hy) (cuantoDim_pos hz)
  nlinarith [mul_lt_mul_of_pos_right this p]

theorem cuantoVolumetrico_strictMono_y {dy' : ℕ} (hx : 4 ≤ dx) (hy : 4 ≤ dy) (h : dy < dy')
    (hz : 4 ≤ dz) : cuantoVolumetrico dx dy dz < cuantoVolumetrico dx dy' dz := by
  unfold cuantoVolumetrico
  have := cuantoDim_strictMono hy h
  have p := mul_pos (cuantoDim_pos hx) (cuantoDim_pos hz)
  nlinarith [mul_lt_mul_of_pos_right this p]

theorem cuantoVolumetrico_strictMono_z {dz' : ℕ} (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz)
    (h : dz < dz') : cuantoVolumetrico dx dy dz < cuantoVolumetrico dx dy dz' := by
  unfold cuantoVolumetrico
  have := cuantoDim_strictMono hz h
  have p := mul_pos (cuantoDim_pos hx) (cuantoDim_pos hy)
  nlinarith [mul_lt_mul_of_pos_right this p]

/-- **Certificate of the volumetric quantum.** Zero only at a seed axis; from `4 × 4 × 4` on,
positive, at least `δ(4)³`, strictly below `δ_∞³`, strictly increasing in each axis. -/
theorem cuanto_volumetrico (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    0 < cuantoVolumetrico dx dy dz ∧
      cuantoDim 4 ^ 3 ≤ cuantoVolumetrico dx dy dz ∧
      cuantoVolumetrico dx dy dz < deltaInf ^ 3 :=
  ⟨cuantoVolumetrico_pos hx hy hz, cuantoVolumetrico_piso hx hy hz,
    cuantoVolumetrico_techo hx hy hz⟩

end CuantoVolumetrico

end

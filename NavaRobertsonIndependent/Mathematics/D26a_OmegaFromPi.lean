/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D8_Szego
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# D26a — `Ω` desde `π`: la constante `g_s·e^{−1/C∞}` y su encierro racional

Matemática pura (Capa 1): solo `π`. Con `C∞ = √(π²/3 − 2)` (`D8`),

`omegaPi = (1 − 1/C∞) · e^{−1/C∞} = 0.04954367888809…`

y el decimal `0.049543679` es su redondeo a 9 cifras, **certificado por los dos lados**:

`1.11×10⁻¹⁰ < 0.049543679 − omegaPi < 1.12×10⁻¹⁰`  (`< 2.3×10⁻⁹` relativo).

Método: `π` a 20 decimales (`Real.pi_gt_d20`/`pi_lt_d20`); `C∞` encerrado a 13
decimales; `1/C∞` por monotonía de la división; `e^{−1/C∞}` con la cota de Taylor
`Real.exp_bound` en `n = 16` (resto `< 7×10⁻¹⁵`), evaluada en los extremos racionales.

Uso: la Capa 2 toma `Ω_b = 0.049543679` y, con este módulo, sabe que ese decimal sale
de `π` (`LimiteSubPlanckiano.Omega_b_desde_pi`). La lectura "fracción bariónica" es de
la Capa 3 (`D26`, `D26b`).

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

@[expose] public noncomputable section

namespace OmegaDesdePi

open Gnomon

/-- `g_s = 1 − 1/C∞`. -/
def gPi : ℝ := 1 - 1 / CoherenceConstantInf

/-- `e^{−1/C∞}`. -/
def boltzmannPi : ℝ := Real.exp (-1 / CoherenceConstantInf)

/-- `omegaPi = g_s · e^{−1/C∞}`, función solo de `π`. -/
def omegaPi : ℝ := gPi * boltzmannPi

/-! ## `C∞` a 13 decimales -/

theorem CoherenceConstantInf_gt : (1.1357236167732 : ℝ) < CoherenceConstantInf := by
  unfold CoherenceConstantInf
  rw [show (1.1357236167732:ℝ) = Real.sqrt (1.1357236167732^2) from
    (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_lt_sqrt (by norm_num)
  nlinarith [Real.pi_gt_d20]

theorem CoherenceConstantInf_lt : CoherenceConstantInf < 1.1357236167733 := by
  unfold CoherenceConstantInf
  rw [Real.sqrt_lt' (by norm_num)]
  nlinarith [Real.pi_lt_d20, Real.pi_pos]

/-! ## `1/C∞` y `g_s` -/

theorem invCoherenceConstantInf_gt : (0.88049591047606 : ℝ) < 1 / CoherenceConstantInf := by
  have h := one_div_lt_one_div_of_lt CoherenceConstantInf_pos CoherenceConstantInf_lt
  have h2 : (1:ℝ) / 1.1357236167733 > 0.88049591047606 := by norm_num
  linarith

theorem invCoherenceConstantInf_lt : 1 / CoherenceConstantInf < (0.88049591047623 : ℝ) := by
  have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 1.1357236167732) CoherenceConstantInf_gt
  have h2 : (1:ℝ) / 1.1357236167732 < 0.88049591047623 := by norm_num
  linarith

theorem gPi_gt : (0.11950408952377 : ℝ) < gPi := by
  unfold gPi; linarith [invCoherenceConstantInf_lt]

theorem gPi_lt : gPi < (0.11950408952394 : ℝ) := by
  unfold gPi; linarith [invCoherenceConstantInf_gt]

theorem gPi_pos : 0 < gPi := by linarith [gPi_gt]

/-! ## `e^{−1/C∞}` vía Taylor `n = 16` -/

theorem boltzmannPi_gt : (0.41457726748507 : ℝ) < boltzmannPi := by
  have hz : (-1 : ℝ) / CoherenceConstantInf = -(1 / CoherenceConstantInf) := by ring
  have hmono : Real.exp (-0.88049591047623) < Real.exp (-1 / CoherenceConstantInf) :=
    Real.exp_lt_exp.mpr (by rw [hz]; linarith [invCoherenceConstantInf_lt])
  have hx : |(-0.88049591047623:ℝ)| ≤ 1 := by norm_num
  have h := Real.exp_bound hx (n := 16) (by norm_num)
  rw [abs_le] at h
  unfold boltzmannPi
  nlinarith [h.1, hmono]

theorem boltzmannPi_lt : boltzmannPi < (0.41457726748516 : ℝ) := by
  have hz : (-1 : ℝ) / CoherenceConstantInf = -(1 / CoherenceConstantInf) := by ring
  have hmono : Real.exp (-1 / CoherenceConstantInf) < Real.exp (-0.88049591047606) :=
    Real.exp_lt_exp.mpr (by rw [hz]; linarith [invCoherenceConstantInf_gt])
  have hx : |(-0.88049591047606:ℝ)| ≤ 1 := by norm_num
  have h := Real.exp_bound hx (n := 16) (by norm_num)
  rw [abs_le] at h
  unfold boltzmannPi
  nlinarith [h.2, hmono]

theorem boltzmannPi_pos : 0 < boltzmannPi := Real.exp_pos _

/-! ## Cierre -/

/-- **El decimal `0.049543679` es `omegaPi` a 9 cifras**: la distancia está encerrada
por los dos lados en `(1.11, 1.12)×10⁻¹⁰`. -/
theorem decimal_desde_pi :
    111 * 10 ^ (-12 : ℤ) < (49543679 : ℝ) / 10 ^ 9 - omegaPi ∧
      (49543679 : ℝ) / 10 ^ 9 - omegaPi < 112 * 10 ^ (-12 : ℤ) := by
  unfold omegaPi
  have hb := boltzmannPi_pos
  have hg := gPi_pos
  constructor
  · nlinarith [mul_lt_mul_of_pos_left boltzmannPi_lt hg,
      mul_lt_mul_of_pos_right gPi_lt hb]
  · nlinarith [mul_lt_mul_of_pos_left boltzmannPi_gt hg,
      mul_lt_mul_of_pos_right gPi_gt hb]

end OmegaDesdePi

import NavaRobertsonIndependent.Mathematics.D6_Fiedler
import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# `RNava`: varianza de posición del estado canónico `ψ` en `H_d`

Pregunta exploratoria del usuario: "¿qué da `Vsub` contra un Hamiltoniano?"
`Vsub` contra `PuenteAreaBekenstein` ya colapsaba a `Asub`
(`Constructor_Bekenstein_Vsub.lean`). Este módulo instancia la otra pieza
todavía viva en el mismo `H_d`: el Hamiltoniano canónico `{T_d,P_d}` en el
estado de máxima tensión `ψ = vectorFiedlerExplicito` (`hamiltonianoCanal`,
`E03_Fiedler_03_Constructor_Tensor_Energia_Momento_Discreto.lean`).

**Resultado 1 (numérico, no en este módulo):** `⟨ψ|{T_d,P_d}|ψ⟩ = 0`
exactamente, para todo `d`, por paridad bajo la reflexión `j ↦ d-1-j` del
camino (`P_d` es impar, `T_d` es par, la densidad `|ψ_j|²` es par). No hay
nada que certificar: es cero por simetría, mismo patrón que `Vsub`.

**Resultado 2 (este módulo):** la cantidad que SÍ sobrevive en ese mismo
`H_d` es la varianza de posición `⟨ψ|P_d²|ψ⟩ = Σⱼ |ψⱼ|² · posicionCoord(j)²`.
Se calcula aquí en forma cerrada exacta (vía blindaje Fourier/raíz de la
unidad sobre `z = exp(i·2θ)`, con `θ = Gnomon.theta d`) y se cierra con un
límite `d → ∞`.

## Qué NO es

No es una relación de incertidumbre nueva ni una energía de Hamiltoniano:
`⟨H⟩` ya es cero (resultado 1). `RNava` es, literalmente, el radio de giro
(RMS) del estado de máxima tensión sobre la malla de posición `[-1,1]`.

## El hallazgo

Numéricamente (fuera de Lean, no certificado en este módulo) en las seeds
de Niven (`d=2,3`, donde `cos²(θ)=(d-1)/4` sí satura): `RNavaSq(2)=1`,
`RNavaSq(3)=1/2` — valores racionales limpios, mismo patrón que
`CoherenceConstantSq(2)=CoherenceConstantSq(3)=1`. No se formaliza aquí (`RNavaSq` solo se certifica
para `d≥2` vía `RNavaSq_eq`, que ya cubre ambas seeds si alguien quiere
evaluarlas por `norm_num`/`decide` más adelante).

En el régimen físico (`d≥4`, donde Niven prueba que la saturación es
imposible): `RNavaSq(d)` decrece estrictamente y **nunca toca** su límite
— mismo carácter que `δ_geom(d) > 0` nunca llega a cero.

El límite no es una constante independiente: `Rinf = Gnomon.CoherenceConstantInf / π`
(`Rinf_eq_CoherenceConstantInf_div_pi`, teorema, no definición) — la misma constante de
Szegő que ya blinda todo el corpus (`CoherenceConstantInf`, la que alimenta `Ω_b`, `g_s_sq`),
reescalada por `π`. `RNava` es una cantidad propia (varianza de posición,
no de saturación de banda) que resulta estar conectada a `CoherenceConstantInf` por un
factor limpio, no "la misma constante reusada".

**Cierre físico** (`§9`, `RNavaSq_eq_varianzaFin`): `RNavaSq(d)` no es solo
una forma cerrada que numéricamente coincide con la varianza -- es,
literalmente, `Σⱼ |vectorFiedlerExplicito(d)ⱼ|² · posicionCoord(d,j)²` sobre
`Fin d`, probado por reindexación exacta (`j.val+1 = k`, el término `k=0`
se anula por `sin 0 = 0`) contra las sumas de Fourier de `§2`-`§4`.
-/

noncomputable section

open Finset Complex Real Filter
open scoped Topology

namespace RNavaVarianzaFiedler

open Gnomon TransportePosicion

/-! ## 1. Raíz de la unidad auxiliar `z = exp(i·2θ)` (maquinaria de Fourier,
sin contenido físico: sirve solo para evaluar las sumas trigonométricas). -/

/-- Ángulo doble auxiliar. -/
noncomputable def phi (d : ℕ) : ℝ := 2 * theta d

noncomputable def z (d : ℕ) : ℂ := Complex.exp ((phi d : ℝ) * Complex.I)

theorem theta_pos (d : ℕ) : 0 < theta d := by unfold theta Nreal; positivity

theorem phi_pos (d : ℕ) : 0 < phi d := by unfold phi; linarith [theta_pos d]

theorem theta_le (d : ℕ) (hd : 1 ≤ d) : theta d ≤ Real.pi / 2 := by
  have hNpos : (0:ℝ) < Nreal d := by unfold Nreal; positivity
  have heq : theta d * Nreal d = Real.pi := by unfold theta; field_simp
  have h2 : (2:ℝ) ≤ Nreal d := by
    unfold Nreal
    have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  nlinarith [theta_pos d]

theorem phi_le (d : ℕ) (hd : 1 ≤ d) : phi d ≤ Real.pi := by
  unfold phi; linarith [theta_le d hd]

theorem z_re (d : ℕ) : (z d).re = Real.cos (phi d) := by
  unfold z; exact Complex.exp_ofReal_mul_I_re _

theorem z_im (d : ℕ) : (z d).im = Real.sin (phi d) := by
  unfold z; exact Complex.exp_ofReal_mul_I_im _

theorem cosphi_ne_one (d : ℕ) (hd : 1 ≤ d) : Real.cos (phi d) ≠ 1 := by
  intro hre
  have hb1 : -(2*Real.pi) < phi d := by have := phi_pos d; linarith [Real.pi_pos]
  have hb2 : phi d < 2 * Real.pi := by have h1 := phi_le d hd; linarith [Real.pi_pos]
  have := (Real.cos_eq_one_iff_of_lt_of_lt hb1 hb2).mp hre
  have := phi_pos d
  linarith

theorem z_ne_one (d : ℕ) (hd : 1 ≤ d) : z d ≠ 1 := by
  intro h
  have hre : (z d).re = 1 := by rw [h]; simp
  rw [z_re] at hre
  exact cosphi_ne_one d hd hre

theorem z_pow_succ (d : ℕ) : z d ^ (d+1) = 1 := by
  unfold z
  rw [← Complex.exp_nat_mul]
  have heq : (↑(d+1) : ℂ) * (↑(phi d : ℝ) * Complex.I) = 2 * ↑Real.pi * Complex.I := by
    unfold phi theta Nreal
    push_cast
    have hne : (d:ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [heq]
  exact Complex.exp_two_pi_mul_I

/-! ## 2. Suma geométrica ponderada general (álgebra pura, cualquier `x ≠ 1`) -/

theorem sum_range_mul_pow (x : ℂ) (hx : x ≠ 1) :
    ∀ n : ℕ, ∑ k ∈ Finset.range n, (k : ℂ) * x ^ k =
      (x + ((n:ℂ) - 1) * x ^ (n+1) - (n:ℂ) * x ^ n) / (x - 1) ^ 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hx1 : (x - 1) ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    push_cast
    ring

theorem sum_range_sq_mul_pow (x : ℂ) (hx : x ≠ 1) :
    ∀ n : ℕ, ∑ k ∈ Finset.range n, (k : ℂ)^2 * x ^ k =
      (((n:ℂ)-1)^2 * x^(n+2) + (1+2*(n:ℂ)-2*(n:ℂ)^2) * x^(n+1) + (n:ℂ)^2 * x^n - x^2 - x) / (x - 1)
          ^ 3 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hx1 : (x - 1) ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    push_cast
    ring

theorem S1_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), (k : ℂ) * (z d) ^ k =
      ((d:ℂ)+1) / (z d - 1) := by
  rw [sum_range_mul_pow (z d) (z_ne_one d hd) (d+1)]
  have hpow1 : (z d) ^ (d+1) = 1 := z_pow_succ d
  have hpow2 : (z d) ^ (d+2) = z d := by
    rw [show d+2 = (d+1)+1 by ring, pow_succ, hpow1, one_mul]
  rw [hpow2, hpow1]
  have hz1 : z d - 1 ≠ 0 := sub_ne_zero.mpr (z_ne_one d hd)
  field_simp
  push_cast
  ring

theorem S2_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), (k : ℂ)^2 * (z d) ^ k =
      ((d:ℂ)+1) * (((d:ℂ)-1) * z d - ((d:ℂ)+1)) / (z d - 1) ^ 2 := by
  rw [sum_range_sq_mul_pow (z d) (z_ne_one d hd) (d+1)]
  have hpow1 : (z d) ^ (d+1) = 1 := z_pow_succ d
  have hpow2 : (z d) ^ (d+2) = z d := by
    rw [show d+2 = (d+1)+1 by ring, pow_succ, hpow1, one_mul]
  have hpow3 : (z d) ^ (d+1+2) = (z d)^2 := by
    rw [show d+1+2 = (d+2)+1 by ring, pow_succ, hpow2, sq]
  rw [hpow1, hpow2, hpow3]
  have hz1 : z d - 1 ≠ 0 := sub_ne_zero.mpr (z_ne_one d hd)
  field_simp
  push_cast
  ring

theorem zpow_eq (d k : ℕ) : (z d)^k = Complex.exp (((k:ℝ)*phi d : ℝ) * Complex.I) := by
  unfold z
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem zpow_re (d k : ℕ) : ((z d)^k).re = Real.cos ((k:ℝ)*phi d) := by
  rw [zpow_eq]; exact Complex.exp_ofReal_mul_I_re _

/-! ## 3. Extracción real: sumas de Fourier con peso `k` y `k²` -/

theorem C1_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), (k : ℝ) * Real.cos ((k:ℝ) * phi d) =
      -((d:ℝ)+1)/2 := by
  have hcomplex := congrArg Complex.re (S1_eq d hd)
  rw [Complex.re_sum] at hcomplex
  have hLHS : ∀ k ∈ Finset.range (d+1),
      ((k:ℂ) * (z d)^k).re = (k:ℝ) * Real.cos ((k:ℝ)*phi d) := by
    intro k _
    rw [show (k:ℂ) = ((k:ℝ):ℂ) from by push_cast; ring]
    rw [Complex.re_ofReal_mul, zpow_re]
  rw [Finset.sum_congr rfl hLHS] at hcomplex
  rw [hcomplex]
  rw [Complex.div_re]
  have hnre : (((d:ℂ)+1)).re = (d:ℝ)+1 := by simp
  have hnim : (((d:ℂ)+1)).im = 0 := by simp
  rw [hnre, hnim]
  have hwre : (z d - 1).re = Real.cos (phi d) - 1 := by simp [z_re]
  have hwim : (z d - 1).im = Real.sin (phi d) := by simp [z_im]
  rw [hwre, hwim]
  have hns : Complex.normSq (z d - 1) = 2 - 2 * Real.cos (phi d) := by
    rw [Complex.normSq_apply, hwre, hwim]
    have hpyth : Real.sin (phi d)^2 + Real.cos (phi d)^2 = 1 := Real.sin_sq_add_cos_sq _
    nlinarith [hpyth]
  rw [hns]
  simp only [zero_mul, zero_div, add_zero]
  have hcos_lt : Real.cos (phi d) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (cosphi_ne_one d hd)
  have hden_pos : (2:ℝ) - 2*Real.cos (phi d) ≠ 0 := by nlinarith
  rw [div_eq_div_iff hden_pos (by norm_num : (2:ℝ) ≠ 0)]
  ring

theorem w_re (d : ℕ) : (z d - 1).re = Real.cos (phi d) - 1 := by simp [z_re]
theorem w_im (d : ℕ) : (z d - 1).im = Real.sin (phi d) := by simp [z_im]

theorem normSq_w (d : ℕ) : Complex.normSq (z d - 1) = 2 - 2 * Real.cos (phi d) := by
  rw [Complex.normSq_apply, w_re, w_im]
  nlinarith [Real.sin_sq_add_cos_sq (phi d)]

theorem wsq_re (d : ℕ) :
    ((z d - 1)^2).re = (Real.cos (phi d) - 1)^2 - (Real.sin (phi d))^2 := by
  rw [sq, Complex.mul_re, w_re, w_im]; ring

theorem wsq_im (d : ℕ) :
    ((z d - 1)^2).im = 2*(Real.cos (phi d) - 1)*Real.sin (phi d) := by
  rw [sq, Complex.mul_im, w_re, w_im]; ring

theorem normSq_wsq (d : ℕ) :
    Complex.normSq ((z d - 1)^2) = (2 - 2*Real.cos (phi d))^2 := by
  rw [sq ((z d - 1)), map_mul, normSq_w]; ring

theorem C2_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), (k : ℝ)^2 * Real.cos ((k:ℝ) * phi d) =
      ((d:ℝ)+1) / (1 - Real.cos (phi d)) - ((d:ℝ)+1)^2 / 2 := by
  have hcomplex := congrArg Complex.re (S2_eq d hd)
  rw [Complex.re_sum] at hcomplex
  have hLHS : ∀ k ∈ Finset.range (d+1),
      ((k:ℂ)^2 * (z d)^k).re = (k:ℝ)^2 * Real.cos ((k:ℝ)*phi d) := by
    intro k _
    rw [show (k:ℂ)^2 = (((k:ℝ)^2 : ℝ):ℂ) from by push_cast; ring]
    rw [Complex.re_ofReal_mul, zpow_re]
  rw [Finset.sum_congr rfl hLHS] at hcomplex
  rw [hcomplex]
  rw [Complex.div_re]
  have hWre : (((d:ℂ)+1) * (((d:ℂ)-1) * z d - ((d:ℂ)+1))).re
      = ((d:ℝ)+1)*((d:ℝ)-1)*Real.cos (phi d) - ((d:ℝ)+1)^2 := by
    have h1 : (((d:ℂ)+1) * (((d:ℂ)-1) * z d - ((d:ℂ)+1))).re
        = ((d:ℂ)+1).re * (((d:ℂ)-1) * z d - ((d:ℂ)+1)).re
          - ((d:ℂ)+1).im * (((d:ℂ)-1) * z d - ((d:ℂ)+1)).im := Complex.mul_re _ _
    rw [h1]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, z_re, z_im]
    ring
  have hWim : (((d:ℂ)+1) * (((d:ℂ)-1) * z d - ((d:ℂ)+1))).im
      = ((d:ℝ)+1)*((d:ℝ)-1)*Real.sin (phi d) := by
    have h1 : (((d:ℂ)+1) * (((d:ℂ)-1) * z d - ((d:ℂ)+1))).im
        = ((d:ℂ)+1).re * (((d:ℂ)-1) * z d - ((d:ℂ)+1)).im
          + ((d:ℂ)+1).im * (((d:ℂ)-1) * z d - ((d:ℂ)+1)).re := Complex.mul_im _ _
    rw [h1]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, z_re, z_im]
    ring
  rw [hWre, hWim, wsq_re, wsq_im, normSq_wsq]
  have hpyth : Real.sin (phi d)^2 + Real.cos (phi d)^2 = 1 := Real.sin_sq_add_cos_sq (phi d)
  have hsinsq : Real.sin (phi d)^2 = 1 - Real.cos (phi d)^2 := by linarith
  have hcos_lt : Real.cos (phi d) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (cosphi_ne_one d hd)
  have hden_pos : (2:ℝ) - 2*Real.cos (phi d) ≠ 0 := by nlinarith
  have hden1 : (1:ℝ) - Real.cos (phi d) ≠ 0 := by nlinarith
  field_simp
  linear_combination ((Real.cos (phi d) - 1)*((d:ℝ)-1) + 2) * hpyth

/-! ## 4. Sumas ponderadas por `sin²(kθ)`: la densidad `|ψⱼ|²` reindexada -/

theorem sum_range_real (n:ℕ) : ∑ k ∈ Finset.range n, (k:ℝ) = (n:ℝ)*((n:ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_sq_real (n:ℕ) : ∑ k ∈ Finset.range n, (k:ℝ)^2 = (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 :=
    by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem S0_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), Real.cos ((k:ℝ) * phi d) = 0 := by
  have hcomplex := congrArg Complex.re (geom_sum_eq (z_ne_one d hd) (d+1))
  rw [Complex.re_sum] at hcomplex
  have hLHS : ∀ k ∈ Finset.range (d+1), ((z d)^k).re = Real.cos ((k:ℝ)*phi d) := by
    intro k _; exact zpow_re d k
  rw [Finset.sum_congr rfl hLHS] at hcomplex
  rw [hcomplex, z_pow_succ]
  simp

theorem sin_sq_sum_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), Real.sin ((k:ℝ)*theta d)^2 = ((d:ℝ)+1)/2 := by
  have hconv : ∀ k : ℕ, Real.sin ((k:ℝ)*theta d)^2 = (1 - Real.cos ((k:ℝ)*phi d))/2 := by
    intro k
    have hdbl : Real.cos ((k:ℝ)*phi d) = 1 - 2*Real.sin ((k:ℝ)*theta d)^2 := by
      unfold phi
      rw [show (k:ℝ)*(2*theta d) = 2*((k:ℝ)*theta d) by ring]
      rw [Real.cos_two_mul']
      have := Real.sin_sq_add_cos_sq ((k:ℝ)*theta d)
      nlinarith
    linarith [hdbl]
  simp_rw [hconv]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [S0_eq d hd]
  simp

theorem k_sin_sq_sum_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), (k:ℝ)*Real.sin ((k:ℝ)*theta d)^2 = ((d:ℝ)+1)^2/4 := by
  have hconv : ∀ k : ℕ, (k:ℝ)*Real.sin ((k:ℝ)*theta d)^2 = (k:ℝ)/2 - (k:ℝ)*Real.cos ((k:ℝ)*phi d)/2
      := by
    intro k
    have hdbl : Real.cos ((k:ℝ)*phi d) = 1 - 2*Real.sin ((k:ℝ)*theta d)^2 := by
      unfold phi
      rw [show (k:ℝ)*(2*theta d) = 2*((k:ℝ)*theta d) by ring]
      rw [Real.cos_two_mul']
      have := Real.sin_sq_add_cos_sq ((k:ℝ)*theta d)
      nlinarith
    nlinarith [hdbl]
  simp_rw [hconv]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ k ∈ Finset.range (d+1), (k:ℝ)/2) = (∑ k ∈ Finset.range (d+1), (k:ℝ))/2 from by
    rw [Finset.sum_div]]
  rw [show (∑ k ∈ Finset.range (d+1), (k:ℝ)*Real.cos ((k:ℝ)*phi d)/2) =
      (∑ k ∈ Finset.range (d+1), (k:ℝ)*Real.cos ((k:ℝ)*phi d))/2 from by
    rw [Finset.sum_div]]
  rw [sum_range_real, C1_eq d hd]
  push_cast
  ring

theorem k_sq_sin_sq_sum_eq (d : ℕ) (hd : 1 ≤ d) :
    ∑ k ∈ Finset.range (d+1), (k:ℝ)^2*Real.sin ((k:ℝ)*theta d)^2 =
      ((d:ℝ)+1)*(d:ℝ)*(2*(d:ℝ)+1)/12 - ((d:ℝ)+1)/(2*(1-Real.cos (phi d))) + ((d:ℝ)+1)^2/4 := by
  have hconv : ∀ k : ℕ, (k:ℝ)^2*Real.sin ((k:ℝ)*theta d)^2 = (k:ℝ)^2/2 - (k:ℝ)^2*Real.cos ((k:ℝ)*phi
      d)/2 := by
    intro k
    have hdbl : Real.cos ((k:ℝ)*phi d) = 1 - 2*Real.sin ((k:ℝ)*theta d)^2 := by
      unfold phi
      rw [show (k:ℝ)*(2*theta d) = 2*((k:ℝ)*theta d) by ring]
      rw [Real.cos_two_mul']
      have := Real.sin_sq_add_cos_sq ((k:ℝ)*theta d)
      nlinarith
    nlinarith [hdbl]
  simp_rw [hconv]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ k ∈ Finset.range (d+1), (k:ℝ)^2/2) = (∑ k ∈ Finset.range (d+1), (k:ℝ)^2)/2 from by
    rw [Finset.sum_div]]
  rw [show (∑ k ∈ Finset.range (d+1), (k:ℝ)^2*Real.cos ((k:ℝ)*phi d)/2) =
      (∑ k ∈ Finset.range (d+1), (k:ℝ)^2*Real.cos ((k:ℝ)*phi d))/2 from by
    rw [Finset.sum_div]]
  rw [sum_range_sq_real, C2_eq d hd]
  have hcos_lt : Real.cos (phi d) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (cosphi_ne_one d hd)
  have hden1 : (1:ℝ) - Real.cos (phi d) ≠ 0 := by nlinarith
  push_cast
  field_simp
  ring

/-! ## 5. `RNavaSq`: forma cerrada exacta -/

noncomputable def numRaw (d : ℕ) : ℝ :=
  4*(∑ k ∈ Finset.range (d+1), (k:ℝ)^2*Real.sin ((k:ℝ)*theta d)^2)
  - 4*((d:ℝ)+1)*(∑ k ∈ Finset.range (d+1), (k:ℝ)*Real.sin ((k:ℝ)*theta d)^2)
  + ((d:ℝ)+1)^2*(∑ k ∈ Finset.range (d+1), Real.sin ((k:ℝ)*theta d)^2)

noncomputable def denRaw (d : ℕ) : ℝ :=
  ((d:ℝ)-1)^2*(∑ k ∈ Finset.range (d+1), Real.sin ((k:ℝ)*theta d)^2)

theorem numRaw_eq (d : ℕ) (hd : 1 ≤ d) :
    numRaw d = ((d:ℝ)+1)*(d:ℝ)*(2*(d:ℝ)+1)/3 - 2*((d:ℝ)+1)/(1-Real.cos (phi d))
      + ((d:ℝ)+1)^2 - ((d:ℝ)+1)^3/2 := by
  unfold numRaw
  rw [k_sq_sin_sq_sum_eq d hd, k_sin_sq_sum_eq d hd, sin_sq_sum_eq d hd]
  have hcos_lt : Real.cos (phi d) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (cosphi_ne_one d hd)
  have hden1 : (1:ℝ) - Real.cos (phi d) ≠ 0 := by nlinarith
  field_simp
  ring

theorem denRaw_eq (d : ℕ) (hd : 1 ≤ d) :
    denRaw d = ((d:ℝ)-1)^2*((d:ℝ)+1)/2 := by
  unfold denRaw
  rw [sin_sq_sum_eq d hd]
  ring

theorem RNavaSq_raw_eq (d : ℕ) (hd : 2 ≤ d) :
    numRaw d / denRaw d =
      (Real.cos (phi d) * ((d:ℝ)^2+2*(d:ℝ)+3) - ((d:ℝ)^2+2*(d:ℝ)-9))
        / (3*(Real.cos (phi d) - 1)*((d:ℝ)-1)^2) := by
  rw [numRaw_eq d (by omega), denRaw_eq d (by omega)]
  have hcos_lt : Real.cos (phi d) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (cosphi_ne_one d (by
      omega))
  have hden1 : (1:ℝ) - Real.cos (phi d) ≠ 0 := by nlinarith
  have hden1' : Real.cos (phi d) - 1 ≠ 0 := fun h => hden1 (by linarith)
  have hdm1 : (d:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    intro h; linarith
  have hdp1 : (d:ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Forma limpia en `sin(theta d)^2`, usando la identidad de ángulo doble.
Coincide numéricamente con `(d²+2d-3-6cot²θ)/(3(d-1)²)`, la forma explorada
antes de sellar en Lean. -/
theorem RNavaSq_clean_eq (d : ℕ) (hd : 2 ≤ d) :
    numRaw d / denRaw d =
      (((d:ℝ)+1)^2 + 2) / 3 / ((d:ℝ) - 1)^2 - 2 / (Real.sin (theta d))^2 / ((d:ℝ)-1)^2 := by
  rw [RNavaSq_raw_eq d hd]
  have hdbl : Real.cos (phi d) = 1 - 2*Real.sin (theta d)^2 := by
    unfold phi
    rw [Real.cos_two_mul']
    have := Real.sin_sq_add_cos_sq (theta d)
    nlinarith
  rw [hdbl]
  have hsinpos : Real.sin (theta d) ≠ 0 := by
    have h1 : 0 < theta d := theta_pos d
    have h2 : theta d ≤ Real.pi/2 := theta_le d (by omega)
    have h3 : theta d < Real.pi := by linarith [Real.pi_pos]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h3)
  have hdm1 : (d:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    intro h; linarith
  have hdm1sq : ((d:ℝ) - 1)^2 ≠ 0 := pow_ne_zero 2 hdm1
  have hsinsq : (Real.sin (theta d))^2 ≠ 0 := pow_ne_zero 2 hsinpos
  field_simp
  ring

/-- `RNavaSq(d)`: varianza de posición `⟨ψ|P_d²|ψ⟩ = Σⱼ |ψⱼ|² · posicionCoord(j)²`
del estado de máxima tensión, en forma cerrada. Ver `RNavaSq_eq_varianzaFin`
para la identidad con la suma física sobre `Fin d`. -/
noncomputable def RNavaSq (d : ℕ) : ℝ := numRaw d / denRaw d

theorem RNavaSq_eq (d : ℕ) (hd : 2 ≤ d) :
    RNavaSq d = (((d:ℝ)+1)^2 + 2) / 3 / ((d:ℝ) - 1)^2 - 2 / (Real.sin (theta d))^2 / ((d:ℝ)-1)^2 :=
  RNavaSq_clean_eq d hd

/-! ## 6. Límite de Szegő: `RNavaSq(d) → 1/3 - 2/π²` -/

/-- Límite universal (forma cuadrática), independiente de `CoherenceConstantInf` por
construcción -- se conecta a él en `Rinf_eq_CoherenceConstantInf_div_pi`. -/
noncomputable def RinfSq : ℝ := 1/3 - 2/Real.pi^2

theorem RNavaSq_tendsto :
    Tendsto (fun d : ℕ => RNavaSq (d+2)) atTop (𝓝 RinfSq) := by
  have hkey : ∀ d : ℕ, RNavaSq (d+2) =
      (((d:ℝ)+3)^2 + 2) / 3 / ((d:ℝ) + 1)^2 - 2 / (Real.sin (theta (d+2)))^2 / ((d:ℝ)+1)^2 := by
    intro d
    have h := RNavaSq_eq (d+2) (by omega)
    have hcast1 : ((d+2 : ℕ):ℝ) + 1 = (d:ℝ)+3 := by push_cast; ring
    have hcast2 : ((d+2 : ℕ):ℝ) - 1 = (d:ℝ)+1 := by push_cast; ring
    rw [h, hcast1, hcast2]
  have hfun_eq : (fun d : ℕ => RNavaSq (d+2)) =
      (fun d : ℕ => (((d:ℝ)+3)^2 + 2) / 3 / ((d:ℝ) + 1)^2
        - 2 / (Real.sin (theta (d+2)))^2 / ((d:ℝ)+1)^2) := funext hkey
  rw [hfun_eq]
  have hterm1 : Tendsto (fun d : ℕ => (((d:ℝ)+3)^2 + 2) / 3 / ((d:ℝ) + 1)^2) atTop (𝓝 (1/3:ℝ)) := by
    have heq : ∀ d : ℕ, (((d:ℝ)+3)^2 + 2) / 3 / ((d:ℝ) + 1)^2
        = 1/3 + (4*(d:ℝ)+10)/(3*((d:ℝ)+1)^2) := by
      intro d
      have h1 : ((d:ℝ)+1) ≠ 0 := by positivity
      field_simp
      ring
    have hfun_eq2 : (fun d : ℕ => (((d:ℝ)+3)^2 + 2) / 3 / ((d:ℝ) + 1)^2)
        = (fun d : ℕ => 1/3 + (4*(d:ℝ)+10)/(3*((d:ℝ)+1)^2)) := funext heq
    rw [hfun_eq2]
    have htail : Tendsto (fun d : ℕ => (4*(d:ℝ)+10)/(3*((d:ℝ)+1)^2)) atTop (𝓝 0) := by
      have hg : Tendsto (fun d : ℕ => (14:ℝ)/(3*((d:ℝ)+1))) atTop (𝓝 0) := by
        have h : Tendsto (fun d : ℕ => (3*((d:ℝ)+1))) atTop atTop :=
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
            (by norm_num : (0:ℝ) < 3)
        simpa using Tendsto.div_atTop (tendsto_const_nhds (x := (14:ℝ))) h
      apply squeeze_zero (fun d => by positivity) (fun d => ?_) hg
      have hdpos : (0:ℝ) < (d:ℝ)+1 := by positivity
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) d]
    have := htail.const_add (1/3:ℝ)
    simpa using this
  have hterm2 : Tendsto (fun d : ℕ => 2 / (Real.sin (theta (d+2)))^2 / ((d:ℝ)+1)^2) atTop (𝓝
      (2/Real.pi^2)) := by
    have hth0 : Tendsto (fun d : ℕ => theta (d+2)) atTop (𝓝 0) := by
      have heq : ∀ d : ℕ, theta (d+2) = Real.pi / ((d:ℝ)+3) := by
        intro d; unfold theta Nreal; push_cast; ring_nf
      have hfe : (fun d : ℕ => theta (d+2)) = (fun d : ℕ => Real.pi/((d:ℝ)+3)) := funext heq
      rw [hfe]
      have h3 : Tendsto (fun d : ℕ => (d:ℝ)+3) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact h3.const_div_atTop Real.pi
    have hsinc1 : Tendsto (fun d : ℕ => Real.sinc (theta (d+2))) atTop (𝓝 1) := by
      have h := Real.continuous_sinc.continuousAt.tendsto.comp hth0
      rw [Real.sinc_zero] at h
      exact h
    have hprod : Tendsto (fun d : ℕ => theta (d+2) * ((d:ℝ)+1)) atTop (𝓝 Real.pi) := by
      have heq : ∀ d : ℕ, theta (d+2) * ((d:ℝ)+1) = Real.pi * (((d:ℝ)+1)/((d:ℝ)+3)) := by
        intro d
        have h1 : theta (d+2) = Real.pi/((d:ℝ)+3) := by unfold theta Nreal; push_cast; ring_nf
        rw [h1]; ring
      have hfe : (fun d : ℕ => theta (d+2)*((d:ℝ)+1)) = (fun d : ℕ => Real.pi*(((d:ℝ)+1)/((d:ℝ)+3)))
          := funext heq
      rw [hfe]
      have hratio : Tendsto (fun d : ℕ => ((d:ℝ)+1)/((d:ℝ)+3)) atTop (𝓝 1) := by
        have heq2 : ∀ d : ℕ, ((d:ℝ)+1)/((d:ℝ)+3) = 1 - 2/((d:ℝ)+3) := by
          intro d
          have h3 : ((d:ℝ)+3) ≠ 0 := by positivity
          field_simp
          ring
        have hfe2 : (fun d : ℕ => ((d:ℝ)+1)/((d:ℝ)+3)) = (fun d : ℕ => 1 - 2/((d:ℝ)+3)) := funext
            heq2
        rw [hfe2]
        have h3 : Tendsto (fun d : ℕ => (d:ℝ)+3) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have := (h3.const_div_atTop (2:ℝ)).const_sub (1:ℝ)
        simpa using this
      simpa using hratio.const_mul Real.pi
    have hden2 : Tendsto (fun d : ℕ => (Real.sin (theta (d+2)))^2 * ((d:ℝ)+1)^2) atTop (𝓝
        (Real.pi^2)) := by
      have heq : ∀ d : ℕ, (Real.sin (theta (d+2)))^2 * ((d:ℝ)+1)^2
          = (theta (d+2) * Real.sinc (theta (d+2)) * ((d:ℝ)+1))^2 := by
        intro d
        have hthne : theta (d+2) ≠ 0 := by
          have : 0 < theta (d+2) := theta_pos (d+2)
          exact ne_of_gt this
        rw [Real.sinc_of_ne_zero hthne]
        field_simp
      have hfe : (fun d : ℕ => (Real.sin (theta (d+2)))^2 * ((d:ℝ)+1)^2)
          = (fun d : ℕ => (theta (d+2) * Real.sinc (theta (d+2)) * ((d:ℝ)+1))^2) := funext heq
      rw [hfe]
      have hinner : Tendsto (fun d : ℕ => theta (d+2) * Real.sinc (theta (d+2)) * ((d:ℝ)+1)) atTop
          (𝓝 Real.pi) := by
        have hm := hsinc1.mul hprod
        rw [show (1:ℝ)*Real.pi = Real.pi by ring] at hm
        have heq3 : ∀ d : ℕ, Real.sinc (theta (d+2)) * (theta (d+2) * ((d:ℝ)+1))
            = theta (d+2) * Real.sinc (theta (d+2)) * ((d:ℝ)+1) := by intro d; ring
        rw [funext heq3] at hm
        exact hm
      have := hinner.pow 2
      simpa using this
    have hne : (Real.pi:ℝ)^2 ≠ 0 := by positivity
    have hdiv : Tendsto (fun d : ℕ => (2:ℝ) / ((Real.sin (theta (d+2)))^2 * ((d:ℝ)+1)^2))
        atTop (𝓝 (2/Real.pi^2)) :=
      (tendsto_const_nhds (x := (2:ℝ))).div hden2 hne
    have hfe3 : (fun d : ℕ => (2:ℝ) / ((Real.sin (theta (d+2)))^2 * ((d:ℝ)+1)^2))
        = (fun d : ℕ => 2 / (Real.sin (theta (d+2)))^2 / ((d:ℝ)+1)^2) := by
      funext d; rw [div_div]
    rw [hfe3] at hdiv
    exact hdiv
  have := hterm1.sub hterm2
  unfold RinfSq
  exact this

/-! ## 8. `RNava`, `Rinf`, y el puente con `CoherenceConstantInf` -/

noncomputable def RNava (d : ℕ) : ℝ := Real.sqrt (RNavaSq d)

/-- Límite de `RNava`, definido de forma independiente (no como `CoherenceConstantInf/π`) --
la conexión es un teorema (`Rinf_eq_CoherenceConstantInf_div_pi`), no una definición. -/
noncomputable def Rinf : ℝ := Real.sqrt RinfSq

theorem RNava_tendsto : Tendsto (fun d : ℕ => RNava (d+2)) atTop (𝓝 Rinf) := by
  unfold RNava Rinf
  exact Real.continuous_sqrt.continuousAt.tendsto.comp RNavaSq_tendsto

/-- **El puente**: `Rinf` (radio RMS límite de la varianza de posición) es
`CoherenceConstantInf` (constante universal de Szegő, la misma que alimenta `Ω_b`, `g_s_sq`,
`deltaInf`) dividida por `π`. No es la misma cantidad reusada -- `Rinf` se
definió sin mencionar `CoherenceConstantInf` -- pero tampoco es independiente: la conexión
es exacta y se prueba aquí. -/
theorem Rinf_eq_CoherenceConstantInf_div_pi : Rinf = CoherenceConstantInf / Real.pi := by
  unfold Rinf RinfSq CoherenceConstantInf
  rw [show (1:ℝ)/3 - 2/Real.pi^2 = (Real.pi^2/3-2)/Real.pi^2 from by
    field_simp]
  have hnn : (0:ℝ) ≤ Real.pi^2/3 - 2 := by nlinarith [Real.pi_gt_three]
  rw [Real.sqrt_div hnn, Real.sqrt_sq Real.pi_pos.le]

/-! ## 9. Conexión física: `RNavaSq` ES la varianza sobre `Fin d`

Todo lo anterior (`numRaw`, `denRaw`, `RNavaSq`) se construyó como suma
sobre `Finset.range (d+1)`, sin tocar `vectorFiedlerExplicito` ni
`posicionCoord`. Esta sección cierra el círculo: `RNavaSq(d)` es,
literalmente, `Σⱼ |ψⱼ|² · posicionCoord(j)²` -- la varianza de posición del
estado canónico, no solo una forma cerrada que numéricamente coincide. -/

theorem anguloFiedler_eq_theta (d : ℕ) : anguloFiedler d = theta d := by
  unfold anguloFiedler theta Nreal; rfl

theorem vectorFiedlerCrudo_norm_sq (d : ℕ) (j : Fin d) :
    ‖vectorFiedlerCrudo d j‖^2 = Real.sin (((j.val:ℝ)+1) * theta d)^2 := by
  have h : vectorFiedlerCrudo d j = (-Complex.I)^j.val * (Real.sin (((j.val:ℝ)+1) * anguloFiedler d)
      : ℂ) := rfl
  rw [h, anguloFiedler_eq_theta]
  rw [norm_mul, norm_pow, Complex.norm_real]
  have h1 : ‖(-Complex.I : ℂ)‖ = 1 := by simp
  rw [h1]
  simp [sq_abs]

theorem crudo_normSq_eq_sum (d : ℕ) :
    ‖vectorFiedlerCrudo d‖^2 = ∑ k ∈ Finset.range (d+1), Real.sin ((k:ℝ)*theta d)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [vectorFiedlerCrudo_norm_sq]
  rw [Fin.sum_univ_eq_sum_range (fun k => Real.sin (((k:ℝ)+1)*theta d)^2) d]
  rw [Finset.sum_range_succ']
  simp

theorem posicionCoord_apply (d : ℕ) (j : Fin d) :
    posicionCoord d j = (2*((j.val:ℝ)+1) - ((d:ℝ)+1)) / ((d:ℝ)-1) := by
  unfold posicionCoord
  ring_nf

theorem numRaw_eq_sum_sq (d : ℕ) :
    numRaw d = ∑ k ∈ Finset.range (d+1), (2*(k:ℝ)-((d:ℝ)+1))^2 * Real.sin ((k:ℝ)*theta d)^2 := by
  unfold numRaw
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem crudo_posicion_sum_eq (d : ℕ) :
    ∑ j : Fin d, ‖vectorFiedlerCrudo d j‖^2 * (posicionCoord d j)^2 = numRaw d / ((d:ℝ)-1)^2 := by
  have hterm : ∀ j : Fin d, ‖vectorFiedlerCrudo d j‖^2 * (posicionCoord d j)^2
      = ((2*((j.val:ℝ)+1) - ((d:ℝ)+1))^2 * Real.sin (((j.val:ℝ)+1)*theta d)^2) / ((d:ℝ)-1)^2 := by
    intro j
    rw [vectorFiedlerCrudo_norm_sq, posicionCoord_apply, div_pow]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (2*((k:ℝ)+1)-((d:ℝ)+1))^2 * Real.sin (((k:ℝ)+1)*theta d)^2) d]
  have hshift : ∑ k ∈ Finset.range (d+1), (2*(k:ℝ)-((d:ℝ)+1))^2*Real.sin ((k:ℝ)*theta d)^2
      = ∑ k ∈ Finset.range d, (2*((k:ℝ)+1)-((d:ℝ)+1))^2*Real.sin (((k:ℝ)+1)*theta d)^2 := by
    rw [Finset.sum_range_succ']
    simp
  rw [← hshift, numRaw_eq_sum_sq]

theorem vectorFiedlerExplicito_norm_sq (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    ‖vectorFiedlerExplicito d j‖^2 = ‖vectorFiedlerCrudo d j‖^2 / ‖vectorFiedlerCrudo d‖^2 := by
  have hcrudo_ne : vectorFiedlerCrudo d ≠ 0 := vectorFiedlerCrudo_ne_zero d hd
  have hnorm_pos : 0 < ‖vectorFiedlerCrudo d‖ := norm_pos_iff.mpr hcrudo_ne
  have happly : vectorFiedlerExplicito d j =
      ((‖vectorFiedlerCrudo d‖:ℂ)⁻¹) * vectorFiedlerCrudo d j := rfl
  rw [happly, norm_mul]
  rw [norm_inv, Complex.norm_real]
  rw [Real.norm_of_nonneg hnorm_pos.le]
  field_simp

/-- **Cierre físico**: `RNavaSq(d)` es exactamente `Σⱼ |ψⱼ|² · posicionCoord(j)²`
sobre `Fin d`, con `ψ = vectorFiedlerExplicito d` -- la varianza de posición
`⟨ψ|P_d²|ψ⟩` real, no solo una forma cerrada que la reproduce numéricamente. -/
theorem RNavaSq_eq_varianzaFin (d : ℕ) (hd : 2 ≤ d) :
    RNavaSq d = ∑ j : Fin d, ‖vectorFiedlerExplicito d j‖^2 * (posicionCoord d j)^2 := by
  have hd1 : 1 ≤ d := by omega
  have hterm : ∀ j : Fin d, ‖vectorFiedlerExplicito d j‖^2 * (posicionCoord d j)^2
      = (‖vectorFiedlerCrudo d j‖^2 * (posicionCoord d j)^2) / ‖vectorFiedlerCrudo d‖^2 := by
    intro j
    rw [vectorFiedlerExplicito_norm_sq d hd1 j]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, crudo_posicion_sum_eq]
  have hdm1 : (d:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    intro h; linarith
  have hcrudonorm : ‖vectorFiedlerCrudo d‖^2 = denRaw d / ((d:ℝ)-1)^2 := by
    rw [crudo_normSq_eq_sum]
    unfold denRaw
    field_simp
    apply Finset.sum_congr rfl
    intro k _; ring_nf
  rw [hcrudonorm]
  have hdm1sq : ((d:ℝ)-1)^2 ≠ 0 := pow_ne_zero 2 hdm1
  have hdenRaw_ne : denRaw d ≠ 0 := by
    rw [denRaw_eq d hd1]
    have h2 : (0:ℝ) < (d:ℝ)+1 := by positivity
    positivity
  unfold RNavaSq
  field_simp

end RNavaVarianzaFiedler

end

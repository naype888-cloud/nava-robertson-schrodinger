/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23f_MinUncertaintyTensionFour
public import NavaRobertsonCertificados.CotaCasoA
public import NavaRobertsonCertificados.CotaCasoB

/-!
# D23g — The minimum-uncertainty states of `H₄` carry tension at most `1/φ`

`D23f` exhibits a minimum-uncertainty state of `H₄` with tension exactly `1/φ = (√5 − 1)/2`.
This file proves that no minimum-uncertainty state goes higher (`tension_le_of_satura`), so
`1/φ` is the **maximum** tension compatible with saturating Robertson–Schrödinger at `d = 4`,
i.e. `3(√5 − 1)/4 ≈ 92.7 %` of the maximal tension `2/3`.

## Proof

1. **Currents.** Saturation gives `centrado T₄ = c · centrado P₄` (`D23`). Row by row this is a
   conservation law for the link currents `Iⱼ = −Im(ψ̄ⱼ ψⱼ₊₁)`: `Iⱼ = s · cⱼ(n)`, with
   `s = ρ₄ · Im c` and `cⱼ` explicit quadratics in the densities `nⱼ = |ψⱼ|²`.
2. **Cauchy–Schwarz on each link:** `Iⱼ² ≤ nⱼ nⱼ₊₁`.
3. **Tension.** `⟨K₄⟩ = (4/(3ρ₄)) Σ Iⱼ = (2/ρ₄) · s · Var P`, since `c₀ + c₁ + c₂ = (3/2) Var P`.
4. **Density inequality** (`CotaDensidades.cota_densidades`): the three link bounds force
   `4 s² (Var P)² ≤ 1`, hence `⟨K₄⟩ ≤ 1/ρ₄ = 1/φ`. By the path's reflection one may assume
   `⟨P⟩ ≥ 0`; then the sign of `H = c₁² − n₁ n₃ (1 − ⟨P⟩)²` decides whether the middle or the
   right link is used, and each case is an exact rational Positivstellensatz certificate
   (`Certificados/CotaCasoA`, `Certificados/CotaCasoB`: 207 and 229 weighted squares,
   found by semidefinite programming, rounded to exact rationals and checked by `ring`).
-/

@[expose] public section

/-! ## Density form of the bound -/

noncomputable section

namespace CotaDensidades

/-- Total weight `S = Σ nⱼ`. -/
def S (n0 n1 n2 n3 : ℝ) : ℝ := n0 + n1 + n2 + n3
/-- `⟨P⟩·S` with `P = diag(−1, −1/3, 1/3, 1)`. -/
def mP (n0 n1 n2 n3 : ℝ) : ℝ := -n0 - n1 / 3 + n2 / 3 + n3
/-- `Var P · S²`. -/
def V (n0 n1 n2 n3 : ℝ) : ℝ :=
  (n0 + n1 / 9 + n2 / 9 + n3) * S n0 n1 n2 n3 - mP n0 n1 n2 n3 ^ 2
/-- Link coefficients `cⱼ·S`: the current on link `j` is `s · cⱼ`. -/
def c0 (n0 n1 n2 n3 : ℝ) : ℝ := (S n0 n1 n2 n3 + mP n0 n1 n2 n3) * n0
def c1 (n0 n1 n2 n3 : ℝ) : ℝ :=
  (S n0 n1 n2 n3 + mP n0 n1 n2 n3) * n0 + (mP n0 n1 n2 n3 + S n0 n1 n2 n3 / 3) * n1
def c2 (n0 n1 n2 n3 : ℝ) : ℝ := (S n0 n1 n2 n3 - mP n0 n1 n2 n3) * n3
/-- The region polynomial: `H ≥ 0` — middle link is the tightest; `H ≤ 0` — the right one. -/
def H (n0 n1 n2 n3 : ℝ) : ℝ :=
  c1 n0 n1 n2 n3 ^ 2 - n1 * n3 * (S n0 n1 n2 n3 - mP n0 n1 n2 n3) ^ 2

variable {n0 n1 n2 n3 : ℝ}

/-- Case A (certificate): `m ≥ 0`, `H ≥ 0` ⟹ `4 V² n₁n₂ ≤ c₁² S²`. -/
theorem casoA (h0 : 0 ≤ n0) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) (h3 : 0 ≤ n3)
    (hm : 0 ≤ mP n0 n1 n2 n3) (hH : 0 ≤ H n0 n1 n2 n3) :
    4 * V n0 n1 n2 n3 ^ 2 * n1 * n2 ≤ c1 n0 n1 n2 n3 ^ 2 * S n0 n1 n2 n3 ^ 2 := by
  have := CertificadoH4.cota_casoA n0 n1 n2 n3 (mP n0 n1 n2 n3) (H n0 n1 n2 n3) h0 h1 h2 h3
    (by unfold mP; ring) (by unfold H c1 mP S; ring) hm hH
  rw [← sub_nonneg]
  convert this using 2
  unfold c1 V mP S; ring

/-- Case B (certificate): `m ≥ 0`, `H ≤ 0` ⟹ `4 V² n₂ ≤ (S − m)² n₃ S²`. -/
theorem casoB (h0 : 0 ≤ n0) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) (h3 : 0 ≤ n3)
    (hm : 0 ≤ mP n0 n1 n2 n3) (hH : H n0 n1 n2 n3 ≤ 0) :
    4 * V n0 n1 n2 n3 ^ 2 * n2 ≤
      (S n0 n1 n2 n3 - mP n0 n1 n2 n3) ^ 2 * n3 * S n0 n1 n2 n3 ^ 2 := by
  have := CertificadoH4.cota_casoB n0 n1 n2 n3 (mP n0 n1 n2 n3) (-H n0 n1 n2 n3) h0 h1 h2 h3
    (by unfold mP; ring) (by unfold H c1 mP S; ring) hm (by linarith)
  have hn3 := h3
  rw [← sub_nonneg]
  have e : (S n0 n1 n2 n3 - mP n0 n1 n2 n3) ^ 2 * n3 * S n0 n1 n2 n3 ^ 2 -
      4 * V n0 n1 n2 n3 ^ 2 * n2 =
      ((S n0 n1 n2 n3 - mP n0 n1 n2 n3) ^ 2 * n3 * S n0 n1 n2 n3 ^ 2 -
      4 * V n0 n1 n2 n3 ^ 2 * n2) := rfl
  convert this using 2
  unfold V mP S; ring

/-- The bound for `⟨P⟩ ≥ 0`. -/
theorem cota_mP_nonneg (h0 : 0 ≤ n0) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) (h3 : 0 ≤ n3)
    (hS : S n0 n1 n2 n3 = 1) (hm : 0 ≤ mP n0 n1 n2 n3) (s : ℝ)
    (k1 : (s * c1 n0 n1 n2 n3) ^ 2 ≤ n1 * n2) (k2 : (s * c2 n0 n1 n2 n3) ^ 2 ≤ n2 * n3) :
    4 * s ^ 2 * V n0 n1 n2 n3 ^ 2 ≤ 1 := by
  rcases le_or_gt (H n0 n1 n2 n3) 0 with hH | hH
  · -- right link
    have hB := casoB h0 h1 h2 h3 hm hH
    rw [hS] at hB
    have hc2 : c2 n0 n1 n2 n3 = (1 - mP n0 n1 n2 n3) * n3 := by unfold c2; rw [hS]
    rcases (mul_nonneg h2 h3).eq_or_lt with h23 | h23
    · -- n₂ n₃ = 0: then s c₂ = 0
      have hz : s * c2 n0 n1 n2 n3 = 0 := by nlinarith [sq_nonneg (s * c2 n0 n1 n2 n3)]
      rcases mul_eq_zero.mp hz with hs | hc
      · subst hs; norm_num
      · rw [hc2] at hc
        rcases mul_eq_zero.mp hc with hm1 | hn3
        · -- ⟨P⟩ = 1: all weight on site 3, Var P = 0
          have : n0 = 0 ∧ n1 = 0 ∧ n2 = 0 := by
            unfold mP at hm1; unfold S at hS; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
          obtain ⟨a, b, c⟩ := this
          have hV : V n0 n1 n2 n3 = 0 := by unfold V mP S; subst a b c; nlinarith
          rw [hV]; norm_num
        · -- n₃ = 0 and H ≤ 0 force c₁ = 0, hence n₀ = n₁ = 0 and Var P = 0
          have hc1 : c1 n0 n1 n2 n3 = 0 := by
            have hH' : c1 n0 n1 n2 n3 ^ 2 ≤ n1 * n3 * (S n0 n1 n2 n3 - mP n0 n1 n2 n3) ^ 2 := by
              unfold H at hH; linarith
            have hz : n1 * n3 * (S n0 n1 n2 n3 - mP n0 n1 n2 n3) ^ 2 = 0 := by rw [hn3]; ring
            have hsq : c1 n0 n1 n2 n3 ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
            exact pow_eq_zero_iff two_ne_zero |>.mp hsq
          have hc1' : (S n0 n1 n2 n3 + mP n0 n1 n2 n3) * n0 + (mP n0 n1 n2 n3 + S n0 n1 n2 n3 / 3) *
              n1 = 0 := hc1
          rw [hS] at hc1'
          have q0 : 0 ≤ (1 + mP n0 n1 n2 n3) * n0 := mul_nonneg (by linarith) h0
          have q1 : 0 ≤ (mP n0 n1 n2 n3 + 1 / 3) * n1 := mul_nonneg (by linarith) h1
          have q0' : (1 + mP n0 n1 n2 n3) * n0 = 0 := by nlinarith
          have ha : n0 = 0 := by
            rcases mul_eq_zero.mp q0' with h | h
            · linarith
            · exact h
          have hb : n1 = 0 := by
            have q1' : (mP n0 n1 n2 n3 + 1 / 3) * n1 = 0 := by nlinarith
            rcases mul_eq_zero.mp q1' with h | h
            · linarith
            · exact h
          have hV : V n0 n1 n2 n3 = 0 := by
            unfold V mP S; unfold S at hS; subst ha hb hn3; nlinarith
          rw [hV]; norm_num
    · -- n₂ n₃ > 0
      have : 4 * s ^ 2 * V n0 n1 n2 n3 ^ 2 * (n2 * n3) ≤ 1 * (n2 * n3) := by
        have := mul_le_mul_of_nonneg_left hB (mul_nonneg (sq_nonneg s) h3)
        rw [hc2] at k2
        nlinarith
      exact le_of_mul_le_mul_right this h23
  · -- middle link
    have hA := casoA h0 h1 h2 h3 hm hH.le
    rw [hS] at hA
    rcases (mul_nonneg h1 h2).eq_or_lt with h12 | h12
    · have hz : s * c1 n0 n1 n2 n3 = 0 := by nlinarith [sq_nonneg (s * c1 n0 n1 n2 n3)]
      rcases mul_eq_zero.mp hz with hs | hc
      · subst hs; norm_num
      · -- c₁ = 0 contradicts H > 0
        exfalso; unfold H at hH; rw [hc] at hH
        nlinarith [mul_nonneg (mul_nonneg h1 h3) (sq_nonneg (S n0 n1 n2 n3 - mP n0 n1 n2 n3))]
    · have : 4 * s ^ 2 * V n0 n1 n2 n3 ^ 2 * (n1 * n2) ≤ 1 * (n1 * n2) := by
        have := mul_le_mul_of_nonneg_left hA (sq_nonneg s)
        nlinarith
      exact le_of_mul_le_mul_right this h12

/-- **Density form of the bound.** If on every link `(s cⱼ)² ≤ nⱼ nⱼ₊₁` (current bounded by
Cauchy–Schwarz), then `4 s² (Var P)² ≤ 1`. -/
theorem cota_densidades (h0 : 0 ≤ n0) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) (h3 : 0 ≤ n3)
    (hS : S n0 n1 n2 n3 = 1) (s : ℝ)
    (k0 : (s * c0 n0 n1 n2 n3) ^ 2 ≤ n0 * n1) (k1 : (s * c1 n0 n1 n2 n3) ^ 2 ≤ n1 * n2)
    (k2 : (s * c2 n0 n1 n2 n3) ^ 2 ≤ n2 * n3) :
    4 * s ^ 2 * V n0 n1 n2 n3 ^ 2 ≤ 1 := by
  rcases le_total 0 (mP n0 n1 n2 n3) with hm | hm
  · exact cota_mP_nonneg h0 h1 h2 h3 hS hm s k1 k2
  · -- mirror n ↦ (n₃, n₂, n₁, n₀)
    have r := cota_mP_nonneg h3 h2 h1 h0 (by unfold S at *; linarith)
      (by unfold mP at *; linarith) s
      (by have e : c1 n3 n2 n1 n0 = c1 n0 n1 n2 n3 := by unfold c1 mP S; ring
          rw [e]; linarith)
      (by have e : c2 n3 n2 n1 n0 = c0 n0 n1 n2 n3 := by unfold c2 c0 mP S; ring
          rw [e]; linarith)
    have e : V n3 n2 n1 n0 = V n0 n1 n2 n3 := by unfold V mP S; ring
    rwa [e] at r

end CotaDensidades

end

/-! ## From a minimum-uncertainty state to the density form -/

noncomputable section

namespace CotaMinimaIncertidumbreCuatro

open TransportePosicion NavaRobertsonSchrodingerEDUI ConstructorEspectralTP SaturacionAutovectores
open IncertidumbreMinimaCuatro CotaDensidades Complex

/-- In coordinates, the tension of `ψ ∈ H₄` is `(4/(3ρ₄)) · (I₀ + I₁ + I₂)`, where
`Iⱼ = −Im(ψ̄ⱼ ψⱼ₊₁)` is the current on link `j`. -/
theorem tension_corrientes (ψ : Hd 4) :
    SobranteIntermedio.tension 4 ψ =
      4 / (3 * rho 4) * (((ψ 0).im * (ψ 1).re - (ψ 0).re * (ψ 1).im) +
        ((ψ 1).im * (ψ 2).re - (ψ 1).re * (ψ 2).im) +
        ((ψ 2).im * (ψ 3).re - (ψ 2).re * (ψ 3).im)) := by
  have hr := rho_cuatro_pos
  rw [SobranteIntermedio.tension, re_inner_KdOp, TdOp_cuatro_apply, PdOp_cuatro_apply]
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re, Complex.neg_re, Complex.neg_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  field_simp
  ring

theorem normSq_suma (ψ : Hd 4) :
    ‖ψ‖ ^ 2 = normSq (ψ 0) + normSq (ψ 1) + normSq (ψ 2) + normSq (ψ 3) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Complex.normSq_eq_norm_sq]

theorem media_P_coord (ψ : Hd 4) :
    media (PdOp 4) ψ = mP (normSq (ψ 0)) (normSq (ψ 1)) (normSq (ψ 2)) (normSq (ψ 3)) := by
  rw [media, PdOp_cuatro_apply]
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im, mP,
    Complex.normSq_apply]
  ring

/-- `|Im(z̄ w)|² ≤ |z|² |w|²`. -/
theorem corriente_cs (z w : ℂ) :
    (z.im * w.re - z.re * w.im) ^ 2 ≤ normSq z * normSq w := by
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re * w.re + z.im * w.im)]

/-- **Upper bound.** Every minimum-uncertainty state of `H₄` has tension at most `1/φ`. -/
theorem tension_le_of_satura (ψ : Hd 4) (hψ : ‖ψ‖ = 1)
    (hsat : defectGramEn (TdOp 4) (PdOp 4) ψ = 0) :
    SobranteIntermedio.tension 4 ψ ≤ (√5 - 1) / 2 := by
  have hr := rho_cuatro_pos
  have hbound : 1 / rho 4 = (√5 - 1) / 2 := by
    rw [rho_cuatro]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have : 0 < 1 + Real.sqrt 5 := by positivity
    field_simp; nlinarith [h5]
  have hpos : 0 < (√5 - 1) / 2 := by
    have : (1:ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  rcases (defectGramEn_eq_zero_iff _ _ _).mp hsat with hvar | ⟨c, hc⟩
  · -- `Var P = 0`: the tension vanishes
    have h := SaturacionAutovectores.producto_varianzas_ge_K 4 ψ
    rw [hvar, mul_zero] at h
    have : (inner ℂ ψ (KdOp 4 ψ)).re = 0 := by nlinarith [sq_nonneg (inner ℂ ψ (KdOp 4 ψ)).re]
    rw [SobranteIntermedio.tension, this]; exact hpos.le
  · -- coordinates
    set t := media (TdOp 4) ψ
    set p := media (PdOp 4) ψ
    set h := 1 / rho 4 with hh
    have hrh : rho 4 * h = 1 := by rw [hh]; field_simp
    have comp : ∀ j : Fin 4, (centrado (TdOp 4) ψ) j = c * (centrado (PdOp 4) ψ) j := by
      intro j; rw [hc]; rfl
    have e0 := comp 0; have e1 := comp 1; have e3 := comp 3
    simp only [centrado, TdOp_cuatro_apply, PdOp_cuatro_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at e0 e1 e3
    have r0 := congrArg Complex.re e0; have i0 := congrArg Complex.im e0
    have r1 := congrArg Complex.re e1; have i1 := congrArg Complex.im e1
    have r3 := congrArg Complex.re e3; have i3 := congrArg Complex.im e3
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re,
      Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
      at r0 i0 r1 i1 r3 i3
    -- densities and currents
    set x0 := (ψ 0).re; set y0 := (ψ 0).im; set x1 := (ψ 1).re; set y1 := (ψ 1).im
    set x2 := (ψ 2).re; set y2 := (ψ 2).im; set x3 := (ψ 3).re; set y3 := (ψ 3).im
    set u := c.re; set v := c.im
    have n0d : normSq (ψ 0) = x0 ^ 2 + y0 ^ 2 := by rw [Complex.normSq_apply]; ring
    have n1d : normSq (ψ 1) = x1 ^ 2 + y1 ^ 2 := by rw [Complex.normSq_apply]; ring
    have n2d : normSq (ψ 2) = x2 ^ 2 + y2 ^ 2 := by rw [Complex.normSq_apply]; ring
    have n3d : normSq (ψ 3) = x3 ^ 2 + y3 ^ 2 := by rw [Complex.normSq_apply]; ring
    have hS : S (normSq (ψ 0)) (normSq (ψ 1)) (normSq (ψ 2)) (normSq (ψ 3)) = 1 := by
      have := normSq_suma ψ; rw [hψ] at this; unfold S; linarith
    have hp : p = mP (normSq (ψ 0)) (normSq (ψ 1)) (normSq (ψ 2)) (normSq (ψ 3)) := media_P_coord ψ
    -- current conservation (rows 0, 1, 3), scaled by h = 1/ρ₄
    have I0 : h * (y0 * x1 - x0 * y1) = v * (1 + p) * (x0 ^ 2 + y0 ^ 2) := by
      linear_combination y0 * r0 - x0 * i0
    have I1 : h * ((y1 * x2 - x1 * y2) - (y0 * x1 - x0 * y1)) =
        v * (1 / 3 + p) * (x1 ^ 2 + y1 ^ 2) := by
      linear_combination y1 * r1 - x1 * i1
    have I2 : h * (y2 * x3 - x2 * y3) = v * (1 - p) * (x3 ^ 2 + y3 ^ 2) := by
      linear_combination -(y3 * r3 - x3 * i3)
    -- currents are s · cⱼ with s = v ρ₄
    set N0 := normSq (ψ 0); set N1 := normSq (ψ 1); set N2 := normSq (ψ 2); set N3 := normSq (ψ 3)
    set sc := v * rho 4
    have hc0 : c0 N0 N1 N2 N3 = (1 + p) * N0 := by unfold c0; rw [hS, ← hp]
    have hc1 : c1 N0 N1 N2 N3 = (1 + p) * N0 + (p + 1 / 3) * N1 := by
      unfold c1; rw [hS, ← hp]
    have hc2 : c2 N0 N1 N2 N3 = (1 - p) * N3 := by unfold c2; rw [hS, ← hp]
    have J0 : y0 * x1 - x0 * y1 = sc * c0 N0 N1 N2 N3 := by
      rw [hc0, n0d]; linear_combination (rho 4) * I0 - (y0 * x1 - x0 * y1) * hrh
    have J1 : y1 * x2 - x1 * y2 = sc * c1 N0 N1 N2 N3 := by
      rw [hc1, n0d, n1d]
      linear_combination (rho 4) * I1 + (rho 4) * I0 - (y1 * x2 - x1 * y2) * hrh
    have J2 : y2 * x3 - x2 * y3 = sc * c2 N0 N1 N2 N3 := by
      rw [hc2, n3d]; linear_combination (rho 4) * I2 - (y2 * x3 - x2 * y3) * hrh
    -- Cauchy–Schwarz on each link
    have k0 : (sc * c0 N0 N1 N2 N3) ^ 2 ≤ N0 * N1 := by rw [← J0]; exact corriente_cs _ _
    have k1 : (sc * c1 N0 N1 N2 N3) ^ 2 ≤ N1 * N2 := by rw [← J1]; exact corriente_cs _ _
    have k2 : (sc * c2 N0 N1 N2 N3) ^ 2 ≤ N2 * N3 := by rw [← J2]; exact corriente_cs _ _
    have hN0 : 0 ≤ N0 := Complex.normSq_nonneg _
    have hN1 : 0 ≤ N1 := Complex.normSq_nonneg _
    have hN2 : 0 ≤ N2 := Complex.normSq_nonneg _
    have hN3 : 0 ≤ N3 := Complex.normSq_nonneg _
    have key := cota_densidades hN0 hN1 hN2 hN3 hS sc k0 k1 k2
    -- tension = (2/ρ₄) s V
    have hsum : c0 N0 N1 N2 N3 + c1 N0 N1 N2 N3 + c2 N0 N1 N2 N3 = 3 / 2 * V N0 N1 N2 N3 := by
      unfold c0 c1 c2 V mP S; ring
    have ht : SobranteIntermedio.tension 4 ψ = 2 / rho 4 * (sc * V N0 N1 N2 N3) := by
      rw [tension_corrientes]
      have : (y0 * x1 - x0 * y1) + (y1 * x2 - x1 * y2) + (y2 * x3 - x2 * y3) =
          sc * (3 / 2 * V N0 N1 N2 N3) := by rw [J0, J1, J2, ← hsum]; ring
      rw [this]; field_simp; ring
    have hX : (2 * (sc * V N0 N1 N2 N3)) ^ 2 ≤ 1 := by
      have e : (2 * (sc * V N0 N1 N2 N3)) ^ 2 = 4 * sc ^ 2 * V N0 N1 N2 N3 ^ 2 := by ring
      rw [e]; exact key
    have h2 : 2 * (sc * V N0 N1 N2 N3) ≤ 1 := (abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hX)).2
    rw [ht, ← hbound, hh, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]
    exact h2

end CotaMinimaIncertidumbreCuatro

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap

/-!
# D23f — A minimum-uncertainty state of `H_4` with tension `1/φ`

Minimum-uncertainty states exist in every dimension and carry transport, and for `d ≥ 4` none
has maximal tension (`D23`, `D23b`, `D23d`). At `d = 4`,
`ψ♭ = (1/(2√2)) (1, e^{−iπ/3}√3, e^{−i5π/6}√3, e^{iπ/2})` saturates Robertson–Schrödinger with
tension `1/φ`. That `1/φ` is the largest such tension is `D23g`, in the separate target
`NavaRobertsonCertificados`.

## Main results

- `MinUncertaintyFour.Td_psiSat_eq` : `T₄ ψ♭ = c · P₄ ψ♭`, `c = (−√3 + 3i)/(2ρ₄)`, `ρ₄ = φ`.
- `MinUncertaintyFour.saturated_psiSat` : `ψ♭` saturates Robertson–Schrödinger.
- `MinUncertaintyFour.tension_psiSat` : `⟨K₄⟩ = (√5 − 1)/2 = 1/φ`, that is `3(√5 − 1)/4` of the
  maximal tension `2/3` (`tension_psiSat_fraction`).
-/

@[expose] public noncomputable section

open Real Complex TransportPosition NRSInequality SpectralExtremal
open EigenvectorSaturation

namespace MinUncertaintyFour

/-! ## 1. `T₄`, `P₄` in coordinates -/

theorem rho_four : rho 4 = (1 + √5) / 2 := by
  rw [rho]
  rw [show Real.pi / ((4 : ℕ) + 1 : ℝ) = Real.pi / 5 by norm_num, Real.cos_pi_div_five]
  ring

theorem rho_four_pos : 0 < rho 4 := by
  rw [rho_four]; positivity

theorem TdOp_four_apply (u : Hd 4) :
    TdOp 4 u = WithLp.toLp 2 ![u 1 / (rho 4 : ℂ), (u 0 + u 2) / (rho 4 : ℂ),
      (u 1 + u 3) / (rho 4 : ℂ), u 2 / (rho 4 : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [TdOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Td, Ad,
      MinStep] <;> ring

theorem PdOp_four_apply (u : Hd 4) :
    PdOp 4 u = WithLp.toLp 2 ![-u 0, -(u 1 / 3), u 2 / 3, u 3] := by
  ext i
  fin_cases i <;>
    simp [PdOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Pd, posCoord] <;> ring

/-! ## 2. The state `ψ♭` -/

/-- `a = 1/(2√2) = √2/4`. -/
def a : ℂ := ((√2 / 4 : ℝ) : ℂ)

/-- `√3` as a complex number. -/
def s3 : ℂ := ((√3 : ℝ) : ℂ)

theorem s3_sq : s3 ^ 2 = 3 := by
  rw [s3, ← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem a_sq : a ^ 2 = 1 / 8 := by
  rw [a, ← ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem conj_a : (starRingEnd ℂ) a = a := Complex.conj_ofReal _

theorem conj_s3 : (starRingEnd ℂ) s3 = s3 := Complex.conj_ofReal _

/-- The minimum-uncertainty state `ψ♭` of `H_4`. -/
def psiSat : Hd 4 :=
  WithLp.toLp 2 ![a, a * ((s3 - 3 * I) / 2), a * ((-3 - s3 * I) / 2), a * I]

/-- `c = (−√3 + 3i)/(2ρ₄)`. -/
def cSat : ℂ := (-s3 + 3 * I) / (2 * (rho 4 : ℂ))

theorem rho_ne : (rho 4 : ℂ) ≠ 0 := ofReal_ne_zero.mpr rho_four_pos.ne'

/-- `T₄ ψ♭ = c · P₄ ψ♭`. -/
theorem Td_psiSat_eq : TdOp 4 psiSat = cSat • PdOp 4 psiSat := by
  rw [TdOp_four_apply, PdOp_four_apply]
  have hr := rho_ne
  have h3 := s3_sq
  ext i
  fin_cases i <;> simp [psiSat, cSat] <;> field_simp <;> ring_nf <;>
    simp only [I_sq, h3] <;> ring

/-! ## 3. Inner products -/

/-- `ψ♭` is a unit vector. -/
theorem inner_psiSat_self : inner ℂ psiSat psiSat = 1 := by
  have h3 := s3_sq
  have ha := a_sq
  simp only [psiSat, PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [map_mul, map_div₀, map_sub, map_neg, conj_I, conj_a, conj_s3, map_ofNat]
  ring_nf
  simp only [I_sq, h3, ha]
  norm_num

theorem norm_psiSat : ‖psiSat‖ = 1 := by
  have h' : ‖psiSat‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_psiSat_self]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h'

theorem inner_psiSat_P : inner ℂ psiSat (PdOp 4 psiSat) = 0 := by
  have h3 := s3_sq
  have ha := a_sq
  rw [PdOp_four_apply]
  simp only [psiSat, PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [map_mul, map_div₀, map_sub, map_neg, conj_I, conj_a, conj_s3, map_ofNat]
  ring_nf
  simp only [I_sq, h3, ha]
  norm_num

theorem inner_P_psiSat_P : inner ℂ (PdOp 4 psiSat) (PdOp 4 psiSat) = 1 / 3 := by
  have h3 := s3_sq
  have ha := a_sq
  rw [PdOp_four_apply]
  simp only [psiSat, PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [map_mul, map_div₀, map_sub, map_neg, conj_I, conj_a, conj_s3, map_ofNat]
  ring_nf
  simp only [I_sq, h3, ha]
  norm_num

/-! ## 4. Minimum uncertainty with transport -/

theorem mean_P_psiSat : mean (PdOp 4) psiSat = 0 := by
  rw [mean, inner_psiSat_P]; simp

theorem mean_T_psiSat : mean (TdOp 4) psiSat = 0 := by
  rw [mean, Td_psiSat_eq, inner_smul_right, inner_psiSat_P]; simp

/-- `ψ♭` saturates Robertson–Schrödinger: the Gram defect of `(T₄, P₄)` vanishes. -/
theorem saturated_psiSat : gramDefectAt (TdOp 4) (PdOp 4) psiSat = 0 := by
  rw [gramDefectAt_eq_zero_iff]
  refine Or.inr ⟨cSat, ?_⟩
  rw [centered, centered, mean_T_psiSat, mean_P_psiSat]
  simpa using Td_psiSat_eq

/-- The tension of `ψ♭` is `1/ρ₄`. -/
theorem tension_psiSat_rho : NearMaxTension.tension 4 psiSat = 1 / rho 4 := by
  have hr := rho_four_pos
  rw [NearMaxTension.tension, re_inner_KdOp, Td_psiSat_eq, inner_smul_left,
    inner_P_psiSat_P, cSat]
  simp only [map_div₀, map_add, map_neg, map_mul, conj_s3, conj_I, map_ofNat,
    Complex.conj_ofReal]
  have hc : (-s3 + 3 * -I) / (2 * (rho 4 : ℂ)) * (1 / 3) =
      ((-(√3) / (6 * rho 4) : ℝ) : ℂ) + ((-1 / (2 * rho 4) : ℝ) : ℂ) * I := by
    rw [s3]; push_cast; field_simp; ring
  rw [hc]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  field_simp
  ring

/-- The tension of `ψ♭` is `(√5 − 1)/2 = 1/φ`. -/
theorem tension_psiSat : NearMaxTension.tension 4 psiSat = (√5 - 1) / 2 := by
  rw [tension_psiSat_rho, rho_four]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 1 + Real.sqrt 5 := by positivity
  field_simp
  nlinarith [h5]

/-- `ψ♭` carries `3(√5 − 1)/4 ≈ 92.7 %` of the maximal tension `2/3`. -/
theorem tension_psiSat_fraction :
    NearMaxTension.tension 4 psiSat / (2 / ((4 : ℕ) - 1 : ℝ)) = 3 * (√5 - 1) / 4 ∧
      NearMaxTension.tension 4 psiSat < 2 / ((4 : ℕ) - 1 : ℝ) := by
  rw [tension_psiSat]
  have h5 : Real.sqrt 5 < 7 / 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · push_cast; ring
  · push_cast; linarith

end MinUncertaintyFour

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49d_RobertsonDeterminantBand
public import NavaRobertsonIndependent.Mathematics.D1_CauchyGramInequality

/-!
# D49e — The defect of every axis in the band, for every state

`D44` forces the Robertson–Schrödinger defect of a state of `H_d` whose speed lies in the band
`Ϙ(d) = (v*(d), 1]`. Here the state `Φ` lives on a product `ℂ^d ⊗ ℂ^β` (an axis of the cube and
the rest) and may be entangled across the factors. The defect of the pair `(T, P)` of the axis
is still positive.

The argument: a vanishing defect makes the fluctuation vectors parallel,
`(T − αP − μ)Φ = 0`. Column by column this is the recurrence of the tridiagonal `T_d − αP_d`,
whose solutions are fixed by their first entry; so every column is a multiple of one vector `φ`
and `Φ = φ ⊗ χ` is a product. Then the defect of `Φ` is the defect of `φ` and its speed is the
speed of `φ`, which lies in `Ϙ(d)`: the defect is positive (`D44`), a contradiction. Entanglement
across axes cannot hide the defect of an axis.

## Main results

- `AxisDefectEntangled.eq_zero_of_eigen` : a solution of `T_d v = αP_d v + μv` with `v₀ = 0`
  vanishes.
- `AxisDefectEntangled.exists_prodAlong_of_eigen` : a state whose columns solve it is a product.
- `AxisDefectEntangled.gramDefect_pos_of_band` : speed in `Ϙ(d)` forces the defect of the axis,
  for every unit state of the product.
- `AxisDefectEntangled.axis_defects_pos` : on the cube, speeds in `Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)` force
  the three defects, and their product is positive.
-/

@[expose] public noncomputable section

open TransportPosition NearMaxTension GroupVelocity VelocityBand PathGraph3DNRS CauchyGram
open RobertsonDeterminant RobertsonDeterminant3D GramStep

namespace AxisDefectEntangled

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] {d : ℕ}

/-! ## 1. Columns -/

/-- The column `r` of `Φ` along the axis: `i ↦ Φ(i, r)`. -/
def col (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) : Fin d → ℂ :=
  fun i => Φ (e.symm (i, r))

/-- A lifted operator acts column by column. -/
theorem liftAlong_apply_col (e : ι ≃ Fin d × β) (A : Matrix (Fin d) (Fin d) ℂ)
    (Φ : EuclideanSpace ℂ ι) (i : Fin d) (r : β) :
    Matrix.toEuclideanLin (liftAlong e A) Φ (e.symm (i, r)) = A.mulVec (col e Φ r) i := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, liftAlong,
    Matrix.of_apply, Equiv.apply_symm_apply, col]
  rw [Fintype.sum_equiv e _ (fun x => A i x.1 * (if r = x.2 then 1 else 0) * Φ (e.symm x))
    (fun q => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_ite, ite_mul, Finset.sum_ite_eq]

/-! ## 2. The recurrence of `T_d − αP_d` -/

/-- A solution of `T_d v = αP_d v + μv` with first entry `0` vanishes. -/
theorem eq_zero_of_eigen (hd : 2 ≤ d) {α μ : ℂ} {v : Fin d → ℂ}
    (h : ∀ i, (Td d).mulVec v i = α * (Pd d).mulVec v i + μ * v i) (h0 : v ⟨0, by omega⟩ = 0) :
    v = 0 := by
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  have key : ∀ n (hn : n < d), v ⟨n, hn⟩ = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases n with _ | m
      · exact h0
      · have hm : m < d := by omega
        have h2 : (if h : 0 < m then v ⟨m - 1, by omega⟩ else 0) = 0 := by
          split_ifs with h
          exacts [ih (m - 1) (by omega) _, rfl]
        have hrow := h ⟨m, hm⟩
        simp only [Td_mulVec, Ad_mulVec_apply, Pd_mulVec, hn, ↓reduceDIte] at hrow
        rw [h2, ih m (by omega) hm] at hrow
        simpa [hρ] using hrow
  funext i
  exact key i.val i.isLt

omit [Fintype β] [DecidableEq ι] [DecidableEq β] in
/-- A state whose columns all solve `T_d v = αP_d v + μv` is a product `φ ⊗ χ`. -/
theorem exists_prodAlong_of_eigen (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (hΦ : Φ ≠ 0) {α μ : ℂ}
    (h : ∀ r i, (Td d).mulVec (col e Φ r) i = α * (Pd d).mulVec (col e Φ r) i + μ * col e Φ r i) :
    ∃ (φ : EuclideanSpace ℂ (Fin d)) (χ : EuclideanSpace ℂ β), Φ = prodAlong e φ χ := by
  obtain ⟨p, hp⟩ : ∃ p, Φ p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΦ (by ext p; simp [hc])
  set i₀ : Fin d := ⟨0, by omega⟩
  set v := col e Φ (e p).2
  have hv0 : v i₀ ≠ 0 := by
    intro h0
    have hz := congrFun (eq_zero_of_eigen hd (h (e p).2) h0) (e p).1
    simp [col] at hz
    exact hp hz
  have hprop (r : β) (i : Fin d) : col e Φ r i = col e Φ r i₀ / v i₀ * v i := by
    have hu := eq_zero_of_eigen hd (α := α) (μ := μ)
      (v := v i₀ • col e Φ r - col e Φ r i₀ • v) (fun i => by
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          h r i, h (e p).2 i, v]
        ring) (by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
    have hi := congrFun hu i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    field_simp
    linear_combination hi
  refine ⟨WithLp.toLp 2 v, WithLp.toLp 2 fun r => col e Φ r i₀ / v i₀, ?_⟩
  ext q
  have hq := hprop (e q).2 (e q).1
  simp only [col, Prod.mk.eta, Equiv.symm_apply_apply] at hq
  rw [prodAlong_apply, hq]
  simp [mul_comm, col]

/-! ## 3. The defect of an axis in the band -/

/-- **The defect of an axis in the band, for every state.** If the speed of the axis lies in
`Ϙ(d)`, the Gram defect of `(T, P)` on that axis is positive, whether or not `Φ` is entangled
with the rest. -/
theorem gramDefect_pos_of_band (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (hΦ : ‖Φ‖ = 1)
    (hb : |((d : ℝ) - 1) / 2 * tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ| ∈ Ϙ d) :
    0 < gramDefectC (centeredG (Matrix.toEuclideanLin (liftAlong e (Td d))) Φ)
      (centeredG (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ) := by
  set T := Matrix.toEuclideanLin (liftAlong e (Td d))
  set P := Matrix.toEuclideanLin (liftAlong e (Pd d))
  have hTs : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian e (Td_isHermitian d))
  have hPs : P.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian e (Pd_isHermitian d))
  have hv0 : 0 ≤ threshold d := by
    obtain ⟨ψ, -, -, hs⟩ := (threshold_isGreatest (d := d) (by omega)).1
    rw [← hs]
    exact abs_nonneg _
  rcases (gramDefectC_nonneg (centeredG T Φ) (centeredG P Φ)).lt_or_eq with h | h
  · exact h
  exfalso
  by_cases hcP : centeredG P Φ = 0
  · have ht := tensionG_eq (Φ := Φ) hTs hPs
    rw [hcP, inner_zero_right, Complex.zero_im, mul_zero] at ht
    rw [ht, mul_zero, abs_zero] at hb
    exact absurd hb.1 (not_lt.mpr hv0)
  have hcs : ‖inner ℂ (centeredG P Φ) (centeredG T Φ)‖ = ‖centeredG P Φ‖ * ‖centeredG T Φ‖ := by
    rw [norm_inner_symm, ((gramDefectC_eq_zero_iff _ _).mp h.symm), mul_comm]
  obtain ⟨α, hα⟩ := Or.resolve_left
    (((norm_inner_eq_norm_tfae ℂ (centeredG P Φ) (centeredG T Φ)).out 1 3).mp hcs) hcP
  have hcol (r : β) (i : Fin d) : (Td d).mulVec (col e Φ r) i =
      α * (Pd d).mulVec (col e Φ r) i + ((meanG T Φ : ℂ) - α * meanG P Φ) * col e Φ r i := by
    have hx := congrArg (fun x : EuclideanSpace ℂ ι => x (e.symm (i, r))) hα
    simp only [centeredG, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hx
    rw [liftAlong_apply_col, liftAlong_apply_col] at hx
    simp only [col] at hx ⊢
    linear_combination hx
  have hΦ0 : Φ ≠ 0 := by
    rintro rfl
    simp at hΦ
  obtain ⟨φ, χ, hprod⟩ := exists_prodAlong_of_eigen hd e hΦ0 hcol
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hΦ0
    rw [hprod]
    ext p
    simp [prodAlong_apply]
  have hn : (‖φ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hφ0)
  set φ' := (‖φ‖ : ℂ)⁻¹ • φ
  set χ' := (‖φ‖ : ℂ) • χ
  have hprod' : Φ = prodAlong e φ' χ' := by
    rw [hprod]
    ext p
    simp only [prodAlong_apply, φ', χ', PiLp.smul_apply, smul_eq_mul]
    field_simp
  have hφ' : ‖φ'‖ = 1 := by
    simp only [φ', norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ0)
  have hχ' : ‖χ'‖ = 1 := by
    have hi := inner_prodAlong e φ' φ' χ' χ'
    rw [← hprod', inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hΦ, hφ'] at hi
    push_cast at hi
    have hsq : ‖χ'‖ ^ 2 = 1 := by
      have h2 : ((‖χ'‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination -hi
      exact_mod_cast h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq
  have hdef : gramDefectC (centeredG T Φ) (centeredG P Φ) = surplus d φ' := by
    simp only [T, P]
    rw [hprod', centeredG_lift e hχ', centeredG_lift e hχ']
    unfold gramDefectC varianceC
    rw [norm_sq_prodAlong e _ _ hχ', norm_sq_prodAlong e _ _ hχ', inner_prodAlong,
      inner_self_of_norm_one hχ', mul_one]
    rfl
  have hvel : velocity d φ' = ((d : ℝ) - 1) / 2 * tensionG T P Φ := by
    simp only [T, P]
    rw [hprod', tensionG_lift e hχ']
    rfl
  have hs := surplus_pos_of_mem_band hd φ' hφ' (by rwa [hvel])
  linarith

/-! ## 4. The three axes of the cube -/

variable {dx dy dz : ℕ}

/-- **The three defects of the cube in the band, for every state.** If the speeds on `x`, `y`,
`z` lie in `Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)`, the three defects are positive, and so is their product. -/
theorem axis_defects_pos (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H3D dx dy dz}
    (hΦ : ‖Φ‖ = 1) (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy)
    (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    0 < gramDefectC (centeredG (TX dx dy dz) Φ) (centeredG (PX dx dy dz) Φ) *
      gramDefectC (centeredG (TY dx dy dz) Φ) (centeredG (PY dx dy dz) Φ) *
        gramDefectC (centeredG (TZ dx dy dz) Φ) (centeredG (PZ dx dy dz) Φ) := by
  have h1 := gramDefect_pos_of_band hx (eX dx dy dz) hΦ hbx
  have h2 := gramDefect_pos_of_band hy (eY dx dy dz) hΦ hby
  have h3 := gramDefect_pos_of_band hz (eZ dx dy dz) hΦ hbz
  exact mul_pos (mul_pos h1 h2) h3

end AxisDefectEntangled

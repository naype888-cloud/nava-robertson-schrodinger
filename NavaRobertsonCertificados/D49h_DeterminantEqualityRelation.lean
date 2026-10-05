/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49f_MaxTensionCube
public import NavaRobertsonIndependent.Mathematics.D49g_RobertsonDeterminantEquality
public import Mathlib.Analysis.Matrix.Order

/-!
# D49h — Equality in det|NRS³ needs a relation among the three tensions

Suppose the speeds on `x`, `y`, `z` lie in the band and det|NRS³ is an equality,
`det Σ = |det Ω|`. By `D49g` the kernel `N` of the Gram matrix `Σ + iΩ` of the six fluctuation
vectors has dimension at least `3`. Each `a ∈ N` is a relation `Σ a_p (A_p − ⟨A_p⟩)Φ = 0`, so `Φ`
is an eigenvector of `L_a = Σ a_p A_p`, and `[L_a, L_b]Φ = 0` for `a, b ∈ N`. Pairs of different
axes commute, so `[L_a, L_b] = Σ_i σ_i(a, b) [T_i, P_i]` with
`σ_i(a, b) = a(T_i) b(P_i) − a(P_i) b(T_i)`.

If every `σ_i` vanished on `N`, the part of `N` on each axis would be a line; three lines and
`dim N ≥ 3` leave a relation on one axis alone, which is a vanishing defect of that axis,
excluded in the band (`D49e`). Hence equality forces

  `σ_x [T_x, P_x] Φ + σ_y [T_y, P_y] Φ + σ_z [T_z, P_z] Φ = 0` with `σ ≠ 0`.

In the continuum the commutators are one constant and such a relation is free; here
`i[T, P] = K` is an operator. Whether this relation can hold in the band is not decided here.

## Main results

- `DeterminantEqualityRelation.exists_single_axis` : the linear algebra of the three lines.
- `DeterminantEqualityRelation.commutator_sum` : `[L_a, L_b] = Σ_i σ_i(a, b) [T_i, P_i]`.
- `DeterminantEqualityRelation.exists_sigma_of_det_eq` : equality in the band gives the relation.
-/

@[expose] public noncomputable section

open Matrix TransportPosition NRSInequality NearMaxTension GroupVelocity PathGraph3DNRS
open RobertsonDeterminant RobertsonDeterminant3D AxisDefectEntangled VelocityBand CauchyGram
open SpectralExtremal
open scoped ComplexOrder

namespace DeterminantEqualityRelation

/-! ## 1. Three lines in `ℂ² ⊕ ℂ² ⊕ ℂ²` -/

/-- The part of a coefficient vector on axis `i`. -/
def restr (i : Fin 3) : (Fin 2 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 × Fin 3 → ℂ) :=
  LinearMap.pi fun p => if p.2 = i then LinearMap.proj p else 0

theorem restr_apply (i : Fin 3) (a : Fin 2 × Fin 3 → ℂ) (p : Fin 2 × Fin 3) :
    restr i a p = if p.2 = i then a p else 0 := by
  simp only [restr, LinearMap.pi_apply]
  split_ifs <;> simp

/-- If the `2 × 2` determinants `σ_i` vanish on `N`, the part of `N` on axis `i` is a line. -/
theorem exists_line (N : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (i : Fin 3)
    (hσ : ∀ a ∈ N, ∀ b ∈ N, a (0, i) * b (1, i) - a (1, i) * b (0, i) = 0) :
    ∃ g, ∀ a ∈ N, ∃ t : ℂ, restr i a = t • g := by
  by_cases h : ∃ a₀ ∈ N, a₀ (0, i) ≠ 0 ∨ a₀ (1, i) ≠ 0
  · obtain ⟨a₀, ha₀, h0⟩ := h
    refine ⟨restr i a₀, fun a ha => ?_⟩
    have hs := hσ a₀ ha₀ a ha
    rcases h0 with h0 | h0
    · refine ⟨a (0, i) / a₀ (0, i), ?_⟩
      ext ⟨s, j⟩
      simp only [restr_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs with hj
      · subst hj
        rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
        · field_simp
        · field_simp
          linear_combination hs
      · simp
    · refine ⟨a (1, i) / a₀ (1, i), ?_⟩
      ext ⟨s, j⟩
      simp only [restr_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs with hj
      · subst hj
        rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
        · field_simp
          linear_combination -hs
        · field_simp
      · simp
  · push Not at h
    refine ⟨0, fun a ha => ⟨0, ?_⟩⟩
    ext ⟨s, j⟩
    simp only [restr_apply, smul_zero, Pi.zero_apply]
    split_ifs with hj
    · subst hj
      rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
      exacts [(h a ha).1, (h a ha).2]
    · rfl

/-- **Three lines and dimension three leave a vector on one axis.** -/
theorem exists_single_axis (N : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (hdim : 3 ≤ Module.finrank ℂ N)
    (hσ : ∀ a ∈ N, ∀ b ∈ N, ∀ i, a (0, i) * b (1, i) - a (1, i) * b (0, i) = 0) :
    ∃ a ∈ N, a ≠ 0 ∧ ∀ s i, i ≠ 2 → a (s, i) = 0 := by
  obtain ⟨g₀, hg₀⟩ := exists_line N 0 fun a ha b hb => hσ a ha b hb 0
  obtain ⟨g₁, hg₁⟩ := exists_line N 1 fun a ha b hb => hσ a ha b hb 1
  set P := (restr 0 + restr 1) ∘ₗ N.subtype
  have hrange : LinearMap.range P ≤ Submodule.span ℂ (Set.range ![g₀, g₁]) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨t₀, ht₀⟩ := hg₀ x x.2
    obtain ⟨t₁, ht₁⟩ := hg₁ x x.2
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.add_apply, ht₀, ht₁]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hr : Module.finrank ℂ (LinearMap.range P) ≤ 2 :=
    (Submodule.finrank_mono hrange).trans ((finrank_range_le_card _).trans (by simp))
  have hrn := LinearMap.finrank_range_add_finrank_ker P
  have hker : LinearMap.ker P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrn
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, x.2, fun h => hx0 (Subtype.ext h), fun s i hi => ?_⟩
  have hP := congrFun (show P x = 0 from hx) (s, i)
  simp only [P, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.add_apply,
    Pi.add_apply, restr_apply, Pi.zero_apply] at hP
  fin_cases i
  · simpa using hP
  · simpa using hP
  · exact absurd rfl hi

/-! ## 2. Relations among the fluctuation vectors -/

variable {dx dy dz : ℕ} (Φ : H3D dx dy dz)

/-- The six fluctuation vectors. -/
def fluct (p : Fin 2 × Fin 3) : H3D dx dy dz := centeredG (pairs dx dy dz p) Φ

/-- The combination `L_a = Σ a_p A_p`. -/
def comb (a : Fin 2 × Fin 3 → ℂ) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  ∑ p, a p • pairs dx dy dz p

theorem sum_eq_zero_of_mulVec {a : Fin 2 × Fin 3 → ℂ} (h : gram ℂ (fluct Φ) *ᵥ a = 0) :
    ∑ p, a p • fluct Φ p = 0 := by
  have := star_dotProduct_gram_mulVec (𝕜 := ℂ) (fluct Φ) a a
  rw [h, dotProduct_zero, eq_comm, inner_self_eq_zero] at this
  exact this

theorem comb_eigen {a : Fin 2 × Fin 3 → ℂ} (h : ∑ p, a p • fluct Φ p = 0) :
    comb a Φ = (∑ p, a p * meanG (pairs dx dy dz p) Φ) • Φ := by
  simp only [fluct, centeredG, smul_sub, Finset.sum_sub_distrib, smul_smul] at h
  simp only [comb, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
  exact sub_eq_zero.mp h

/-- **`[L_a, L_b] = Σ_i σ_i(a, b) [T_i, P_i]`**: pairs of different axes commute. -/
theorem commutator_sum (a b : Fin 2 × Fin 3 → ℂ) :
    comb a (comb b Φ) - comb b (comb a Φ) =
      ∑ i, (a (0, i) * b (1, i) - a (1, i) * b (0, i)) •
        opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ := by
  have hc (s t : Fin 2) (i j : Fin 3) (h : i ≠ j) :
      pairs dx dy dz (t, j) (pairs dx dy dz (s, i) Φ) =
        pairs dx dy dz (s, i) (pairs dx dy dz (t, j) Φ) := by
    have := congrArg (fun L => L Φ) (commutator_pairs dx dy dz (a := s) (b := t) h)
    simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      sub_eq_zero] at this
    exact this.symm
  have h01 (s t : Fin 2) := hc s t 0 1 (by decide)
  have h02 (s t : Fin 2) := hc s t 0 2 (by decide)
  have h12 (s t : Fin 2) := hc s t 1 2 (by decide)
  simp only [comb, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, opCommutator,
    LinearMap.sub_apply, LinearMap.comp_apply, h01, h02, h12]
  module

/-! ## 3. Equality in the band -/

theorem gramDefectC_eq_zero_of_rel {x y : H3D dx dy dz} {α β : ℂ} (h : α • x + β • y = 0)
    (hαβ : α ≠ 0 ∨ β ≠ 0) : gramDefectC x y = 0 := by
  rw [gramDefectC_eq_zero_iff]
  rcases hαβ with hα | hβ
  · have hx : x = (-β / α) • y := by
      have h' : α • x = -(β • y) := eq_neg_of_add_eq_zero_left h
      calc x = α⁻¹ • (α • x) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = (-β / α) • y := by
          rw [h', smul_neg, smul_smul, ← neg_smul, neg_div, div_eq_inv_mul]
    rw [norm_inner_symm, mul_comm]
    exact ((norm_inner_eq_norm_tfae ℂ y x).out 3 1).mp (Or.inr (⟨_, hx⟩ : ∃ r : ℂ, x = r • y))
  · have hy : y = (-α / β) • x := by
      have h' : β • y = -(α • x) := eq_neg_of_add_eq_zero_right h
      calc y = β⁻¹ • (β • y) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = (-α / β) • x := by
          rw [h', smul_neg, smul_smul, ← neg_smul, neg_div, div_eq_inv_mul]
    exact ((norm_inner_eq_norm_tfae ℂ x y).out 3 1).mp (Or.inr (⟨_, hy⟩ : ∃ r : ℂ, y = r • x))

variable {Φ}

/-- **The kernel of the Gram matrix has dimension at least three** when det|NRS³ is an equality
with the three speeds in the band. -/
theorem three_le_finrank_ker (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz)
    (heq : (covMatrix (pairs dx dy dz) Φ).det = |(imMatrix (pairs dx dy dz) Φ).det|) :
    3 ≤ Module.finrank ℂ (LinearMap.ker (gram ℂ (fluct Φ)).mulVecLin) := by
  set S := covMatrix (pairs dx dy dz) Φ
  set W := imMatrix (pairs dx dy dz) Φ
  set A : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ := S.map ((↑) : ℝ → ℂ)
  set B : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ := Complex.I • W.map ((↑) : ℝ → ℂ)
  have hG : gram ℂ (fluct Φ) = A + B := gram_centeredG (pairs dx dy dz) Φ
  have hGt : (gram ℂ (fluct Φ))ᵀ = A - B := transpose_gram_centeredG (pairs dx dy dz) Φ
  have h₂ : (A + B).PosSemidef := hG ▸ posSemidef_gram ℂ (fluct Φ)
  have h₁ : (A - B).PosSemidef := hGt ▸ (posSemidef_gram ℂ (fluct Φ)).transpose
  have hS : A.PosSemidef := by
    have h := (h₁.add h₂).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
    convert h using 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    ring
  have hB : B.IsHermitian := by
    rw [show B = A - (A - B) by abel]
    exact hS.1.sub h₁.1
  -- the three tensions are not zero in the band
  have hv0 (d : ℕ) (hd : 2 ≤ d) {v : ℝ} (hv : |v| ∈ Ϙ d) : v ≠ 0 := by
    rintro rfl
    obtain ⟨ψ, -, -, hs⟩ := (threshold_isGreatest (d := d) (by omega)).1
    have h0 : 0 ≤ threshold d := hs ▸ abs_nonneg _
    have := hv.1
    rw [abs_zero] at this
    linarith
  have ht (i : Fin 3) :
      tensionG (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ = -2 * omega Φ i :=
    tensionG_eq (pairs_isSymmetric dx dy dz _) (pairs_isSymmetric dx dy dz _)
  have hom0 : omega Φ 0 ≠ 0 := fun h0 => hv0 dx hx hbx (by
    show ((dx : ℝ) - 1) / 2 * tensionG (pairs dx dy dz (0, 0)) (pairs dx dy dz (1, 0)) Φ = 0
    rw [ht 0, h0, mul_zero, mul_zero])
  have hom1 : omega Φ 1 ≠ 0 := fun h0 => hv0 dy hy hby (by
    show ((dy : ℝ) - 1) / 2 * tensionG (pairs dx dy dz (0, 1)) (pairs dx dy dz (1, 1)) Φ = 0
    rw [ht 1, h0, mul_zero, mul_zero])
  have hom2 : omega Φ 2 ≠ 0 := fun h0 => hv0 dz hz hbz (by
    show ((dz : ℝ) - 1) / 2 * tensionG (pairs dx dy dz (0, 2)) (pairs dx dy dz (1, 2)) Φ = 0
    rw [ht 2, h0, mul_zero, mul_zero])
  have hdetW : |W.det| ≠ 0 := by
    rw [abs_det_imMatrix_pairs]
    exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hom0 hom1) hom2)
  have hdetA : A.det = (S.det : ℂ) := (RingHom.map_det Complex.ofRealHom S).symm
  have hA : A.PosDef :=
    (Matrix.PosSemidef.posDef_iff_det_ne_zero hS).mpr (by rw [hdetA, heq]; exact_mod_cast hdetW)
  have hW : (W.map ((↑) : ℝ → ℂ)).det = (W.det : ℂ) := (RingHom.map_det Complex.ofRealHom W).symm
  have hnorm : ‖B.det‖ = A.det.re := by
    rw [det_smul, hW, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hdetA, Complex.ofReal_re, heq]
  -- the kernel of the Gram matrix has dimension at least three
  set N := LinearMap.ker (gram ℂ (fluct Φ)).mulVecLin
  set M := LinearMap.ker (gram ℂ (fluct Φ))ᵀ.mulVecLin
  have hsup : N ⊔ M = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, z, hy, hz, rfl⟩ := exists_add_of_norm_det_eq hA hB h₁ h₂ hnorm x
    refine Submodule.add_mem_sup (LinearMap.mem_ker.mpr ?_) (LinearMap.mem_ker.mpr ?_)
    · rw [Matrix.mulVecLin_apply, hG]
      exact hy
    · rw [Matrix.mulVecLin_apply, hGt]
      exact hz
  have hNM : Module.finrank ℂ M = Module.finrank ℂ N := finrank_ker_transpose _
  show 3 ≤ Module.finrank ℂ N
  have h := Submodule.finrank_sup_add_finrank_inf_eq N M
  rw [hsup, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

/-- **Equality in det|NRS³ needs a relation among the three tensions.** If the speeds on `x`, `y`,
`z` lie in the band and `det Σ = |det Ω|`, then `Σ_i σ_i [T_i, P_i] Φ = 0` for some `σ ≠ 0`. -/
theorem exists_sigma_of_det_eq (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hΦ : ‖Φ‖ = 1)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz)
    (heq : (covMatrix (pairs dx dy dz) Φ).det = |(imMatrix (pairs dx dy dz) Φ).det|) :
    ∃ σ : Fin 3 → ℂ, σ ≠ 0 ∧
      ∑ i, σ i • opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ = 0 := by
  set N := LinearMap.ker (gram ℂ (fluct Φ)).mulVecLin
  have hdim : 3 ≤ Module.finrank ℂ N := three_le_finrank_ker hx hy hz hbx hby hbz heq
  -- if every `σ` vanished, one axis would carry a relation alone
  by_contra hcon
  push Not at hcon
  have hrel (a : Fin 2 × Fin 3 → ℂ) (ha : a ∈ N) : ∑ p, a p • fluct Φ p = 0 :=
    sum_eq_zero_of_mulVec Φ (by rw [← Matrix.mulVecLin_apply]; exact ha)
  have hσ : ∀ a ∈ N, ∀ b ∈ N, ∀ i, a (0, i) * b (1, i) - a (1, i) * b (0, i) = 0 := by
    intro a ha b hb i
    by_contra hi
    apply hcon (fun i => a (0, i) * b (1, i) - a (1, i) * b (0, i)) (fun h => hi (congrFun h i))
    rw [← commutator_sum, comb_eigen Φ (hrel b hb), comb_eigen Φ (hrel a ha), map_smul,
      map_smul, comb_eigen Φ (hrel b hb), comb_eigen Φ (hrel a ha), smul_smul, smul_smul,
      mul_comm, sub_self]
  obtain ⟨a, haN, ha0, hsupp⟩ := exists_single_axis N hdim hσ
  have hz' : a (0, 2) • fluct Φ (0, 2) + a (1, 2) • fluct Φ (1, 2) = 0 := by
    have h := hrel a haN
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, hsupp 0 0 (by decide),
      hsupp 1 0 (by decide), hsupp 0 1 (by decide), hsupp 1 1 (by decide)] using h
  have hαβ : a (0, 2) ≠ 0 ∨ a (1, 2) ≠ 0 := by
    by_contra h
    push Not at h
    apply ha0
    ext ⟨s, i⟩
    rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl <;>
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl <;>
      simp [hsupp, h]
  exact (ne_of_gt (gramDefect_pos_of_band hz (eZ dx dy dz) hΦ hbz))
    (gramDefectC_eq_zero_of_rel hz' hαβ)

end DeterminantEqualityRelation

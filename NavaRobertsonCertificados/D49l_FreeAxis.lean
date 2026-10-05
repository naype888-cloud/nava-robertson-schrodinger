/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49h_DeterminantEqualityRelation
public import NavaRobertsonIndependent.Mathematics.D47_PlatformBlindness
public import NavaRobertsonIndependent.Mathematics.D49i_TransportPositionLieClosure

/-!
# D49l — A free axis leaves no state

Equality in det|NRS³ makes `Φ` an eigenvector of every `L_a = Σ a_p A_p` with `a` in the kernel
`N` of the Gram matrix (`D49g`, `D49h`), so `[L_a, L_b] Φ = 0`. Suppose the brackets of `N`
reach one axis `i` alone: `[L_a, L_b] = σ [T_i, P_i]` with `σ ≠ 0`, and some `c ∈ N` carries
position on axis `i` but no transport there. Then `[T_i, P_i] Φ = 0`, and since `L_c Φ = λ Φ`,
also `[P_i, [T_i, P_i]] Φ = 0`. By `D49i` that bracket is `−h² T_i`, so `T_i Φ = 0`.

Transport and its commutator with position have no common vector: `T_d v = 0` and
`[T_d, P_d] v = 0` force `v = 0`. Indeed `T_d (P_d v) = 0`, so `P_d v − x₀ v` solves the
recurrence of `D49e` with first entry `0` and vanishes; `v` is then a position eigenvector,
and transport moves it (`D47`). Column by column the same holds on the cube, so `Φ = 0`.

The algebra of `T_d`, `P_d` does the work: no spectral input, no velocity hypothesis.

## Main results

- `FreeAxis.eq_zero_of_Td_C` : `T_d v = 0` and `[T_d, P_d] v = 0` give `v = 0`.
- `FreeAxis.eq_zero_of_lift` : the same on `ℂ^d ⊗ ℂ^β`, column by column.
- `FreeAxis.eq_zero_of_free_axis_core` : a state annihilated by `[T, P]` and an eigenvector of
  `κ P + R`, with `κ ≠ 0` and `R` commuting with `T` and `P`, vanishes.
- `FreeAxis.eq_zero_of_free_axis` : on the cube, `a, b, c` in the kernel with the brackets of
  `a, b` on axis `i` alone and `c` without transport on axis `i` leave `Φ = 0`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D AxisDefectEntangled PathGraph3DNRS GramStep

namespace FreeAxis

/-! ## 1. Transport and `[T_d, P_d]` have no common vector -/

variable {d : ℕ}

/-- **No common vector.** `T_d v = 0` and `[T_d, P_d] v = 0` give `v = 0`. -/
theorem eq_zero_of_Td_C (hd : 2 ≤ d) {v : Fin d → ℂ} (hT : (Td d).mulVec v = 0)
    (hC : (LieClosure.C d).mulVec v = 0) : v = 0 := by
  have hTP : (Td d).mulVec ((Pd d).mulVec v) = 0 := by
    have h : (LieClosure.C d).mulVec v =
        (Td d).mulVec ((Pd d).mulVec v) - (Pd d).mulVec ((Td d).mulVec v) := by
      simp [LieClosure.C, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    rw [hC, hT, Matrix.mulVec_zero, sub_zero] at h
    exact h.symm
  set i₀ : Fin d := ⟨0, by omega⟩
  set x₀ : ℂ := (posCoord d i₀ : ℂ)
  have hu := eq_zero_of_eigen hd (α := 0) (μ := 0) (v := (Pd d).mulVec v - x₀ • v)
    (fun i => by simp [Matrix.mulVec_sub, Matrix.mulVec_smul, hTP, hT])
    (by simp [Pd_mulVec, x₀, i₀])
  have hsupp : ∀ j : Fin d, j ≠ i₀ → v j = 0 := by
    intro j hj
    have h := congrFun hu j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have hne : (posCoord d j : ℂ) - x₀ ≠ 0 := by
      rw [sub_ne_zero]
      intro h'
      exact hj (PlatformBlindness.posCoord_injective hd
        (Complex.ofReal_injective (by simpa [x₀] using h')))
    rw [Pd_mulVec] at h
    exact (mul_eq_zero.mp (by linear_combination h)).resolve_left hne
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  have h1 := congrFun hT ⟨1, by omega⟩
  simp only [Td_mulVec, Ad_mulVec_apply, Pi.zero_apply] at h1
  have h2 : v ⟨0, by omega⟩ = 0 := by
    have h2' : (if h : 1 + 1 < d then v ⟨1 + 1, h⟩ else 0) = 0 := by
      split_ifs
      exacts [hsupp _ (by simp [i₀, Fin.ext_iff]), rfl]
    simp only [h2', zero_add, div_eq_zero_iff, hρ, or_false] at h1
    simpa using h1
  have hv0 : v i₀ = 0 := h2
  funext j
  by_cases hj : j = i₀
  · rw [hj, hv0]; rfl
  · exact hsupp j hj

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]

/-- The column of a lifted operator applied to `Φ`. -/
theorem col_lift (e : ι ≃ Fin d × β) (A : Matrix (Fin d) (Fin d) ℂ) (Φ : EuclideanSpace ℂ ι)
    (r : β) : col e (Matrix.toEuclideanLin (liftAlong e A) Φ) r = A.mulVec (col e Φ r) :=
  funext fun i => liftAlong_apply_col e A Φ i r

omit [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] in
@[simp] theorem col_zero (e : ι ≃ Fin d × β) (r : β) : col e (0 : EuclideanSpace ℂ ι) r = 0 :=
  funext fun _ => rfl

/-- Lifted transport along `e`. -/
abbrev LT (d : ℕ) (e : ι ≃ Fin d × β) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (liftAlong e (Td d))

/-- Lifted position along `e`. -/
abbrev LP (d : ℕ) (e : ι ≃ Fin d × β) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (liftAlong e (Pd d))

/-- The column of `[T, P] Φ` is `[T_d, P_d]` applied to the column. -/
theorem col_comm (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) (r : β) :
    col e (LT d e (LP d e Φ) - LP d e (LT d e Φ)) r = (LieClosure.C d).mulVec (col e Φ r) := by
  have hs : col e (LT d e (LP d e Φ) - LP d e (LT d e Φ)) r =
      col e (LT d e (LP d e Φ)) r - col e (LP d e (LT d e Φ)) r := by
    funext i; simp [AxisDefectEntangled.col]
  rw [hs, col_lift, col_lift, col_lift, col_lift]
  simp [LieClosure.C, Matrix.sub_mulVec, Matrix.mulVec_mulVec]

/-- **No common vector on `ℂ^d ⊗ ℂ^β`.** -/
theorem eq_zero_of_lift (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (hT : LT d e Φ = 0) (hC : LT d e (LP d e Φ) - LP d e (LT d e Φ) = 0) : Φ = 0 := by
  have hcol : ∀ r, col e Φ r = 0 := fun r => by
    refine eq_zero_of_Td_C hd ?_ ?_
    · rw [← col_lift, hT]; rfl
    · rw [← col_comm, hC]; rfl
  ext q
  simpa [AxisDefectEntangled.col] using congrFun (hcol (e q).2) (e q).1

/-! ## 2. The core: `[T, P] Φ = 0` and an eigenvector of `κ P + R` -/

/-- **The core.** If `[T, P] Φ = 0` and `Φ` is an eigenvector of `κ P + R` with `κ ≠ 0` and `R`
commuting with `T` and `P`, then `Φ = 0`: the bracket with `κ P + R` gives
`[P, [T, P]] Φ = −h² T Φ = 0`, and `T`, `[T, P]` have no common vector. -/
theorem eq_zero_of_free_axis_core (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    {R : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} {κ μ : ℂ} (hκ : κ ≠ 0)
    (hRT : ∀ ψ, R (LT d e ψ) = LT d e (R ψ)) (hRP : ∀ ψ, R (LP d e ψ) = LP d e (R ψ))
    (hL : κ • LP d e Φ + R Φ = μ • Φ)
    (hC : LT d e (LP d e Φ) - LP d e (LT d e Φ) = 0) : Φ = 0 := by
  set Cop := LT d e ∘ₗ LP d e - LP d e ∘ₗ LT d e with hCop
  have hCΦ : Cop Φ = 0 := by simpa [Cop] using hC
  have hCR : Cop (R Φ) = R (Cop Φ) := by
    simp only [Cop, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hRT, hRP]
  have hCP : Cop (LP d e Φ) = 0 := by
    have h := congrArg Cop hL
    rw [map_add, map_smul, map_smul, hCR, hCΦ, map_zero, smul_zero, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_left hκ
  have hh : ((((2 / ((d : ℝ) - 1)) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    have : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    exact_mod_cast pow_ne_zero 2 (div_ne_zero two_ne_zero this)
  have hcol : ∀ r, col e Φ r = 0 := fun r => by
    have hCc : (LieClosure.C d).mulVec (col e Φ r) = 0 := by
      have := congrArg (fun ψ => col e ψ r) hCΦ
      simpa [Cop, col_comm] using this
    have hCPc : (LieClosure.C d * Pd d).mulVec (col e Φ r) = 0 := by
      have := congrArg (fun ψ => col e ψ r) hCP
      simp only [Cop, LinearMap.sub_apply, LinearMap.comp_apply] at this
      rw [col_comm, col_lift] at this
      simpa [Matrix.mulVec_mulVec] using this
    refine eq_zero_of_Td_C hd ?_ hCc
    have hPC := congrArg (fun M => M.mulVec (col e Φ r)) (LieClosure.commutator_P_C (d := d))
    simp only [Matrix.sub_mulVec, hCPc, sub_zero, Matrix.smul_mulVec] at hPC
    rw [← Matrix.mulVec_mulVec, hCc, Matrix.mulVec_zero] at hPC
    exact (smul_eq_zero.mp hPC.symm).resolve_left (neg_ne_zero.mpr hh)
  ext q
  simpa [AxisDefectEntangled.col] using congrFun (hcol (e q).2) (e q).1

/-! ## 3. On the cube -/

section Cube

open DeterminantEqualityRelation SpectralExtremal

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- Pairs of different axes commute. -/
theorem pairs_comm {s t : Fin 2} {i j : Fin 3} (h : i ≠ j) (ψ : H3D dx dy dz) :
    pairs dx dy dz (t, j) (pairs dx dy dz (s, i) ψ) =
      pairs dx dy dz (s, i) (pairs dx dy dz (t, j) ψ) := by
  have := congrArg (fun L => L ψ) (commutator_pairs dx dy dz (a := s) (b := t) h)
  simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    sub_eq_zero] at this
  exact this.symm

/-- **The brackets of `N` on one axis.** If `a, b` are relations of `Φ` and their brackets
vanish on every axis but `i`, then `[T_i, P_i] Φ = 0`. -/
theorem comm_axis_eq_zero {i : Fin 3} {a b : Fin 2 × Fin 3 → ℂ}
    (ha : ∑ p, a p • fluct Φ p = 0) (hb : ∑ p, b p • fluct Φ p = 0)
    (hσ : ∀ j, j ≠ i → a (0, j) * b (1, j) - a (1, j) * b (0, j) = 0)
    (hσi : a (0, i) * b (1, i) - a (1, i) * b (0, i) ≠ 0) :
    opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ = 0 := by
  have h := commutator_sum Φ a b
  rw [comb_eigen Φ hb, comb_eigen Φ ha, map_smul, map_smul, comb_eigen Φ ha, comb_eigen Φ hb,
    smul_smul, smul_smul, mul_comm, sub_self, Finset.sum_eq_single i] at h
  · exact (smul_eq_zero.mp h.symm).resolve_left hσi
  · intro j _ hj
    rw [hσ j hj, zero_smul]
  · simp

/-- `L_c` without its position term on axis `i`. -/
def rest (dx dy dz : ℕ) (c : Fin 2 × Fin 3 → ℂ) (i : Fin 3) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  comb c - c (1, i) • pairs dx dy dz (1, i)

/-- `L_c` minus its position term on axis `i` commutes with transport and position of `i`, when
`c` has no transport on axis `i`. -/
theorem rest_comm {i : Fin 3} {c : Fin 2 × Fin 3 → ℂ} (hcT : c (0, i) = 0) (s : Fin 2)
    (ψ : H3D dx dy dz) :
    rest dx dy dz c i (pairs dx dy dz (s, i) ψ) =
      pairs dx dy dz (s, i) (rest dx dy dz c i ψ) := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hcT ⊢
  · simp only [rest, comb, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_sub, map_smul,
      hcT, zero_smul, zero_add,
      pairs_comm (i := 0) (j := 1) (by decide), pairs_comm (i := 0) (j := 2) (by decide)]
    abel
  · simp only [rest, comb, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_sub, map_smul,
      hcT, zero_smul, add_zero,
      pairs_comm (i := 1) (j := 0) (by decide), pairs_comm (i := 1) (j := 2) (by decide)]
    abel
  · simp only [rest, comb, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_sub, map_smul,
      hcT, zero_smul, add_zero,
      pairs_comm (i := 2) (j := 0) (by decide), pairs_comm (i := 2) (j := 1) (by decide)]
    abel

/-- **A free axis leaves no state.** Let `a, b, c` be relations of `Φ` (vectors of the kernel
of the Gram matrix). If the brackets of `a, b` vanish on every axis but `i`, and `c` carries
position on axis `i` but no transport there, then `Φ = 0`. -/
theorem eq_zero_of_free_axis (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {i : Fin 3}
    {a b c : Fin 2 × Fin 3 → ℂ} (ha : ∑ p, a p • fluct Φ p = 0) (hb : ∑ p, b p • fluct Φ p = 0)
    (hc : ∑ p, c p • fluct Φ p = 0)
    (hσ : ∀ j, j ≠ i → a (0, j) * b (1, j) - a (1, j) * b (0, j) = 0)
    (hσi : a (0, i) * b (1, i) - a (1, i) * b (0, i) ≠ 0) (hcT : c (0, i) = 0)
    (hcP : c (1, i) ≠ 0) : Φ = 0 := by
  have hC := comm_axis_eq_zero ha hb hσ hσi
  obtain ⟨μ, hL⟩ : ∃ μ : ℂ, c (1, i) • pairs dx dy dz (1, i) Φ + rest dx dy dz c i Φ = μ • Φ :=
    ⟨_, by rw [rest, LinearMap.sub_apply, LinearMap.smul_apply, add_sub_cancel, comb_eigen Φ hc]⟩
  simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply] at hC
  fin_cases i
  · exact eq_zero_of_free_axis_core hx (eX dx dy dz) hcP (rest_comm hcT 0) (rest_comm hcT 1) hL hC
  · exact eq_zero_of_free_axis_core hy (eY dx dy dz) hcP (rest_comm hcT 0) (rest_comm hcT 1) hL hC
  · exact eq_zero_of_free_axis_core hz (eZ dx dy dz) hcP (rest_comm hcT 0) (rest_comm hcT 1) hL hC

end Cube

end FreeAxis

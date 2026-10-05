/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49l_FreeAxis

/-!
# D49n — Brackets on two axes

Equality in det|NRS³ gives `Σ_k σ_k [T_k, P_k] Φ = 0` (`D49h`). Here the brackets reach two axes
`i`, `j`: `σ_i [T_i, P_i] Φ + σ_j [T_j, P_j] Φ = 0` with `σ_i ≠ 0`. If a relation `c` of `Φ`
carries position on axis `i` and nothing else on the axes `i`, `j`, its bracket with that
combination isolates axis `i`: `[P_i, [T_i, P_i]] Φ = −h² T_i Φ = 0` (`D49i`). Then `T_i Φ = 0`,
and any relation with position on axis `i` gives `[T_i, P_i] Φ = 0` as well, so `Φ = 0` (`D49l`).

## Main results

- `TwoAxes.T_eq_zero_of_PC` : `[P, [T, P]] Φ = 0` gives `T Φ = 0`.
- `TwoAxes.eq_zero_of_T_eq_zero` : `T Φ = 0` and an eigenvector of `κ P + α T + R`, `κ ≠ 0`,
  `R` commuting with `T`, give `Φ = 0`.
- `TwoAxes.eq_zero_of_two_axes` : on the cube, brackets on the axes `i`, `j` with `σ_i ≠ 0` and a
  relation with position on axis `i` and nothing else on `i`, `j` leave `Φ = 0`.
- `TwoAxes.eq_zero_of_comm_eq_zero` : `[T_i, P_i] Φ = 0` and a relation with position on axis `i`
  and no transport there leave `Φ = 0`.

## What remains

Write `W ⊆ ℂ³` for the span of the bracket coefficients `σ(a, b)`, `a, b ∈ N`; every `w ∈ W`
gives `Σ w_k [T_k, P_k] Φ = 0`. `W = 0` is excluded by `D49h`. `W ∋ e_i` is closed by
`eq_zero_of_comm_eq_zero`, since `σ_i ≠ 0` makes the projection of `N` on axis `i` all of `ℂ²`
and so provides the relation (this linear step is not yet written in Lean). A two-axis `w` is
closed here when `N` has a relation with position on axis `i` alone on the axes `i`, `j`. The other configurations need the second bracket
`[L_c, Σ w_k [T_k, P_k]] = Σ w_k (c_{T_k} [T_k, [T_k, P_k]] − c_{P_k} h_k² T_k)`, where the
diagonal `[T_k, [T_k, P_k]]` leaves the span of `T_k`, `P_k`, `[T_k, P_k]` from `d = 4` on
(`D49i`).
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D AxisDefectEntangled PathGraph3DNRS GramStep
open FreeAxis

namespace TwoAxes

variable {d : ℕ} {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]

/-- `[T, P] Φ` on the lifted axis. -/
abbrev Cop (d : ℕ) (e : ι ≃ Fin d × β) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  LT d e (LP d e ψ) - LP d e (LT d e ψ)

/-- **`[P, [T, P]] Φ = 0` gives `T Φ = 0`**, since `[P_d, [T_d, P_d]] = −h² T_d` (`D49i`). -/
theorem T_eq_zero_of_PC (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (h : LP d e (Cop d e Φ) - Cop d e (LP d e Φ) = 0) : LT d e Φ = 0 := by
  have hh : ((((2 / ((d : ℝ) - 1)) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    have : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    exact_mod_cast pow_ne_zero 2 (div_ne_zero two_ne_zero this)
  have hcol : ∀ r, (Td d).mulVec (col e Φ r) = 0 := fun r => by
    have hc := congrArg (fun ψ => col e ψ r) h
    have hs : col e (LP d e (Cop d e Φ) - Cop d e (LP d e Φ)) r =
        col e (LP d e (Cop d e Φ)) r - col e (Cop d e (LP d e Φ)) r := by
      funext i; simp [AxisDefectEntangled.col]
    simp only [col_zero] at hc
    rw [hs, col_lift, col_comm, col_comm, col_lift, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.sub_mulVec, LieClosure.commutator_P_C, Matrix.smul_mulVec] at hc
    exact (smul_eq_zero.mp hc).resolve_left (neg_ne_zero.mpr hh)
  ext q
  have := congrFun (hcol (e q).2) (e q).1
  rw [← col_lift] at this
  simpa [AxisDefectEntangled.col] using this

/-- **`T Φ = 0` leaves no state** once `Φ` is an eigenvector of `κ P + α T + R` with `κ ≠ 0` and
`R` commuting with `T`: then `T P Φ = 0`, so `[T, P] Φ = 0`, and `D49l` applies. -/
theorem eq_zero_of_T_eq_zero (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    {R : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} {κ α μ : ℂ} (hκ : κ ≠ 0)
    (hRT : ∀ ψ, R (LT d e ψ) = LT d e (R ψ)) (hT : LT d e Φ = 0)
    (hL : κ • LP d e Φ + α • LT d e Φ + R Φ = μ • Φ) : Φ = 0 := by
  have h := congrArg (LT d e) hL
  rw [map_add, map_add, map_smul, map_smul, map_smul, ← hRT, hT, map_zero, map_zero, smul_zero,
    smul_zero, add_zero, add_zero] at h
  have hTP : LT d e (LP d e Φ) = 0 := (smul_eq_zero.mp h).resolve_left hκ
  exact eq_zero_of_lift hd e hT (by rw [hTP, hT, map_zero, sub_zero])

/-! ## On the cube -/

section Cube

open DeterminantEqualityRelation SpectralExtremal

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- `L_c` without its position term on axis `i` commutes with an axis `j` on which `c` vanishes. -/
theorem rest_comm_other {i j : Fin 3} (hij : i ≠ j) {c : Fin 2 × Fin 3 → ℂ} (hc0 : c (0, j) = 0)
    (hc1 : c (1, j) = 0) (s : Fin 2) (ψ : H3D dx dy dz) :
    rest dx dy dz c i (pairs dx dy dz (s, j) ψ) = pairs dx dy dz (s, j) (rest dx dy dz c i ψ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hc0 hc1 hij ⊢ <;>
    first
    | exact absurd rfl hij
    | simp only [rest, comb, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_sub, map_smul,
        hc0, hc1, zero_smul, zero_add, add_zero,
        pairs_comm (i := 0) (j := 1) (by decide), pairs_comm (i := 0) (j := 2) (by decide),
        pairs_comm (i := 1) (j := 2) (by decide)]

/-- **Brackets on two axes leave no state.** Let `a, b, c` be relations of `Φ`. If the brackets
of `a, b` vanish outside the axes `i`, `j` and `σ_i(a, b) ≠ 0`, and `c` carries position on axis
`i` and nothing else on the axes `i`, `j`, then `Φ = 0`. -/
theorem eq_zero_of_two_axes (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {i j : Fin 3} (hij : i ≠ j)
    {a b c : Fin 2 × Fin 3 → ℂ} (ha : ∑ p, a p • fluct Φ p = 0) (hb : ∑ p, b p • fluct Φ p = 0)
    (hc : ∑ p, c p • fluct Φ p = 0)
    (hσ : ∀ k, k ≠ i → k ≠ j → a (0, k) * b (1, k) - a (1, k) * b (0, k) = 0)
    (hσi : a (0, i) * b (1, i) - a (1, i) * b (0, i) ≠ 0)
    (hc0i : c (0, i) = 0) (hc0j : c (0, j) = 0) (hc1j : c (1, j) = 0) (hc1i : c (1, i) ≠ 0) :
    Φ = 0 := by
  set σi := a (0, i) * b (1, i) - a (1, i) * b (0, i)
  set σj := a (0, j) * b (1, j) - a (1, j) * b (0, j)
  set Ci := opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i))
  set Cj := opCommutator (pairs dx dy dz (0, j)) (pairs dx dy dz (1, j))
  set Pi := pairs dx dy dz (1, i)
  obtain ⟨μ, hL⟩ : ∃ μ : ℂ, c (1, i) • Pi Φ + rest dx dy dz c i Φ = μ • Φ :=
    ⟨_, by rw [rest, LinearMap.sub_apply, LinearMap.smul_apply, add_sub_cancel, comb_eigen Φ hc]⟩
  set R := rest dx dy dz c i
  have hK : σi • Ci Φ + σj • Cj Φ = 0 := by
    have h := commutator_sum Φ a b
    rw [comb_eigen Φ hb, comb_eigen Φ ha, map_smul, map_smul, comb_eigen Φ ha, comb_eigen Φ hb,
      smul_smul, smul_smul, mul_comm, sub_self,
      Fintype.sum_eq_add i j hij (fun k hk => by rw [hσ k hk.1 hk.2, zero_smul])] at h
    exact h.symm
  have hRC (k : Fin 3) (hk : ∀ s (ψ : H3D dx dy dz),
      R (pairs dx dy dz (s, k) ψ) = pairs dx dy dz (s, k) (R ψ)) (ψ : H3D dx dy dz) :
      R (opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k)) ψ) =
        opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k)) (R ψ) := by
    simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hk]
  have hRi : ∀ ψ, R (Ci ψ) = Ci (R ψ) := hRC i (rest_comm hc0i)
  have hRj : ∀ ψ, R (Cj ψ) = Cj (R ψ) := hRC j (rest_comm_other hij hc0j hc1j)
  have hPCj (ψ : H3D dx dy dz) : Pi (Cj ψ) = Cj (Pi ψ) := by
    simp only [Pi, Cj, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      pairs_comm (i := j) (j := i) hij.symm]
  have hRΦ : R Φ = μ • Φ - c (1, i) • Pi Φ := by rw [← hL, add_sub_cancel_left]
  have h1 := congrArg (fun v => c (1, i) • Pi v + R v) hK
  simp only [map_add, map_smul, map_zero, smul_zero, add_zero, hRi, hRj, hPCj, hRΦ, map_sub]
    at h1
  have hkey : c (1, i) • σi • (Pi (Ci Φ) - Ci (Pi Φ)) = 0 := by
    linear_combination (norm := module) h1 - μ • hK
  have hPC : Pi (Ci Φ) - Ci (Pi Φ) = 0 :=
    (smul_eq_zero.mp ((smul_eq_zero.mp hkey).resolve_left hc1i)).resolve_left hσi
  have hL' : c (1, i) • Pi Φ + (0 : ℂ) • pairs dx dy dz (0, i) Φ + R Φ = μ • Φ := by
    rw [zero_smul, add_zero, hL]
  fin_cases i
  · have hT := T_eq_zero_of_PC hx (eX dx dy dz) hPC
    exact eq_zero_of_T_eq_zero hx (eX dx dy dz) hc1i (rest_comm hc0i 0) hT hL'
  · have hT := T_eq_zero_of_PC hy (eY dx dy dz) hPC
    exact eq_zero_of_T_eq_zero hy (eY dx dy dz) hc1i (rest_comm hc0i 0) hT hL'
  · have hT := T_eq_zero_of_PC hz (eZ dx dy dz) hPC
    exact eq_zero_of_T_eq_zero hz (eZ dx dy dz) hc1i (rest_comm hc0i 0) hT hL'

/-- **One tension annihilates `Φ`.** If `[T_i, P_i] Φ = 0` and a relation `c` of `Φ` carries
position on axis `i` without transport there (whatever it does on the other axes), `Φ = 0`. -/
theorem eq_zero_of_comm_eq_zero (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {i : Fin 3}
    {c : Fin 2 × Fin 3 → ℂ} (hc : ∑ p, c p • fluct Φ p = 0)
    (hC : opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ = 0)
    (hc0 : c (0, i) = 0) (hc1 : c (1, i) ≠ 0) : Φ = 0 := by
  obtain ⟨μ, hL⟩ : ∃ μ : ℂ, c (1, i) • pairs dx dy dz (1, i) Φ + rest dx dy dz c i Φ = μ • Φ :=
    ⟨_, by rw [rest, LinearMap.sub_apply, LinearMap.smul_apply, add_sub_cancel, comb_eigen Φ hc]⟩
  simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply] at hC
  fin_cases i
  · exact eq_zero_of_free_axis_core hx (eX dx dy dz) hc1 (rest_comm hc0 0) (rest_comm hc0 1) hL hC
  · exact eq_zero_of_free_axis_core hy (eY dx dy dz) hc1 (rest_comm hc0 0) (rest_comm hc0 1) hL hC
  · exact eq_zero_of_free_axis_core hz (eZ dx dy dz) hc1 (rest_comm hc0 0) (rest_comm hc0 1) hL hC

end Cube

end TwoAxes

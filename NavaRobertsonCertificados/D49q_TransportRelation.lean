/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49p_RelationsDimension

/-!
# D49q — A transport relation from two tensions

Suppose `w_i [T_i, P_i] Φ + w_j [T_j, P_j] Φ = 0` and `c` is a relation of `Φ` with no transport on
the axes `i`, `j`. Bracketing with `L_c` keeps only the position terms of `c` on `i`, `j`, and
`[P_k, [T_k, P_k]] = −h_k² T_k` (`D49i`) turns them into transport:

  `(w_i c(P_i) h_i² T_i + w_j c(P_j) h_j² T_j) Φ = 0`.

This is a relation of `Φ` made of transport alone, the first step of the last case of the open
step of `D49h`.

## Main results

- `TransportRelation.PC_eq` : `[P, [T, P]] ψ = −h² T ψ` on a lifted axis.
- `TransportRelation.pairs_PC` : the same on each axis of the cube.
- `TransportRelation.rest2_comm_left`, `rest2_comm_right` : `L_c` without its position terms on
  `i`, `j` commutes with both axes when `c` has no transport there.
- `TransportRelation.transport_relation` : the transport relation above.
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D AxisDefectEntangled PathGraph3DNRS GramStep
open FreeAxis TwoAxes

namespace TransportRelation

variable {d : ℕ} {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]

/-- `h_d² = (2/(d − 1))²`, as a complex number. -/
abbrev hsq (d : ℕ) : ℂ := (((2 / ((d : ℝ) - 1)) ^ 2 : ℝ) : ℂ)

/-- **`[P, [T, P]] = −h² T`** on a lifted axis (`D49i`, column by column). -/
theorem PC_eq (e : ι ≃ Fin d × β) (ψ : EuclideanSpace ℂ ι) :
    LP d e (Cop d e ψ) - Cop d e (LP d e ψ) = -(hsq d) • LT d e ψ := by
  ext q
  have key (r : β) : col e (LP d e (Cop d e ψ) - Cop d e (LP d e ψ)) r =
      col e (-(hsq d) • LT d e ψ) r := by
    have hs : col e (LP d e (Cop d e ψ) - Cop d e (LP d e ψ)) r =
        col e (LP d e (Cop d e ψ)) r - col e (Cop d e (LP d e ψ)) r := by
      funext i; simp [AxisDefectEntangled.col]
    have hsm : col e (-(hsq d) • LT d e ψ) r = -(hsq d) • col e (LT d e ψ) r := by
      funext i; simp [AxisDefectEntangled.col]
    rw [hs, hsm, col_lift, col_comm, col_comm, col_lift, col_lift, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.sub_mulVec, LieClosure.commutator_P_C, Matrix.smul_mulVec]
  have := congrFun (key (e q).2) (e q).1
  simpa [AxisDefectEntangled.col] using this

section Cube

open DeterminantEqualityRelation SpectralExtremal

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- The number of positions on axis `k`. -/
abbrev dim3 (dx dy dz : ℕ) : Fin 3 → ℕ := ![dx, dy, dz]

/-- **`[P_k, [T_k, P_k]] = −h_k² T_k`** on each axis of the cube. -/
theorem pairs_PC (k : Fin 3) (ψ : H3D dx dy dz) :
    pairs dx dy dz (1, k) (opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k)) ψ) -
      opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k)) (pairs dx dy dz (1, k) ψ) =
      -(hsq (dim3 dx dy dz k)) • pairs dx dy dz (0, k) ψ := by
  simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply]
  fin_cases k
  · exact PC_eq (eX dx dy dz) ψ
  · exact PC_eq (eY dx dy dz) ψ
  · exact PC_eq (eZ dx dy dz) ψ

/-- `L_c` without its position terms on the axes `i`, `j`. -/
def rest2 (dx dy dz : ℕ) (c : Fin 2 × Fin 3 → ℂ) (i j : Fin 3) :
    H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  rest dx dy dz c i - c (1, j) • pairs dx dy dz (1, j)

/-- `L_c` without its position terms on `i`, `j` commutes with axis `i`. -/
theorem rest2_comm_left {i j : Fin 3} (hij : i ≠ j) {c : Fin 2 × Fin 3 → ℂ} (hci : c (0, i) = 0)
    (hcj : c (0, j) = 0) (s : Fin 2) (ψ : H3D dx dy dz) :
    rest2 dx dy dz c i j (pairs dx dy dz (s, i) ψ) =
      pairs dx dy dz (s, i) (rest2 dx dy dz c i j ψ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hci hcj hij ⊢ <;>
    first
    | exact absurd rfl hij
    | (simp only [rest2, rest, comb, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
        map_add, map_sub, map_smul, hci, hcj, zero_smul, zero_add, add_zero,
        pairs_comm (i := 0) (j := 1) (by decide),
        pairs_comm (i := 0) (j := 2) (by decide)]; abel1)
    | (simp only [rest2, rest, comb, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
        map_add, map_sub, map_smul, hci, hcj, zero_smul, zero_add, add_zero,
        pairs_comm (i := 1) (j := 0) (by decide),
        pairs_comm (i := 1) (j := 2) (by decide)]; abel1)

/-- `L_c` without its position terms on `i`, `j` commutes with axis `j`. -/
theorem rest2_comm_right {i j : Fin 3} (hij : i ≠ j) {c : Fin 2 × Fin 3 → ℂ} (hci : c (0, i) = 0)
    (hcj : c (0, j) = 0) (s : Fin 2) (ψ : H3D dx dy dz) :
    rest2 dx dy dz c i j (pairs dx dy dz (s, j) ψ) =
      pairs dx dy dz (s, j) (rest2 dx dy dz c i j ψ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hci hcj hij ⊢ <;>
    first
    | exact absurd rfl hij
    | (simp only [rest2, rest, comb, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
        map_add, map_sub, map_smul, hci, hcj, zero_smul, zero_add, add_zero,
        pairs_comm (i := 0) (j := 1) (by decide),
        pairs_comm (i := 0) (j := 2) (by decide)]; abel1)
    | (simp only [rest2, rest, comb, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
        map_add, map_sub, map_smul, hci, hcj, zero_smul, zero_add, add_zero,
        pairs_comm (i := 1) (j := 0) (by decide),
        pairs_comm (i := 1) (j := 2) (by decide)]; abel1)


/-- **A transport relation from two tensions.** If `w_i [T_i, P_i] Φ + w_j [T_j, P_j] Φ = 0` and
`c` is a relation of `Φ` with no transport on the axes `i`, `j`, then
`(w_i c(P_i) h_i² T_i + w_j c(P_j) h_j² T_j) Φ = 0`. -/
theorem transport_relation {i j : Fin 3} (hij : i ≠ j) {wi wj : ℂ}
    (hK : wi • opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ +
      wj • opCommutator (pairs dx dy dz (0, j)) (pairs dx dy dz (1, j)) Φ = 0)
    {c : Fin 2 × Fin 3 → ℂ} (hc : ∑ p, c p • fluct Φ p = 0) (hci : c (0, i) = 0)
    (hcj : c (0, j) = 0) :
    (wi * c (1, i) * hsq (dim3 dx dy dz i)) • pairs dx dy dz (0, i) Φ +
      (wj * c (1, j) * hsq (dim3 dx dy dz j)) • pairs dx dy dz (0, j) Φ = 0 := by
  set Ci := opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i))
  set Cj := opCommutator (pairs dx dy dz (0, j)) (pairs dx dy dz (1, j))
  set Pi := pairs dx dy dz (1, i)
  set Pj := pairs dx dy dz (1, j)
  obtain ⟨μ, hL⟩ : ∃ μ : ℂ,
      c (1, i) • Pi Φ + c (1, j) • Pj Φ + rest2 dx dy dz c i j Φ = μ • Φ :=
    ⟨_, by
      rw [rest2, rest, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, comb_eigen Φ hc]
      abel⟩
  set R := rest2 dx dy dz c i j
  have hRC (k : Fin 3) (hk : ∀ s (ψ : H3D dx dy dz),
      R (pairs dx dy dz (s, k) ψ) = pairs dx dy dz (s, k) (R ψ)) (ψ : H3D dx dy dz) :
      R (opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k)) ψ) =
        opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k)) (R ψ) := by
    simp only [opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hk]
  have hRi : ∀ ψ, R (Ci ψ) = Ci (R ψ) := hRC i (rest2_comm_left hij hci hcj)
  have hRj : ∀ ψ, R (Cj ψ) = Cj (R ψ) := hRC j (rest2_comm_right hij hci hcj)
  have hPiCj (ψ : H3D dx dy dz) : Pi (Cj ψ) = Cj (Pi ψ) := by
    simp only [Pi, Cj, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      pairs_comm (i := j) (j := i) hij.symm]
  have hPjCi (ψ : H3D dx dy dz) : Pj (Ci ψ) = Ci (Pj ψ) := by
    simp only [Pj, Ci, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      pairs_comm (i := i) (j := j) hij]
  have hRΦ : R Φ = μ • Φ - c (1, i) • Pi Φ - c (1, j) • Pj Φ := by
    rw [← hL]; abel
  have h1 := congrArg (fun v => c (1, i) • Pi v + c (1, j) • Pj v + R v) hK
  simp only [map_add, map_smul, map_zero, smul_zero, add_zero, hRi, hRj, hPiCj, hPjCi, hRΦ,
    map_sub] at h1
  have hPCi := pairs_PC (dx := dx) (dy := dy) (dz := dz) i Φ
  have hPCj := pairs_PC (dx := dx) (dy := dy) (dz := dz) j Φ
  linear_combination (norm := module) -h1 + μ • hK + (c (1, i) * wi) • hPCi +
    (c (1, j) * wj) • hPCj

end Cube

end TransportRelation

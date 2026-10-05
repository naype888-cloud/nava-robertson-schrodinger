/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49n_TwoAxes

/-!
# D49o — The span of the brackets

A *relation* of `Φ` is a coefficient vector `a` with `Σ_p a_p (A_p − ⟨A_p⟩) Φ = 0`, so that `Φ`
is an eigenvector of `L_a = Σ_p a_p A_p` (`D49h`). Two relations give `[L_a, L_b] Φ = 0`, and
since different axes commute, `[L_a, L_b] = Σ_k σ_k(a, b) [T_k, P_k]` with
`σ_k(a, b) = a(T_k) b(P_k) − a(P_k) b(T_k)`. The triple `σ(a, b) = (σ_x, σ_y, σ_z)` is the recipe
of how much tension of each axis enters that bracket.

`W` is the span of all these recipes. Every `w ∈ W` gives `Σ_k w_k [T_k, P_k] Φ = 0`
(`annihilates`). If `W` contains the recipe of one axis alone, `e_i`, then `Φ = 0`
(`eq_zero_of_single_mem`): some pair has `σ_i(a, b) ≠ 0`, and the relation
`c = a(T_i) b − b(T_i) a` has no transport on axis `i` and position `σ_i(a, b) ≠ 0` there, so
`D49n` applies. The linear step is explicit.

## Main results

- `BracketSpan.rel` : the relations of `Φ`, a subspace of `ℂ^(2 × 3)`.
- `BracketSpan.sigma` : the recipe `σ(a, b)`.
- `BracketSpan.W` : the span of the recipes of pairs of relations.
- `BracketSpan.annihilates` : `Σ_k w_k [T_k, P_k] Φ = 0` for every `w ∈ W`.
- `BracketSpan.exists_rel_P` : `σ_i(a, b) ≠ 0` gives a relation with position and no transport
  on axis `i`.
- `BracketSpan.eq_zero_of_single_mem` : `e_i ∈ W` leaves `Φ = 0`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D PathGraph3DNRS
open DeterminantEqualityRelation SpectralExtremal FreeAxis TwoAxes

namespace BracketSpan

variable {dx dy dz : ℕ} (Φ : H3D dx dy dz)

/-- The relations of `Φ`: coefficient vectors `a` with `Σ_p a_p (A_p − ⟨A_p⟩) Φ = 0`. -/
def rel : Submodule ℂ (Fin 2 × Fin 3 → ℂ) :=
  LinearMap.ker (Fintype.linearCombination ℂ (fluct Φ))

theorem mem_rel {a : Fin 2 × Fin 3 → ℂ} : a ∈ rel Φ ↔ ∑ p, a p • fluct Φ p = 0 := by
  simp [rel, Fintype.linearCombination_apply]

/-- The recipe of the bracket of `L_a` and `L_b`: how much tension of each axis it carries. -/
def sigma (a b : Fin 2 × Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun k => a (0, k) * b (1, k) - a (1, k) * b (0, k)

/-- `W`: the span of the recipes of all pairs of relations. -/
def W : Submodule ℂ (Fin 3 → ℂ) :=
  Submodule.span ℂ {s | ∃ a ∈ rel Φ, ∃ b ∈ rel Φ, s = sigma a b}

/-- The combination `Σ_k w_k [T_k, P_k]` of the three tensions. -/
def tensionComb (w : Fin 3 → ℂ) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  ∑ k, w k • opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k))

/-- **Every recipe in `W` annihilates `Φ`**: `Σ_k w_k [T_k, P_k] Φ = 0`. -/
theorem annihilates {w : Fin 3 → ℂ} (hw : w ∈ W Φ) : tensionComb w Φ = 0 := by
  induction hw using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    rw [mem_rel] at ha hb
    have h := commutator_sum Φ a b
    rw [comb_eigen Φ hb, comb_eigen Φ ha, map_smul, map_smul, comb_eigen Φ ha, comb_eigen Φ hb,
      smul_smul, smul_smul, mul_comm, sub_self] at h
    simpa [tensionComb, sigma, LinearMap.sum_apply] using h.symm
  | zero => simp [tensionComb]
  | add x y _ _ hx hy =>
    simp only [tensionComb, Pi.add_apply, add_smul, Finset.sum_add_distrib, LinearMap.add_apply]
      at hx hy ⊢
    rw [hx, hy, add_zero]
  | smul r x _ hx =>
    simp only [tensionComb, Pi.smul_apply, smul_eq_mul, LinearMap.sum_apply,
      LinearMap.smul_apply] at hx ⊢
    simp only [mul_smul, ← Finset.smul_sum, hx, smul_zero]

/-- **The linear step.** If `σ_i(a, b) ≠ 0`, the relation `c = a(T_i) b − b(T_i) a` has no
transport on axis `i` and position `σ_i(a, b)` there. -/
theorem exists_rel_P {i : Fin 3} {a b : Fin 2 × Fin 3 → ℂ} (ha : a ∈ rel Φ) (hb : b ∈ rel Φ)
    (hσ : sigma a b i ≠ 0) : ∃ c ∈ rel Φ, c (0, i) = 0 ∧ c (1, i) ≠ 0 := by
  refine ⟨a (0, i) • b - b (0, i) • a, Submodule.sub_mem _ (Submodule.smul_mem _ _ hb)
    (Submodule.smul_mem _ _ ha), by simp [mul_comm], ?_⟩
  simpa [sigma, mul_comm] using hσ

/-- If every generator has `σ_i = 0`, so does every recipe in `W`. -/
theorem apply_eq_zero_of_forall {i : Fin 3}
    (h : ∀ a ∈ rel Φ, ∀ b ∈ rel Φ, sigma a b i = 0) {w : Fin 3 → ℂ} (hw : w ∈ W Φ) : w i = 0 := by
  induction hw using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    exact h a ha b hb
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

variable {Φ}

/-- **The recipe of one axis alone leaves no state.** If `e_i ∈ W`, then `[T_i, P_i] Φ = 0`, a
pair of relations has `σ_i ≠ 0`, the linear step gives a relation with position and no
transport on axis `i`, and `Φ = 0` (`D49n`). -/
theorem eq_zero_of_single_mem (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {i : Fin 3}
    (hW : Pi.single i 1 ∈ W Φ) : Φ = 0 := by
  have hC : opCommutator (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Φ = 0 := by
    have h := annihilates Φ hW
    simpa [tensionComb, LinearMap.sum_apply, Pi.single_apply] using h
  obtain ⟨a, ha, b, hb, hσ⟩ : ∃ a ∈ rel Φ, ∃ b ∈ rel Φ, sigma a b i ≠ 0 := by
    by_contra hc
    push Not at hc
    have := apply_eq_zero_of_forall Φ hc hW
    simp at this
  obtain ⟨c, hc, hc0, hc1⟩ := exists_rel_P Φ ha hb hσ
  exact eq_zero_of_comm_eq_zero hx hy hz ((mem_rel Φ).mp hc) hC hc0 hc1

end BracketSpan

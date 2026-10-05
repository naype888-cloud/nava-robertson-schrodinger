/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49r_EdgeOperator

/-!
# D49s — The edge of the cube and the transport recurrence

Let `Φ` satisfy a transport relation `(α T_x + β T_y) Φ = 0` with `α ≠ 0` (`D49q`). Read along `x`,
it is a recurrence: the slice `x = n + 1` is fixed by the slices `x = n` and `x = n − 1`. So if the
edge slice `x = 0` vanishes, `Φ = 0` (`eq_zero_of_edge`).

If moreover `w_x [T_x, P_x] Φ + w_y [T_y, P_y] Φ = 0`, the bracket with `α T_x + β T_y` gives
`(α w_x [T_x, [T_x, P_x]] + β w_y [T_y, [T_y, P_y]]) Φ = 0` (`edge_relation`). Both brackets live on
the ends (`D49r`), so on the edge slice `x = 0` this is a diagonal condition, and it leaves at most
one position `y*` free. Then `Φ(x, y, z) = g(z) f(x, y)`: the state splits off `z`
(`eq_zero_or_split`).

## Main results

- `EdgeSlices.pairsX_apply`, `pairsY_apply` : transport and position act on one coordinate.
- `EdgeSlices.edgeX_apply` : `[T_x, [T_x, P_x]] ψ = D_{ii} ψ` pointwise.
- `EdgeSlices.edge_relation` : the bracket of a transport relation with two tensions.
- `EdgeSlices.eq_zero_of_edge` : the recurrence with a vanishing edge slice leaves `0`.
- `EdgeSlices.eq_zero_or_split` : `Φ = 0`, or `Φ = w ⊗ χ` with `w` on `z` and `‖χ‖ = 1`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D AxisDefectEntangled PathGraph3DNRS GramStep
open FreeAxis TwoAxes LieClosure EdgeOperator DeterminantEqualityRelation SpectralExtremal

namespace EdgeSlices

/-! ## 1. One axis at a time -/

section Axis

variable {d : ℕ} {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]

/-- The column of `[T, [T, P]] ψ` is `[T_d, [T_d, P_d]]` applied to the column. -/
theorem col_edge (e : ι ≃ Fin d × β) (ψ : EuclideanSpace ℂ ι) (r : β) :
    col e (LT d e (Cop d e ψ) - Cop d e (LT d e ψ)) r = (D d).mulVec (col e ψ r) := by
  have hs : col e (LT d e (Cop d e ψ) - Cop d e (LT d e ψ)) r =
      col e (LT d e (Cop d e ψ)) r - col e (Cop d e (LT d e ψ)) r := by
    funext i; simp [AxisDefectEntangled.col]
  rw [hs, col_lift, col_comm, col_comm, col_lift, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.sub_mulVec]
  rfl

/-- A diagonal matrix acts entrywise. -/
theorem D_mulVec (v : Fin d → ℂ) (i : Fin d) : (D d).mulVec v i = D d i i * v i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hj; rw [D_offdiag (Ne.symm hj), zero_mul]
  · simp

end Axis

/-! ## 2. On the cube -/

variable {dx dy dz : ℕ}

theorem pairsX_apply (s : Fin 2) (ψ : H3D dx dy dz) (i : Fin dx) (j : Fin dy) (k : Fin dz) :
    pairs dx dy dz (s, 0) ψ (i, j, k) = (![Td dx, Pd dx] s).mulVec (fun i' => ψ (i', j, k)) i :=
  liftAlong_apply_col (eX dx dy dz) _ ψ i (j, k)

theorem pairsY_apply (s : Fin 2) (ψ : H3D dx dy dz) (i : Fin dx) (j : Fin dy) (k : Fin dz) :
    pairs dx dy dz (s, 1) ψ (i, j, k) = (![Td dy, Pd dy] s).mulVec (fun j' => ψ (i, j', k)) j :=
  liftAlong_apply_col (eY dx dy dz) _ ψ j (i, k)

/-- `[T_k, P_k]` on the cube. -/
abbrev Cm (dx dy dz : ℕ) (k : Fin 3) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  opCommutator (pairs dx dy dz (0, k)) (pairs dx dy dz (1, k))

/-- `[T_k, [T_k, P_k]]` on the cube. -/
abbrev Dm (dx dy dz : ℕ) (k : Fin 3) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  opCommutator (pairs dx dy dz (0, k)) (Cm dx dy dz k)

theorem edgeX_apply (ψ : H3D dx dy dz) (i : Fin dx) (j : Fin dy) (k : Fin dz) :
    Dm dx dy dz 0 ψ (i, j, k) = D dx i i * ψ (i, j, k) := by
  have h := congrFun (col_edge (eX dx dy dz) ψ (j, k)) i
  rw [D_mulVec] at h
  exact h

theorem edgeY_apply (ψ : H3D dx dy dz) (i : Fin dx) (j : Fin dy) (k : Fin dz) :
    Dm dx dy dz 1 ψ (i, j, k) = D dy j j * ψ (i, j, k) := by
  have h := congrFun (col_edge (eY dx dy dz) ψ (i, k)) j
  rw [D_mulVec] at h
  exact h

/-- **The bracket of a transport relation with two tensions.** -/
theorem edge_relation {Φ : H3D dx dy dz} {α β wx wy : ℂ}
    (ht : α • pairs dx dy dz (0, 0) Φ + β • pairs dx dy dz (0, 1) Φ = 0)
    (hK : wx • Cm dx dy dz 0 Φ + wy • Cm dx dy dz 1 Φ = 0) :
    (α * wx) • Dm dx dy dz 0 Φ + (β * wy) • Dm dx dy dz 1 Φ = 0 := by
  have hXY (s t : Fin 2) (ψ : H3D dx dy dz) :
      pairs dx dy dz (t, 1) (pairs dx dy dz (s, 0) ψ) =
        pairs dx dy dz (s, 0) (pairs dx dy dz (t, 1) ψ) := pairs_comm (by decide) ψ
  have hTxCy (ψ : H3D dx dy dz) :
      pairs dx dy dz (0, 0) (Cm dx dy dz 1 ψ) = Cm dx dy dz 1 (pairs dx dy dz (0, 0) ψ) := by
    simp only [Cm, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hXY]
  have hTyCx (ψ : H3D dx dy dz) :
      pairs dx dy dz (0, 1) (Cm dx dy dz 0 ψ) = Cm dx dy dz 0 (pairs dx dy dz (0, 1) ψ) := by
    simp only [Cm, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hXY]
  have h1 := congrArg (fun v => α • pairs dx dy dz (0, 0) v + β • pairs dx dy dz (0, 1) v) hK
  have h2 := congrArg (fun v => wx • Cm dx dy dz 0 v + wy • Cm dx dy dz 1 v) ht
  simp only [map_add, map_smul, map_zero, smul_zero, add_zero, hTxCy, hTyCx] at h1 h2
  simp only [Dm, Cm, opCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    at h1 h2 ⊢
  linear_combination (norm := module) h1 - h2

/-- The transport relation, pointwise. -/
theorem transport_apply {Φ : H3D dx dy dz} {α β : ℂ}
    (ht : α • pairs dx dy dz (0, 0) Φ + β • pairs dx dy dz (0, 1) Φ = 0)
    (i : Fin dx) (j : Fin dy) (k : Fin dz) :
    α * (Td dx).mulVec (fun i' => Φ (i', j, k)) i +
      β * (Td dy).mulVec (fun j' => Φ (i, j', k)) j = 0 := by
  have h := congrArg (fun v : H3D dx dy dz => v (i, j, k)) ht
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h
  rw [pairsX_apply, pairsY_apply] at h
  exact h

/-- **The recurrence along `x`.** A solution with vanishing edge slice `x = 0` vanishes. -/
theorem eq_zero_of_edge (hx : 2 ≤ dx) {α β : ℂ} (hα : α ≠ 0)
    {F : Fin dx → Fin dy → ℂ}
    (hF : ∀ i j, α * (Td dx).mulVec (fun i' => F i' j) i +
      β * (Td dy).mulVec (fun j' => F i j') j = 0)
    (h0 : ∀ j, F ⟨0, by omega⟩ j = 0) : ∀ i j, F i j = 0 := by
  have hρ : (rho dx : ℂ) ≠ 0 := by exact_mod_cast (rho_pos dx hx).ne'
  have key : ∀ n (hn : n < dx), ∀ j, F ⟨n, hn⟩ j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn j
      rcases n with _ | m
      · exact h0 j
      · have hm : m < dx := by omega
        have hrow : (fun j' => F ⟨m, hm⟩ j') = 0 := funext fun j' => ih m (by omega) hm j'
        have hprev : (if h : 0 < m then F ⟨m - 1, by omega⟩ j else 0) = 0 := by
          split_ifs with h
          exacts [ih (m - 1) (by omega) _ j, rfl]
        have h := hF ⟨m, hm⟩ j
        rw [show (fun j' => F ⟨m, hm⟩ j') = 0 from hrow, Matrix.mulVec_zero] at h
        simp only [Td_mulVec, Ad_mulVec_apply, hn, ↓reduceDIte, hprev, add_zero,
          Pi.zero_apply, mul_zero] at h
        have := (mul_eq_zero.mp h).resolve_left hα
        simpa [hρ] using this
  intro i j
  exact key i.val i.isLt j

/-- `2h/ρ_d²`, the size of `[T_d, [T_d, P_d]]` at the ends. -/
abbrev κ (d : ℕ) : ℝ := 2 * (2 / ((d : ℝ) - 1)) / rho d ^ 2

theorem κ_ne_zero {d : ℕ} (hd : 2 ≤ d) : (κ d : ℂ) ≠ 0 := by
  have h1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h2 : rho d ≠ 0 := (rho_pos d hd).ne'
  have : κ d ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (div_ne_zero two_ne_zero h1)) (pow_ne_zero 2 h2)
  exact_mod_cast this

/-- Where `[T_d, [T_d, P_d]]` does not vanish: only at the two ends, with opposite values. -/
theorem D_cases {d : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    (j.val = 0 ∧ D d j j = -(κ d : ℂ)) ∨ (j.val = d - 1 ∧ D d j j = (κ d : ℂ)) ∨ D d j j = 0 := by
  by_cases h0 : j.val = 0
  · left
    refine ⟨h0, ?_⟩
    have : j = ⟨0, by omega⟩ := Fin.ext h0
    rw [this, D_zero_zero hd]
  · by_cases h1 : j.val = d - 1
    · right; left
      refine ⟨h1, ?_⟩
      have : j = ⟨d - 1, by omega⟩ := Fin.ext h1
      rw [this, D_last hd]
    · right; right
      exact D_interior (by omega) (by omega)

/-- **At most one free position on the edge.** If `a ≠ 0` and `b ≠ 0`, the coefficient
`a + b D_{jj}` vanishes for at most one `j`. -/
theorem coef_unique {d : ℕ} (hd : 2 ≤ d) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) {j₁ j₂ : Fin d}
    (h₁ : a + b * D d j₁ j₁ = 0) (h₂ : a + b * D d j₂ j₂ = 0) : j₁ = j₂ := by
  have hκ := κ_ne_zero hd
  have hD : D d j₁ j₁ = D d j₂ j₂ := by
    have := h₁.trans h₂.symm
    exact mul_left_cancel₀ hb (add_left_cancel this)
  have hnz : D d j₁ j₁ ≠ 0 := fun h => ha (by simpa [h] using h₁)
  rcases D_cases hd j₁ with ⟨a1, v1⟩ | ⟨a1, v1⟩ | v1 <;>
    rcases D_cases hd j₂ with ⟨a2, v2⟩ | ⟨a2, v2⟩ | v2
  all_goals first
    | exact Fin.ext (by omega)
    | exact absurd v1 hnz
    | (exfalso; rw [hD] at hnz; exact hnz v2)
    | (exfalso; rw [v1, v2] at hD
       have : (2 : ℂ) * κ d = 0 := by linear_combination -hD
       exact hκ ((mul_eq_zero.mp this).resolve_left two_ne_zero))
    | (exfalso; rw [v1, v2] at hD
       have : (2 : ℂ) * κ d = 0 := by linear_combination hD
       exact hκ ((mul_eq_zero.mp this).resolve_left two_ne_zero))

/-- **`Φ = 0`, or `Φ` splits off `z`.** Under a transport relation `(α T_x + β T_y) Φ = 0` and
`w_x [T_x, P_x] Φ + w_y [T_y, P_y] Φ = 0`, with `α, β, w_x, w_y ≠ 0`. -/
theorem eq_zero_or_split (hx : 2 ≤ dx) (hy : 2 ≤ dy) {Φ : H3D dx dy dz} {α β wx wy : ℂ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hwx : wx ≠ 0) (hwy : wy ≠ 0)
    (ht : α • pairs dx dy dz (0, 0) Φ + β • pairs dx dy dz (0, 1) Φ = 0)
    (hK : wx • Cm dx dy dz 0 Φ + wy • Cm dx dy dz 1 Φ = 0) :
    Φ = 0 ∨ ∃ (w : Hd dz) (χ : EuclideanSpace ℂ (Fin dx × Fin dy)), ‖χ‖ = 1 ∧
      Φ = prodAlong (eZ dx dy dz) w χ := by
  set i₀ : Fin dx := ⟨0, by omega⟩
  have hE := edge_relation ht hK
  set a : ℂ := α * wx * D dx i₀ i₀
  set b : ℂ := β * wy
  have ha : a ≠ 0 := by
    have hD : D dx i₀ i₀ ≠ 0 := by
      rw [D_zero_zero hx]
      exact neg_ne_zero.mpr (κ_ne_zero hx)
    exact mul_ne_zero (mul_ne_zero hα hwx) hD
  have hb : b ≠ 0 := mul_ne_zero hβ hwy
  -- the edge condition
  have hedge (j : Fin dy) (k : Fin dz) : (a + b * D dy j j) * Φ (i₀, j, k) = 0 := by
    have h := congrArg (fun v : H3D dx dy dz => v (i₀, j, k)) hE
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply, edgeX_apply,
      edgeY_apply] at h
    linear_combination h
  -- one free position `j*`
  obtain ⟨jstar, hjs⟩ : ∃ jstar : Fin dy, ∀ j, j ≠ jstar → ∀ k, Φ (i₀, j, k) = 0 := by
    by_cases hex : ∃ j, a + b * D dy j j = 0
    · obtain ⟨j₀, hj₀⟩ := hex
      refine ⟨j₀, fun j hj k => ?_⟩
      have hc : a + b * D dy j j ≠ 0 := fun h => hj (coef_unique hy ha hb h hj₀)
      exact (mul_eq_zero.mp (hedge j k)).resolve_left hc
    · push Not at hex
      exact ⟨⟨0, by omega⟩, fun j _ k => (mul_eq_zero.mp (hedge j k)).resolve_left (hex j)⟩
  have hrec := transport_apply ht
  set G : Fin dz → ℂ := fun k => Φ (i₀, jstar, k)
  by_cases hG : ∀ k, G k = 0
  · left
    ext ⟨i, j, k⟩
    have := eq_zero_of_edge hx hα (F := fun i j => Φ (i, j, k)) (fun i j => hrec i j k)
      (fun j => by
        by_cases hj : j = jstar
        · subst hj; exact hG k
        · exact hjs j hj k) i j
    simpa using this
  · right
    push Not at hG
    obtain ⟨k₀, hk₀⟩ := hG
    have hprop (i : Fin dx) (j : Fin dy) (k : Fin dz) :
        Φ (i, j, k) = G k / G k₀ * Φ (i, j, k₀) := by
      have := eq_zero_of_edge hx hα (β := β)
        (F := fun i j => G k₀ * Φ (i, j, k) - G k * Φ (i, j, k₀))
        (fun i j => by
          have h1 := hrec i j k
          have h2 := hrec i j k₀
          have e1 : (fun i' => G k₀ * Φ (i', j, k) - G k * Φ (i', j, k₀)) =
              G k₀ • (fun i' => Φ (i', j, k)) - G k • (fun i' => Φ (i', j, k₀)) := by
            funext i'; simp
          have e2 : (fun j' => G k₀ * Φ (i, j', k) - G k * Φ (i, j', k₀)) =
              G k₀ • (fun j' => Φ (i, j', k)) - G k • (fun j' => Φ (i, j', k₀)) := by
            funext j'; simp
          simp only [e1, e2, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]
          linear_combination G k₀ * h1 - G k * h2)
        (fun j => by
          by_cases hj : j = jstar
          · subst hj
            show G k₀ * Φ (i₀, j, k) - G k * Φ (i₀, j, k₀) = 0
            simp only [G]; ring
          · show G k₀ * Φ (i₀, j, k) - G k * Φ (i₀, j, k₀) = 0
            rw [hjs j hj k, hjs j hj k₀]; ring) i j
      field_simp
      linear_combination this
    set χ₀ : EuclideanSpace ℂ (Fin dx × Fin dy) := WithLp.toLp 2 fun q => Φ (q.1, q.2, k₀)
    have hχ₀ : χ₀ ≠ 0 := by
      intro h
      have := congrArg (fun v : EuclideanSpace ℂ (Fin dx × Fin dy) => v (i₀, jstar)) h
      exact hk₀ (by simpa [χ₀, G] using this)
    have hn : (‖χ₀‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hχ₀)
    refine ⟨WithLp.toLp 2 fun k => (‖χ₀‖ : ℂ) * (G k / G k₀), (‖χ₀‖ : ℂ)⁻¹ • χ₀, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hχ₀)]
    · ext ⟨i, j, k⟩
      rw [prodAlong_apply, hprop i j k]
      simp only [eZ, Equiv.coe_fn_mk, PiLp.smul_apply, smul_eq_mul]
      field_simp
      rfl

end EdgeSlices

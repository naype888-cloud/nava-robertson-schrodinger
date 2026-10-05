/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49s_EdgeSlices
public import NavaRobertsonCertificados.D49j_RobertsonDeterminantSplitAxis

/-!
# D49t — det|NRS³ is strict in the band, for every state

**Theorem.** On every box, for every unit state `Φ` whose speeds on `x`, `y`, `z` lie in the bands
`Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)`, Robertson 1934 on the six observables `(T_x, T_y, T_z, P_x, P_y, P_z)`
is strict: `|det Ω| < det Σ`. No product structure, no canonical axes: the states that mix the
three directions are included.

Suppose equality. The relations of `Φ` form a space of dimension `3` or `4` (`D49p`); four leave no
state. With three, look at the span `W` of the bracket recipes (`D49o`):

* If `W` has a nonzero recipe with no `z` part, `(w_x, w_y, 0)`: a recipe of one axis alone leaves
  no state (`D49o`); otherwise a relation `c` without transport on `x`, `y` gives the transport
  relation `(α T_x + β T_y) Φ = 0` (`D49q`). If one of `α`, `β` vanishes, one transport
  annihilates `Φ` and no state is left (`D49n`); if both vanish, `c` lives on `z` alone, against the
  band (`D49p`). Otherwise the edge argument gives `Φ = 0` or `Φ` split off `z` (`D49s`), and a
  split state is strict (`D49j`).
* Otherwise every nonzero recipe has a `z` part. A relation `a` without `z` part has
  `σ(a, b) = 0` for every `b`; its `x` and `y` parts are both nonzero (`D49p`), which forces every
  recipe to live on `z`, so `e_z ∈ W` and no state is left (`D49o`), or `W = 0`, where one axis
  carries a relation alone (`D49h`).

## Main results

- `RobertsonDeterminantBandStrict.robertson_det_band_strict` : `|det Ω| < det Σ` in the band, for
  every state.
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D AxisDefectEntangled PathGraph3DNRS
open GroupVelocity VelocityBand RobertsonDeterminant DeterminantEqualityRelation SpectralExtremal
open FreeAxis TwoAxes BracketSpan RelationsDimension TransportRelation EdgeSlices

namespace RobertsonDeterminantBandStrict

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- With three relations, two coordinates can be made to vanish on a nonzero relation. -/
theorem exists_rel_two_zero (h3 : 3 ≤ Module.finrank ℂ (rel Φ)) (p q : Fin 2 × Fin 3) :
    ∃ a ∈ rel Φ, a ≠ 0 ∧ a p = 0 ∧ a q = 0 := by
  let f : (Fin 2 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun a => ![a p, a q]
      map_add' := fun a b => by funext s; fin_cases s <;> rfl
      map_smul' := fun c a => by funext s; fin_cases s <;> rfl }
  have hk := LinearMap.finrank_range_add_finrank_ker (f.domRestrict (rel Φ))
  have hr : Module.finrank ℂ (LinearMap.range (f.domRestrict (rel Φ))) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (f.domRestrict (rel Φ)))
    simpa using this
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker (f.domRestrict (rel Φ))) := by omega
  have hbot : LinearMap.ker (f.domRestrict (rel Φ)) ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hpos; omega
  obtain ⟨⟨a, ha⟩, hker, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have h0 := LinearMap.mem_ker.mp hker
  have hp := congrFun h0 0
  have hq := congrFun h0 1
  refine ⟨a, ha, fun h => hne (Subtype.ext h), ?_, ?_⟩
  · simpa [f] using hp
  · simpa [f] using hq

theorem hsq_ne_zero {d : ℕ} (hd : 2 ≤ d) : hsq d ≠ 0 := by
  have h1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (div_ne_zero two_ne_zero h1))

/-- **One transport annihilating `Φ` leaves no state**, given a relation with position and no
transport on that axis. -/
theorem eq_zero_of_T_zero_cube (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {i : Fin 3}
    {c : Fin 2 × Fin 3 → ℂ} (hc : c ∈ rel Φ) (hc0 : c (0, i) = 0) (hc1 : c (1, i) ≠ 0)
    (hT : pairs dx dy dz (0, i) Φ = 0) : Φ = 0 := by
  obtain ⟨μ, hL⟩ : ∃ μ : ℂ, c (1, i) • pairs dx dy dz (1, i) Φ + (0 : ℂ) • pairs dx dy dz (0, i) Φ +
      rest dx dy dz c i Φ = μ • Φ :=
    ⟨_, by rw [zero_smul, add_zero, rest, LinearMap.sub_apply, LinearMap.smul_apply,
      add_sub_cancel, comb_eigen Φ ((mem_rel Φ).mp hc)]⟩
  fin_cases i
  · exact eq_zero_of_T_eq_zero hx (eX dx dy dz) hc1 (rest_comm hc0 0) hT hL
  · exact eq_zero_of_T_eq_zero hy (eY dx dy dz) hc1 (rest_comm hc0 0) hT hL
  · exact eq_zero_of_T_eq_zero hz (eZ dx dy dz) hc1 (rest_comm hc0 0) hT hL

/-- **det|NRS³ is strict in the band, for every state.** -/
theorem robertson_det_band_strict (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hΦ : ‖Φ‖ = 1)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    |(imMatrix (pairs dx dy dz) Φ).det| < (covMatrix (pairs dx dy dz) Φ).det := by
  have hle : |(imMatrix (pairs dx dy dz) Φ).det| ≤ (covMatrix (pairs dx dy dz) Φ).det :=
    robertson_det (pairs dx dy dz) Φ
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hΦ0 : Φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΦ; exact zero_ne_one hΦ
  have h3 := three_le_finrank_rel hx hy hz hbx hby hbz heq.symm
  have h4 := finrank_rel_le_four hx hy hz hΦ hbx hby hbz
  have hsingle {a : Fin 2 × Fin 3 → ℂ} (ha : a ∈ rel Φ) {k : Fin 3}
      (hsupp : ∀ s j, j ≠ k → a (s, j) = 0) : a = 0 :=
    eq_zero_of_single_axis hx hy hz hΦ hbx hby hbz ha hsupp
  have hrec3 : Module.finrank ℂ (rel Φ) = 3 := by
    rcases (show Module.finrank ℂ (rel Φ) = 3 ∨ Module.finrank ℂ (rel Φ) = 4 by omega) with h | h
    · exact h
    · exact absurd (eq_zero_of_finrank_four hx hy hz hΦ hbx hby hbz h) hΦ0
  by_cases hA : ∃ w ∈ W Φ, w ≠ 0 ∧ w 2 = 0
  · obtain ⟨w, hw, hw0, hw2⟩ := hA
    by_cases hwx : w 0 = 0
    · have hwy : w 1 ≠ 0 := fun h => hw0 (by funext k; fin_cases k <;> simp [hwx, h, hw2])
      have he : Pi.single (1 : Fin 3) (1 : ℂ) = (w 1)⁻¹ • w := by
        funext k; fin_cases k <;> simp [hwx, hw2, hwy]
      exact hΦ0 (eq_zero_of_single_mem hx hy hz (i := 1) (he ▸ Submodule.smul_mem _ _ hw))
    by_cases hwy : w 1 = 0
    · have he : Pi.single (0 : Fin 3) (1 : ℂ) = (w 0)⁻¹ • w := by
        funext k; fin_cases k <;> simp [hwx, hwy, hw2]
      exact hΦ0 (eq_zero_of_single_mem hx hy hz (i := 0) (he ▸ Submodule.smul_mem _ _ hw))
    have hK : w 0 • Cm dx dy dz 0 Φ + w 1 • Cm dx dy dz 1 Φ = 0 := by
      have h := annihilates Φ hw
      simpa [tensionComb, Fin.sum_univ_three, hw2, LinearMap.sum_apply] using h
    obtain ⟨c, hc, hc0, hcx, hcy⟩ := exists_rel_two_zero h3 (0, 0) (0, 1)
    have ht := transport_relation (i := 0) (j := 1) (by decide) hK ((mem_rel Φ).mp hc) hcx hcy
    have hqx := hsq_ne_zero hx
    have hqy := hsq_ne_zero hy
    by_cases hα : w 0 * c (1, 0) * hsq (dim3 dx dy dz 0) = 0
    · have hc10 : c (1, 0) = 0 := by
        rcases mul_eq_zero.mp hα with h | h
        · exact (mul_eq_zero.mp h).resolve_left hwx
        · exact absurd h hqx
      rw [hα, zero_smul, zero_add] at ht
      by_cases hβ : w 1 * c (1, 1) * hsq (dim3 dx dy dz 1) = 0
      · have hc11 : c (1, 1) = 0 := by
          rcases mul_eq_zero.mp hβ with h | h
          · exact (mul_eq_zero.mp h).resolve_left hwy
          · exact absurd h hqy
        refine hc0 (hsingle hc (k := 2) fun s j hj => ?_)
        fin_cases s <;> fin_cases j <;>
          first | exact hcx | exact hcy | exact hc10 | exact hc11 | exact absurd rfl hj
      · have hc11 : c (1, 1) ≠ 0 := fun h => hβ (by rw [h]; ring)
        have hTy : pairs dx dy dz (0, 1) Φ = 0 := (smul_eq_zero.mp ht).resolve_left hβ
        exact hΦ0 (eq_zero_of_T_zero_cube hx hy hz hc hcy hc11 hTy)
    · have hc10 : c (1, 0) ≠ 0 := fun h => hα (by rw [h]; ring)
      by_cases hβ : w 1 * c (1, 1) * hsq (dim3 dx dy dz 1) = 0
      · rw [hβ, zero_smul, add_zero] at ht
        have hTx : pairs dx dy dz (0, 0) Φ = 0 := (smul_eq_zero.mp ht).resolve_left hα
        exact hΦ0 (eq_zero_of_T_zero_cube hx hy hz hc hcx hc10 hTx)
      · rcases eq_zero_or_split hx hy hα hβ hwx hwy ht hK with h0 | ⟨w', χ, hχ, hsplit⟩
        · exact hΦ0 h0
        · have hw' : ‖w'‖ = 1 := by
            have h := norm_sq_prodAlong (eZ dx dy dz) w' χ hχ
            rw [← hsplit, hΦ, one_pow] at h
            exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h.symm)
          subst hsplit
          have := SplitAxis.robertson_det_strict_of_split hx hy hz hw' hχ hbx
            hby hbz
          linarith
  · push Not at hA
    obtain ⟨a, ha, ha0, haz0, haz1⟩ := exists_rel_two_zero h3 (0, 2) (1, 2)
    have hσa : ∀ b ∈ rel Φ, sigma a b = 0 := by
      intro b hb
      by_contra hne
      exact hA _ (Submodule.subset_span ⟨a, ha, b, hb, rfl⟩) hne (by simp [sigma, haz0, haz1])
    have hpart (k : Fin 3) (hk : k ≠ 2) : a (0, k) ≠ 0 ∨ a (1, k) ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨h0, h1⟩ := h
      fin_cases k
      · exact ha0 (hsingle ha (k := 1) fun s j hj => by
          fin_cases s <;> fin_cases j <;>
            first | exact h0 | exact h1 | exact haz0 | exact haz1 | exact absurd rfl hj)
      · exact ha0 (hsingle ha (k := 0) fun s j hj => by
          fin_cases s <;> fin_cases j <;>
            first | exact h0 | exact h1 | exact haz0 | exact haz1 | exact absurd rfl hj)
      · exact absurd rfl hk
    have hvan (k : Fin 3) (hk : k ≠ 2) : ∀ b ∈ rel Φ, ∀ b' ∈ rel Φ, sigma b b' k = 0 := by
      intro b hb b' hb'
      have e1 := congrFun (hσa b hb) k
      have e2 := congrFun (hσa b' hb') k
      simp only [sigma, Pi.zero_apply] at e1 e2 ⊢
      have m0 : (b (0, k) * b' (1, k) - b (1, k) * b' (0, k)) * a (0, k) = 0 := by
        linear_combination b (0, k) * e2 - b' (0, k) * e1
      have m1 : (b (0, k) * b' (1, k) - b (1, k) * b' (0, k)) * a (1, k) = 0 := by
        linear_combination b (1, k) * e2 - b' (1, k) * e1
      rcases hpart k hk with h | h
      · exact (mul_eq_zero.mp m0).resolve_right h
      · exact (mul_eq_zero.mp m1).resolve_right h
    by_cases hW0 : ∀ b ∈ rel Φ, ∀ b' ∈ rel Φ, sigma b b' 2 = 0
    · obtain ⟨a', ha', ha'0, hsupp⟩ := exists_single_axis (rel Φ) h3 fun b hb b' hb' k => by
        fin_cases k
        · exact hvan 0 (by decide) b hb b' hb'
        · exact hvan 1 (by decide) b hb b' hb'
        · exact hW0 b hb b' hb'
      exact ha'0 (hsingle ha' (k := 2) hsupp)
    · push Not at hW0
      obtain ⟨b, hb, b', hb', hne⟩ := hW0
      have h0 := hvan 0 (by decide) b hb b' hb'
      have h1 := hvan 1 (by decide) b hb b' hb'
      have he : Pi.single (2 : Fin 3) (1 : ℂ) = (sigma b b' 2)⁻¹ • sigma b b' := by
        funext k; fin_cases k <;> simp [h0, h1, hne]
      exact hΦ0 (eq_zero_of_single_mem hx hy hz (i := 2)
        (he ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, b', hb', rfl⟩)))

end RobertsonDeterminantBandStrict

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49o_BracketSpan

/-!
# D49p — How many relations

In the band no relation of `Φ` lives on one axis alone: it would make the defect of that axis
vanish, against `D49e` (`eq_zero_of_single_axis`). So forgetting one axis loses nothing: the
relations embed into the coefficients of the other two axes, and there are at most four
independent ones (`finrank_rel_le_four`). At equality in det|NRS³ there are at least three
(`three_le_finrank_rel`, from `D49h`). Four relations leave no state
(`eq_zero_of_finrank_four`): forgetting `z` is then onto, which provides relations with `x`, `y`
coefficients `T_x`, `P_x`, `T_y`, `P_y` alone, and `D49n`, `D49o` close the case.

## Main results

- `RelationsDimension.eq_zero_of_single_axis` : in the band, a relation on one axis is `0`.
- `RelationsDimension.finrank_rel_le_four` : in the band, `dim rel ≤ 4`.
- `RelationsDimension.three_le_finrank_rel` : at equality in the band, `3 ≤ dim rel`.
- `RelationsDimension.eq_zero_of_finrank_four` : four relations in the band leave `Φ = 0`.

So at equality in the band exactly three relations remain to be studied.
-/

@[expose] public noncomputable section

open Matrix TransportPosition RobertsonDeterminant3D PathGraph3DNRS GroupVelocity VelocityBand
open DeterminantEqualityRelation AxisDefectEntangled BracketSpan RobertsonDeterminant

namespace RelationsDimension

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- **No relation on one axis in the band.** A relation supported on axis `k` alone is `0`. -/
theorem eq_zero_of_single_axis (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hΦ : ‖Φ‖ = 1)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz)
    {a : Fin 2 × Fin 3 → ℂ} (ha : a ∈ rel Φ) {k : Fin 3}
    (hsupp : ∀ s j, j ≠ k → a (s, j) = 0) : a = 0 := by
  rw [mem_rel] at ha
  have hsum : a (0, k) • fluct Φ (0, k) + a (1, k) • fluct Φ (1, k) = 0 := by
    rw [← ha, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_eq_single k,
      Finset.sum_eq_single k]
    all_goals first
      | (intro j _ hj; rw [hsupp _ j hj, zero_smul])
      | simp
  by_contra hne
  have hαβ : a (0, k) ≠ 0 ∨ a (1, k) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    ext ⟨s, j⟩
    by_cases hj : j = k
    · subst hj
      fin_cases s
      exacts [h.1, h.2]
    · exact hsupp s j hj
  have hg := gramDefectC_eq_zero_of_rel hsum hαβ
  fin_cases k
  · exact (ne_of_gt (gramDefect_pos_of_band hx (eX dx dy dz) hΦ hbx)) hg
  · exact (ne_of_gt (gramDefect_pos_of_band hy (eY dx dy dz) hΦ hby)) hg
  · exact (ne_of_gt (gramDefect_pos_of_band hz (eZ dx dy dz) hΦ hbz)) hg

/-- The coefficients on the axes `x`, `y`, forgetting `z`. -/
def projXY : (Fin 2 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun a p := a (p.1, Fin.castSucc p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forgetting `z` loses no relation in the band. -/
theorem projXY_injective (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hΦ : ‖Φ‖ = 1)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    Function.Injective (projXY.domRestrict (rel Φ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, ha⟩ h0
  have := eq_zero_of_single_axis hx hy hz hΦ hbx hby hbz ha (k := 2) fun s j hj => by
    have hj' : j.val < 2 := by
      have := j.isLt
      have : j.val ≠ 2 := fun h => hj (Fin.ext h)
      omega
    have h1 := congrFun h0 (s, (⟨j.val, hj'⟩ : Fin 2))
    simpa [projXY, LinearMap.domRestrict_apply] using h1
  exact Subtype.ext this

/-- **At most four relations in the band.** -/
theorem finrank_rel_le_four (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hΦ : ‖Φ‖ = 1)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    Module.finrank ℂ (rel Φ) ≤ 4 := by
  have := LinearMap.finrank_le_finrank_of_injective
    (projXY_injective hx hy hz hΦ hbx hby hbz)
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- **At least three relations at equality.** -/
theorem three_le_finrank_rel (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz)
    (heq : (covMatrix (pairs dx dy dz) Φ).det = |(imMatrix (pairs dx dy dz) Φ).det|) :
    3 ≤ Module.finrank ℂ (rel Φ) := by
  refine (three_le_finrank_ker hx hy hz hbx hby hbz heq).trans (Submodule.finrank_mono ?_)
  intro a ha
  rw [mem_rel]
  exact sum_eq_zero_of_mulVec Φ (by rw [← Matrix.mulVecLin_apply]; exact ha)

open SpectralExtremal TwoAxes in
/-- **Four relations leave no state.** With four independent relations in the band, forgetting
`z` is onto: there are relations with `x`, `y` coefficients `T_x`, `P_x`, `T_y`, `P_y` alone. Their
recipes are `(1, 0, s)` and `(0, 1, s')`. If `s' = 0`, `e_y ∈ W` (`D49o`); otherwise
`s' (1, 0, s) − s (0, 1, s') = (s', −s, 0) ∈ W` and the relation with `P_x` alone closes it
(`D49n`). -/
theorem eq_zero_of_finrank_four (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hΦ : ‖Φ‖ = 1)
    (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy) (hbz : |velocityZ Φ| ∈ Ϙ dz)
    (h4 : Module.finrank ℂ (rel Φ) = 4) : Φ = 0 := by
  have hinj := projXY_injective hx hy hz hΦ hbx hby hbz
  have hsurj : Function.Surjective (projXY.domRestrict (rel Φ)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [h4, Module.finrank_fintype_fun_eq_card])).mp hinj
  have hpre (q : Fin 2 × Fin 2) : ∃ a ∈ rel Φ, ∀ s t, a (s, Fin.castSucc t) =
      if (s, t) = q then 1 else 0 := by
    obtain ⟨⟨a, ha⟩, h⟩ := hsurj (Pi.single q 1)
    refine ⟨a, ha, fun s t => ?_⟩
    have := congrFun h (s, t)
    simp only [LinearMap.domRestrict_apply, projXY, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, Pi.single_apply]
  obtain ⟨a, ha, hav⟩ := hpre (0, 0)
  obtain ⟨b, hb, hbv⟩ := hpre (1, 0)
  obtain ⟨a', ha', hav'⟩ := hpre (0, 1)
  obtain ⟨b', hb', hbv'⟩ := hpre (1, 1)
  have v00 : a (0, 0) = 1 := by simpa using hav 0 0
  have v01 : a (0, 1) = 0 := by simpa using hav 0 1
  have v10 : a (1, 0) = 0 := by simpa using hav 1 0
  have v11 : a (1, 1) = 0 := by simpa using hav 1 1
  have w00 : b (0, 0) = 0 := by simpa using hbv 0 0
  have w01 : b (0, 1) = 0 := by simpa using hbv 0 1
  have w10 : b (1, 0) = 1 := by simpa using hbv 1 0
  have w11 : b (1, 1) = 0 := by simpa using hbv 1 1
  have x00 : a' (0, 0) = 0 := by simpa using hav' 0 0
  have x01 : a' (0, 1) = 1 := by simpa using hav' 0 1
  have x10 : a' (1, 0) = 0 := by simpa using hav' 1 0
  have x11 : a' (1, 1) = 0 := by simpa using hav' 1 1
  have y00 : b' (0, 0) = 0 := by simpa using hbv' 0 0
  have y01 : b' (0, 1) = 0 := by simpa using hbv' 0 1
  have y10 : b' (1, 0) = 0 := by simpa using hbv' 1 0
  have y11 : b' (1, 1) = 1 := by simpa using hbv' 1 1
  have hσ1 : sigma a b = ![1, 0, sigma a b 2] := by
    funext k; fin_cases k <;> simp [sigma, v00, v10, v01, v11, w00, w10, w01, w11]
  have hσ2 : sigma a' b' = ![0, 1, sigma a' b' 2] := by
    funext k; fin_cases k <;> simp [sigma, x00, x10, x01, x11, y00, y10, y01, y11]
  have hm1 : sigma a b ∈ W Φ := Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
  have hm2 : sigma a' b' ∈ W Φ := Submodule.subset_span ⟨a', ha', b', hb', rfl⟩
  set s := sigma a b 2
  set s' := sigma a' b' 2
  by_cases hs' : s' = 0
  · refine eq_zero_of_single_mem hx hy hz (i := 1) ?_
    convert hm2 using 1
    rw [hσ2, hs']
    funext k; fin_cases k <;> simp
  · have hw : s' • sigma a b - s • sigma a' b' ∈ W Φ :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ hm1) (Submodule.smul_mem _ _ hm2)
    have hK := annihilates Φ hw
    rw [hσ1, hσ2] at hK
    simp only [tensionComb, Fin.sum_univ_three, LinearMap.add_apply, LinearMap.smul_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one, mul_zero, sub_zero,
      zero_sub, mul_comm s' s, sub_self, zero_smul, add_zero] at hK
    refine eq_zero_of_two_comm hx hy hz (i := 0) (j := 1) (by decide) (σi := s') (σj := -s) hs'
      ?_ ((mem_rel Φ).mp hb) w00 w01 w11 (by rw [w10]; exact one_ne_zero)
    rw [← hK]

end RelationsDimension

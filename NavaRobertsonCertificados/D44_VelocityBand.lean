/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D43_NRSOctahedron

/-!
# D44 — The velocity band `Ϙ(d)` of forced defect

On `H_d` the cone speed `|v| = 1` is reached by the maximal current state (`D38`). The
minimum-uncertainty states
reach speeds up to the threshold `v*(d)`, the largest of their speeds: some minimum-uncertainty
state moves exactly at `v*(d)` (compactness of the unit sphere). The band
`Ϙ(d) = (v*(d), 1]` is the range of speeds at which every state has a Robertson–Schrödinger
surplus; its width is `ϙ(d) = 1 − v*(d)` (koppa).

* At `d = 2, 3`, the maximal current state saturates at the cone: `ϙ = 0` and the band is empty.
* For `d ≥ 4` the band is never empty: `ϙ(d) ≥ ((d − 1)/2) · bandWidth d > 0` (`D23d`).
* At `d = 4` the width is exact: `ϙ(4) = (7 − 3√5)/4 ≈ 0.0729` (`D23f`, `D23g`, `D43`).

The exact value of `ϙ(d)` for `d ≥ 5` is not computed here; `D45d` proves
`ϙ(d) ≤ 0.0728 < ϙ(4)`. Numerically (`docs/simulation/figures_velocity_band.py`), for `d ≥ 5` the
fastest minimum-uncertainty state is an eigenvector of `T_d − iμ P_d` with `μ` real, and
`ϙ(d) ≈ (2 ln d + b)/d²`, with `b` depending on the parity of `d`; neither is proved here.

## Main results

- `VelocityBand.threshold_isGreatest`, `VelocityBand.exists_saturated_threshold` : `v*(d)` is
  attained by a minimum-uncertainty state.
- `VelocityBand.surplus_pos_of_mem_band` : on `Ϙ(d)` the defect is forced.
- `VelocityBand.koppa_eq_zero` : `ϙ(2) = ϙ(3) = 0`.
- `VelocityBand.koppa_ge`, `VelocityBand.koppa_pos` : for `d ≥ 4`, an explicit positive width.
- `VelocityBand.band_four`, `VelocityBand.koppa_four` : `Ϙ(4) = (v*(4), 1]`,
  `ϙ(4) = (7 − 3√5)/4`.
- `VelocityBand.velocityBand_certificate` : everything at once.
-/

@[expose] public noncomputable section

open Real TransportPosition NRSInequality NearMaxTension EigenvectorSaturation GramStep
open GroupVelocity Direction BandWidth MinUncertaintyFour

namespace VelocityBand

variable {d : ℕ}

/-! ## 1. The threshold, the band and its width -/

/-- The speeds `|v|` of the minimum-uncertainty unit states of `H_d`. -/
def satSpeeds (d : ℕ) : Set ℝ :=
  {s | ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ surplus d ψ = 0 ∧ |velocity d ψ| = s}

/-- The threshold `v*(d)`: the supremum of the minimum-uncertainty speeds. -/
def threshold (d : ℕ) : ℝ := sSup (satSpeeds d)

/-- The band `Ϙ(d) = (v*(d), 1]` of speeds with forced defect. -/
def band (d : ℕ) : Set ℝ := Set.Ioc (threshold d) 1

/-- The width `ϙ(d) = 1 − v*(d)` of the band. -/
def koppa (d : ℕ) : ℝ := 1 - threshold d

@[inherit_doc] scoped notation "Ϙ" => band
@[inherit_doc] scoped notation "ϙ" => koppa

/-- Basis vectors saturate, so the set of speeds is never empty. -/
theorem satSpeeds_nonempty (hd : 1 ≤ d) : (satSpeeds d).Nonempty :=
  ⟨_, EuclideanSpace.single ⟨0, hd⟩ 1, by simp, (basis_state_saturates d _).2, rfl⟩

theorem satSpeeds_bddAbove (hd : 2 ≤ d) : BddAbove (satSpeeds d) :=
  ⟨1, fun _ ⟨ψ, hψ, _, hs⟩ => hs ▸ abs_velocity_le hd ψ hψ⟩

theorem threshold_le_one (hd : 2 ≤ d) : threshold d ≤ 1 :=
  csSup_le (satSpeeds_nonempty (by omega)) fun _ ⟨ψ, hψ, _, hs⟩ => hs ▸ abs_velocity_le hd ψ hψ

theorem koppa_nonneg (hd : 2 ≤ d) : 0 ≤ ϙ d :=
  sub_nonneg.2 (threshold_le_one hd)

/-! ## 2. The threshold is attained -/

theorem satSpeeds_eq_image (d : ℕ) :
    satSpeeds d =
      (fun ψ => |velocity d ψ|) '' (Metric.sphere 0 1 ∩ {ψ | surplus d ψ = 0}) := by
  ext s
  simp [satSpeeds, and_assoc]

theorem isCompact_satSpeeds (d : ℕ) : IsCompact (satSpeeds d) := by
  rw [satSpeeds_eq_image]
  exact ((isCompact_sphere 0 1).inter_right
    (isClosed_eq (continuous_surplus d) continuous_const)).image
      (continuous_const.mul (continuous_tension d)).abs

theorem threshold_isGreatest (hd : 1 ≤ d) : IsGreatest (satSpeeds d) (threshold d) :=
  (isCompact_satSpeeds d).isGreatest_sSup (satSpeeds_nonempty hd)

/-- **The threshold is attained**: a minimum-uncertainty state moves exactly at `v*(d)`. -/
theorem exists_saturated_threshold (hd : 1 ≤ d) :
    ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ surplus d ψ = 0 ∧ |velocity d ψ| = threshold d :=
  (threshold_isGreatest hd).1

/-! ## 3. The defect is forced on the band -/

/-- Faster than `v*(d)`, Robertson–Schrödinger is strict. -/
theorem surplus_pos_of_threshold_lt (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (hv : threshold d < |velocity d ψ|) : 0 < surplus d ψ :=
  lt_of_le_of_ne (gramDefectAt_nonneg _ _ _) fun h =>
    (le_csSup (satSpeeds_bddAbove hd) ⟨ψ, hψ, h.symm, rfl⟩).not_gt hv

/-- **The band.** Every unit state whose speed lies in `Ϙ(d)` carries a surplus. -/
theorem surplus_pos_of_mem_band (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (hv : |velocity d ψ| ∈ Ϙ d) : 0 < surplus d ψ :=
  surplus_pos_of_threshold_lt hd ψ hψ hv.1

/-! ## 4. No band at `d = 2, 3` -/

theorem surplus_maxCurrentState_eq_zero_iff (hd : 2 ≤ d) :
    surplus d (maxCurrentState d) = 0 ↔ d = 2 ∨ d = 3 := by
  rw [surplus_maxCurrentState hd, gramStep_gram_eq_zero_iff hd]

theorem threshold_eq_one (hd : d = 2 ∨ d = 3) : threshold d = 1 := by
  have h2 : 2 ≤ d := by omega
  refine le_antisymm (threshold_le_one h2) (le_csSup (satSpeeds_bddAbove h2) ?_)
  exact ⟨maxCurrentState d, norm_maxCurrentState h2, (surplus_maxCurrentState_eq_zero_iff h2).2 hd,
    by rw [velocity_maxCurrentState h2, abs_one]⟩

theorem koppa_eq_zero (hd : d = 2 ∨ d = 3) : ϙ d = 0 := by
  rw [koppa, threshold_eq_one hd, sub_self]

theorem band_eq_empty (hd : d = 2 ∨ d = 3) : Ϙ d = ∅ := by
  rw [band, threshold_eq_one hd, Set.Ioc_self]

/-! ## 5. A band of explicit width for `d ≥ 4` -/

/-- A minimum-uncertainty state has tension at most `2/(d−1) − bandWidth d` (`D23d`). -/
theorem tension_le_bandWidth (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) (h0 : surplus d ψ = 0) :
    tension d ψ ≤ 2 / ((d : ℝ) - 1) - bandWidth d := by
  by_contra! hK
  have := strict_inequality_bandWidth hd ψ hψ hK
  rw [surplus_eq] at h0
  linarith

/-- A minimum-uncertainty state moves at most at `1 − ((d−1)/2) · bandWidth d`, either way. -/
theorem abs_velocity_le_bandWidth (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (h0 : surplus d ψ = 0) : |velocity d ψ| ≤ 1 - ((d : ℝ) - 1) / 2 * bandWidth d := by
  have h1 := tension_le_bandWidth hd ψ hψ h0
  have h2 := tension_le_bandWidth hd (reflect d ψ) (by rw [LinearIsometryEquiv.norm_map, hψ])
    (by rw [surplus, NRSOctahedron.gramDefect_reflect]; exact h0)
  rw [tension_reflect] at h2
  have hc : 0 < ((d : ℝ) - 1) / 2 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he : ((d : ℝ) - 1) / 2 * (2 / ((d : ℝ) - 1) - bandWidth d) =
      1 - ((d : ℝ) - 1) / 2 * bandWidth d := by
    field_simp [(by linarith : (d : ℝ) - 1 ≠ 0)]
  rw [velocity, abs_le, ← he]
  constructor <;> nlinarith

theorem threshold_le (hd : 4 ≤ d) : threshold d ≤ 1 - ((d : ℝ) - 1) / 2 * bandWidth d :=
  csSup_le (satSpeeds_nonempty (by omega)) fun _ ⟨ψ, hψ, h0, hs⟩ =>
    hs ▸ abs_velocity_le_bandWidth hd ψ hψ h0

/-- The width of the band is at least `((d−1)/2) · bandWidth d`. -/
theorem koppa_ge (hd : 4 ≤ d) : ((d : ℝ) - 1) / 2 * bandWidth d ≤ ϙ d := by
  have := threshold_le hd
  rw [koppa]
  linarith

theorem bandWidth_speed_pos (hd : 4 ≤ d) : 0 < ((d : ℝ) - 1) / 2 * bandWidth d := by
  have : (4 : ℝ) ≤ d := by exact_mod_cast hd
  exact mul_pos (by linarith) (bandWidth_pos hd)

/-- **For `d ≥ 4` the band is never empty.** -/
theorem koppa_pos (hd : 4 ≤ d) : 0 < ϙ d :=
  (bandWidth_speed_pos hd).trans_le (koppa_ge hd)

/-! ## 6. The exact band at `d = 4` -/

theorem vStar_pos : 0 < NRSOctahedron.vStar := by
  linarith [NRSOctahedron.vStar_bounds.1]

/-- At `d = 4` the threshold is `v*(4) = 3(√5 − 1)/4` (`D23f`, `D23g`). -/
theorem threshold_four : threshold 4 = NRSOctahedron.vStar :=
  IsGreatest.csSup_eq
    ⟨⟨psiSat, norm_psiSat, saturated_psiSat,
        by rw [NRSOctahedron.velocity_psiSat, abs_of_pos vStar_pos]⟩,
      fun _ ⟨ψ, hψ, h0, hs⟩ => hs ▸ NRSOctahedron.abs_velocity_le_of_saturated ψ hψ h0⟩

theorem band_four : Ϙ 4 = Set.Ioc NRSOctahedron.vStar 1 := by
  rw [band, threshold_four]

/-- **The exact width at `d = 4`:** `ϙ(4) = (7 − 3√5)/4`. -/
theorem koppa_four : ϙ 4 = (7 - 3 * √5) / 4 := by
  rw [koppa, threshold_four, NRSOctahedron.vStar]
  ring

/-- `0.0728 < ϙ(4) < 0.073`. -/
theorem koppa_four_bounds : 0.0728 < ϙ 4 ∧ ϙ 4 < 0.073 := by
  have h := NRSOctahedron.vStar_bounds
  rw [koppa, threshold_four]
  constructor <;> linarith [h.1, h.2]

/-! ## 7. Certificate -/

/-- **The velocity band of forced defect.**

1. A minimum-uncertainty state moves exactly at `v*(d)`; on `Ϙ(d)` every unit state carries a
   Robertson–Schrödinger surplus.
2. At `d = 2, 3` the band is empty: `ϙ = 0`.
3. For `d ≥ 4` its width is at least `((d − 1)/2) · bandWidth d > 0`.
4. At `d = 4`, `Ϙ(4) = (v*(4), 1]` and `ϙ(4) = (7 − 3√5)/4`. -/
theorem velocityBand_certificate :
    (∀ d : ℕ, 2 ≤ d →
      (∃ ψ : Hd d, ‖ψ‖ = 1 ∧ surplus d ψ = 0 ∧ |velocity d ψ| = threshold d) ∧
      ∀ ψ : Hd d, ‖ψ‖ = 1 → |velocity d ψ| ∈ Ϙ d → 0 < surplus d ψ) ∧
    ϙ 2 = 0 ∧ ϙ 3 = 0 ∧
    (∀ d : ℕ, 4 ≤ d →
      0 < ((d : ℝ) - 1) / 2 * bandWidth d ∧ ((d : ℝ) - 1) / 2 * bandWidth d ≤ ϙ d) ∧
    Ϙ 4 = Set.Ioc NRSOctahedron.vStar 1 ∧ ϙ 4 = (7 - 3 * √5) / 4 :=
  ⟨fun _ hd => ⟨exists_saturated_threshold (by omega), surplus_pos_of_mem_band hd⟩,
    koppa_eq_zero (Or.inl rfl), koppa_eq_zero (Or.inr rfl),
    fun _ hd => ⟨bandWidth_speed_pos hd, koppa_ge hd⟩, band_four, koppa_four⟩

end VelocityBand

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle
public import NavaRobertsonIndependent.Mathematics.D40_SpeedLimitUncertainty
public import NavaRobertsonIndependent.Mathematics.D23d_BandWidth

/-!
# D48 — Robertson–Schrödinger 1929–30 with discrete transport: spectrum bounds

The original Robertson–Schrödinger inequality is not contradicted by the transport pair
`(T_d, P_d)`; it is bounded, with exact restrictions. On every path with `d ≥ 4` sites:

* **Minimum `0°`, attained.** The per-state angle `θ(ψ)` lies in `[0, π/2]`, and
  `θ(ψ) = 0` exactly at saturation, i.e. when the Gram defect of `D23` vanishes (`D23`).
* **Maximum on maximal tension.** Over the maximal-tension states (`⟨K_d⟩ = 2/(d−1)`,
  `D21`) the angle is `θ_NRS(d)`, attained at `ψ*`; the universal floor is
  `θ_NRS(4) = arccos (1 / √((99 − 42√5)/5))` (D37b).
* **Uniform ceiling, never attained.** `θ_NRS(d) < arccos (1 / C_∞)` for every `d ≥ 4`
  (D37b), so no state of any `d` reaches the ceiling.
* **Cone exclusion.** A unit state moving at the cone velocity `velocity d ψ = 1` has
  strictly positive defect (`D40`): minimum uncertainty never rides at the speed limit.
* **Forced-defect band.** Below the cone there is an open band of width `bandWidth d`
  where the inequality is strict (`D23d`).

## Main results

- `SpectrumBounds.angleState` : the per-state angle `θ(ψ)` of `(T_d, P_d)`, `D37b`'s
  `angleG` on the path.
- `SpectrumBounds.angleState_mem_Icc` : `θ(ψ) ∈ [0, π/2]` whenever `Var T_d · Var P_d > 0`.
- `SpectrumBounds.angleState_eq_zero_iff` : `θ(ψ) = 0` iff the Gram defect vanishes.
- `SpectrumBounds.angleState_eq_angleNRS_of_maxTension` : the maximum over the
  maximal-tension states is `θ_NRS(d)`.
- `SpectrumBounds.angleNRS_spectrum_bounds` : `θ_NRS(4) ≤ θ_NRS(d) < arccos (1 / C_∞)`.
- `SpectrumBounds.defect_pos_of_velocity_eq_one` : at the cone velocity the defect is strict.
- `SpectrumBounds.spectrum_band` : the open forced-defect band of `D23d`.

**Not proved here (work in progress).** The global maximality of `θ(ψ)` over *all* unit
states of a fixed `d` — `θ(ψ) ≤ θ_NRS(d)` for every `ψ` — is not established anywhere in
the package; `D48` records exactly what is proved. The maximum statement above is
restricted to the maximal-tension states, where `D21` forces the strict inequality.
-/

@[expose] public noncomputable section

namespace SpectrumBounds

open Real NRSInequality EigenvectorSaturation TransportPosition NRSAngle NearMaxTension
  GroupVelocity BandWidth Gnomon SpectralExtremal

/-- The per-state angle `θ(ψ)` of `(T_d, P_d)`: the angle between the two fluctuation
vectors, `arccos (‖⟪T̃ψ, P̃ψ⟫‖ / (‖T̃ψ‖ · ‖P̃ψ‖))`. At `ψ*` it is `θ_NRS(d)` (`angleNRS`). -/
def angleState (d : ℕ) (ψ : Hd d) : ℝ := angleG (TdOp d) (PdOp d) ψ

theorem angleState_psiStar (d : ℕ) : angleState d (psiStar d) = angleNRS d := rfl

/-- `D37b`'s `angleG` on the path is `arccos` of the ratio of the `D21` fluctuation
vectors. -/
theorem angleState_eq (d : ℕ) (ψ : Hd d) :
    angleState d ψ =
      arccos (‖inner ℂ (centered (TdOp d) ψ) (centered (PdOp d) ψ)‖ /
        (‖centered (TdOp d) ψ‖ * ‖centered (PdOp d) ψ‖)) := by
  unfold angleState angleG
  rfl

/-- `D37`'s `centeredG` is `D21`'s `centered` on the path. -/
theorem centeredG_eq_centered {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    PathGraph3DNRS.centeredG A ψ = centered A ψ := rfl

/-! ## 1. The per-state angle -/

private theorem variance_mul_pos_iff_norm_ne_zero {d : ℕ} {ψ : Hd d}
    (h : 0 < variance (TdOp d) ψ * variance (PdOp d) ψ) :
    ‖centered (TdOp d) ψ‖ ≠ 0 ∧ ‖centered (PdOp d) ψ‖ ≠ 0 := by
  unfold variance at h
  have key : ∀ a b : ℝ, 0 < a ^ 2 * b ^ 2 → a ≠ 0 ∧ b ≠ 0 := by
    intro a b hab
    rcases mul_pos_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h0 => by rw [h0, zero_pow two_ne_zero] at h1; exact (lt_irrefl (0:ℝ)) h1,
        fun h0 => by rw [h0, zero_pow two_ne_zero] at h2; exact (lt_irrefl (0:ℝ)) h2⟩
    · exact absurd h1 (not_lt.mpr (sq_nonneg a))
  exact key _ _ h

/-- The per-state angle lies in `[0, π/2]` whenever both variances do not vanish. -/
theorem angleState_mem_Icc {d : ℕ} {ψ : Hd d}
    (h : 0 < variance (TdOp d) ψ * variance (PdOp d) ψ) :
    angleState d ψ ∈ Set.Icc 0 (Real.pi / 2) := by
  have _ := variance_mul_pos_iff_norm_ne_zero h
  have hr0 : 0 ≤ ‖inner ℂ (centered (TdOp d) ψ) (centered (PdOp d) ψ)‖ /
      (‖centered (TdOp d) ψ‖ * ‖centered (PdOp d) ψ‖) :=
    div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨Real.arccos_nonneg _, ?_⟩
  rw [angleState_eq]
  exact Real.arccos_le_pi_div_two.mpr hr0

/-- `θ(ψ) = 0` exactly at saturation: the Gram defect of `D23` vanishes. -/
theorem angleState_eq_zero_iff {d : ℕ} {ψ : Hd d}
    (h : 0 < variance (TdOp d) ψ * variance (PdOp d) ψ) :
    angleState d ψ = 0 ↔ gramDefectAt (TdOp d) (PdOp d) ψ = 0 := by
  have hCS := norm_inner_le_norm (𝕜 := ℂ) (centered (TdOp d) ψ) (centered (PdOp d) ψ)
  constructor
  · intro h0
    rw [angleState_eq, arccos_eq_zero] at h0
    have hpos : (0 : ℝ) < ‖centered (TdOp d) ψ‖ * ‖centered (PdOp d) ψ‖ :=
      mul_pos (lt_of_le_of_ne (norm_nonneg _) (variance_mul_pos_iff_norm_ne_zero h).1.symm)
        (lt_of_le_of_ne (norm_nonneg _) (variance_mul_pos_iff_norm_ne_zero h).2.symm)
    have hge : ‖centered (TdOp d) ψ‖ * ‖centered (PdOp d) ψ‖ ≤
        ‖inner ℂ (centered (TdOp d) ψ) (centered (PdOp d) ψ)‖ := by
      have h' := (le_div_iff₀ hpos).mp h0
      rwa [one_mul] at h'
    have hr : ‖inner ℂ (centered (TdOp d) ψ) (centered (PdOp d) ψ)‖ =
        ‖centered (TdOp d) ψ‖ * ‖centered (PdOp d) ψ‖ := le_antisymm hCS hge
    unfold gramDefectAt variance
    rw [hr]
    ring
  · intro h0
    rw [angleState_eq, arccos_eq_zero]
    unfold gramDefectAt variance at h0
    rw [sub_eq_zero] at h0
    have hr : ‖inner ℂ (centered (TdOp d) ψ) (centered (PdOp d) ψ)‖ =
        ‖centered (TdOp d) ψ‖ * ‖centered (PdOp d) ψ‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
      rw [mul_pow, h0]
    rw [hr, div_self (mul_ne_zero (variance_mul_pos_iff_norm_ne_zero h).1
      (variance_mul_pos_iff_norm_ne_zero h).2)]

/-! ## 2. The maximum on maximal tension; the uniform ceiling -/

/-- The maximum of the per-state angle over the maximal-tension states is `θ_NRS(d)`:
every such state is a phase times `ψ*` (`D21`), and the angle is phase-invariant. -/
theorem angleState_eq_angleNRS_of_maxTension {d : ℕ} (hd : 4 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : tension d ψ = 2 / ((d : ℝ) - 1)) : angleState d ψ = angleNRS d := by
  obtain ⟨c, hc, rfl⟩ := maxTension_state_eq_phase (by omega) ψ hψ h
  rw [angleState_eq, angleNRS, angleG]
  congr 1
  rw [centeredG_eq_centered, centeredG_eq_centered, centered_phase _ _ _ hc,
    centered_phase _ _ _ hc, inner_smul_left, inner_smul_right,
    norm_smul, norm_smul, norm_mul, norm_mul, Complex.norm_conj, hc, one_mul, one_mul,
    one_mul, one_mul]

/-- The uniform ceiling of `D37b`, never attained: `θ_NRS(4) ≤ θ_NRS(d) < arccos (1 / C_∞)`
for every `d ≥ 4`. -/
theorem angleNRS_spectrum_bounds {d : ℕ} (hd : 4 ≤ d) :
    0 < angleNRS 4 ∧ angleNRS 4 ≤ angleNRS d ∧
      angleNRS d < arccos (1 / CoherenceConstantInf) :=
  angle_floor hd

/-! ## 3. Cone exclusion and the forced-defect band -/

/-- **Cone exclusion.** A unit state moving at the cone velocity, `velocity d ψ = 1`
(equivalently `⟨i[T_d, P_d]⟩ = 2/(d−1)`, its maximal value), has strictly positive
Gram defect: the strict inequality is non-negotiable at the speed limit (`D40`). -/
theorem defect_pos_of_velocity_eq_one {d : ℕ} (hd : 4 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : velocity d ψ = 1) : 0 < gramDefectAt (TdOp d) (PdOp d) ψ :=
  surplus_pos_of_velocity_eq_one hd ψ hψ h

/-- A minimum-uncertainty unit state moves strictly below the cone (`D40`). -/
theorem velocity_lt_one_of_defect_eq_zero {d : ℕ} (hd : 4 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h0 : gramDefectAt (TdOp d) (PdOp d) ψ = 0) : velocity d ψ < 1 :=
  velocity_lt_one_of_surplus_eq_zero hd ψ hψ h0

/-- **The forced-defect band of `D23d`.** For `d ≥ 4` the band width `bandWidth d` is
positive, and every unit state with tension within `bandWidth d` of the cone,
`⟨K_d⟩ > 2/(d−1) − bandWidth d`, satisfies Robertson–Schrödinger strictly. -/
theorem spectrum_band {d : ℕ} (hd : 4 ≤ d) :
    0 < bandWidth d ∧
      ∀ ψ : Hd d, ‖ψ‖ = 1 →
        2 / ((d : ℝ) - 1) - bandWidth d < tension d ψ →
          covariance (TdOp d) (PdOp d) ψ ^ 2 + tension d ψ ^ 2 / 4 <
            variance (TdOp d) ψ * variance (PdOp d) ψ :=
  ⟨bandWidth_pos hd, fun ψ hψ hK => strict_inequality_bandWidth hd ψ hψ hK⟩

end SpectrumBounds

end

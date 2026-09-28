/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D44_VelocityBand

/-!
# D46 — The cone lies in every band

The band `Ϙ(d) = (v*(d), 1]` narrows as `d` grows (`D45d`), but it never lets the cone speed
`|v| = 1` out: `ϙ(d) > 0` for every `d ≥ 4` (`D44`). Hence every unit state of `H_d` that is
transported at the cone speed carries a Robertson–Schrödinger surplus, whatever `d ≥ 4` is,
and none reaches the minimum uncertainty. The same holds on an explicit neighbourhood of the
cone, `|v| > 1 − ((d − 1)/2) · bandWidth d`.

The condition `d ≥ 4` is sharp: at `d = 2, 3`, `ψ*` moves at the cone and saturates.

The identification of the cone speed with the speed of light in vacuum is the physical bridge
of the README; it is a premise, not used here.

## Main results

- `ConeInBand.one_mem_band` : `1 ∈ Ϙ(d)` for every `d ≥ 4`.
- `ConeInBand.surplus_pos_of_near_cone` : the defect is forced on an explicit neighbourhood of
  the cone.
- `ConeInBand.surplus_pos_of_cone` : every unit state at the cone speed carries a surplus.
- `ConeInBand.cone_forced_iff` : the defect at the cone is forced exactly when `4 ≤ d`.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality NearMaxTension EigenvectorSaturation GramStep
open GroupVelocity BandWidth VelocityBand

namespace ConeInBand

variable {d : ℕ}

/-- **The cone lies in every band.** -/
theorem one_mem_band (hd : 4 ≤ d) : (1 : ℝ) ∈ Ϙ d :=
  ⟨by linarith [koppa_pos hd, show ϙ d = 1 - threshold d from rfl], le_rfl⟩

/-- Near the cone, within `((d − 1)/2) · bandWidth d`, no unit state is of minimum uncertainty. -/
theorem surplus_pos_of_near_cone (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (hv : 1 - ((d : ℝ) - 1) / 2 * bandWidth d < |velocity d ψ|) : 0 < surplus d ψ :=
  surplus_pos_of_threshold_lt (by omega) ψ hψ ((threshold_le hd).trans_lt hv)

/-- **At the cone speed the defect is forced**, for every `d ≥ 4`. -/
theorem surplus_pos_of_cone (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (hv : |velocity d ψ| = 1) : 0 < surplus d ψ :=
  surplus_pos_of_mem_band (by omega) ψ hψ (hv ▸ one_mem_band hd)

/-- **Sharpness.** The defect at the cone is forced exactly when `4 ≤ d`. -/
theorem cone_forced_iff (hd : 2 ≤ d) :
    (∀ ψ : Hd d, ‖ψ‖ = 1 → |velocity d ψ| = 1 → 0 < surplus d ψ) ↔ 4 ≤ d := by
  refine ⟨fun h => ?_, fun h4 => surplus_pos_of_cone h4⟩
  by_contra! h4
  have h0 := (surplus_psiStar_eq_zero_iff hd).2 (by omega)
  have := h (psiStar d) (norm_psiStar hd) (by rw [velocity_psiStar hd, abs_one])
  exact this.ne' h0

/-- **Certificate.** For every `d ≥ 4` the cone lies in the band and every unit state at the
cone speed carries a surplus; for `d = 2, 3`, `ψ*` saturates at the cone. -/
theorem coneInBand_certificate :
    (∀ d : ℕ, 4 ≤ d → (1 : ℝ) ∈ Ϙ d ∧
      ∀ ψ : Hd d, ‖ψ‖ = 1 → |velocity d ψ| = 1 → 0 < surplus d ψ) ∧
    (∀ d : ℕ, 2 ≤ d →
      ((∀ ψ : Hd d, ‖ψ‖ = 1 → |velocity d ψ| = 1 → 0 < surplus d ψ) ↔ 4 ≤ d)) :=
  ⟨fun _ hd => ⟨one_mem_band hd, surplus_pos_of_cone hd⟩, fun _ hd => cone_forced_iff hd⟩

end ConeInBand

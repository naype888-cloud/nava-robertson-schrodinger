/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50_ProperTimeSurplus
public import NavaRobertsonCertificados.D49e_AxisDefectEntangled

/-!
# D50c — Proper time of an axis for every state of the open cube

`D49e` already proves the defect of an axis for every state `Φ` of a product `ℂ^d ⊗ ℂ^β`, entangled
or not. The proper time of that axis is the square root of the same Gram defect: nothing is
defined beyond `√`. For a state `ψ ⊗ φ` it is the `τ` of `D50`.

## Main results

- `ProperTimeAxis.properTimeAxis_pos_of_band` : speed in `Ϙ(d)` gives a positive proper time, for
  every unit state.
- `ProperTimeAxis.properTimeAxis_prodAlong` : on `ψ ⊗ φ` it is `ProperTime.properTime d ψ`.
- `ProperTimeAxis.properTime_cube_pos_of_band` : on the cube, speeds in `Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)`
  give three positive proper times, for every state.
-/

@[expose] public noncomputable section

open TransportPosition NearMaxTension GroupVelocity VelocityBand PathGraph3DNRS CauchyGram
  AxisDefectEntangled ProperTime EigenvectorSaturation NRSInequality

namespace ProperTimeAxis

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β] {d : ℕ}

/-- The proper time of the axis `e` of a state `Φ`: the square root of the Gram defect of the
fluctuations of `(T, P)` on that axis. -/
def properTimeAxis (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) : ℝ :=
  √(gramDefectC (centeredG (Matrix.toEuclideanLin (liftAlong e (Td d))) Φ)
    (centeredG (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ))

omit [Fintype β] in
theorem properTimeAxis_sq (e : ι ≃ Fin d × β) (Φ : EuclideanSpace ℂ ι) :
    properTimeAxis e Φ ^ 2 =
      gramDefectC (centeredG (Matrix.toEuclideanLin (liftAlong e (Td d))) Φ)
        (centeredG (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ) :=
  Real.sq_sqrt (gramDefectC_nonneg _ _)

/-- **The proper time of an axis in the band, for every state.** -/
theorem properTimeAxis_pos_of_band (hd : 2 ≤ d) (e : ι ≃ Fin d × β) {Φ : EuclideanSpace ℂ ι}
    (hΦ : ‖Φ‖ = 1)
    (hb : |((d : ℝ) - 1) / 2 * tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
      (Matrix.toEuclideanLin (liftAlong e (Pd d))) Φ| ∈ Ϙ d) :
    0 < properTimeAxis e Φ :=
  Real.sqrt_pos.mpr (gramDefect_pos_of_band hd e hΦ hb)

variable {dx dy dz : ℕ}

/-- **Three proper times on the cube, for every state.** -/
theorem properTime_cube_pos_of_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    {Φ : H3D dx dy dz} (hΦ : ‖Φ‖ = 1) (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy)
    (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    0 < properTimeAxis (eX dx dy dz) Φ * properTimeAxis (eY dx dy dz) Φ *
      properTimeAxis (eZ dx dy dz) Φ := by
  have a := Real.sqrt_pos.mpr (gramDefect_pos_of_band hx (eX dx dy dz) hΦ hbx)
  have b := Real.sqrt_pos.mpr (gramDefect_pos_of_band hy (eY dx dy dz) hΦ hby)
  have c := Real.sqrt_pos.mpr (gramDefect_pos_of_band hz (eZ dx dy dz) hΦ hbz)
  exact mul_pos (mul_pos a b) c

/-- **On `ψ ⊗ φ` the proper time of the axis is that of `ψ`** (`D50`). -/
theorem properTimeAxis_prodAlong (e : ι ≃ Fin d × β) {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1)
    (ψ : Hd d) :
    properTimeAxis e (prodAlong e ψ φ) = properTime d ψ := by
  unfold properTimeAxis properTime
  congr 1
  rw [centeredG_lift e hφ, centeredG_lift e hφ]
  unfold gramDefectC varianceC
  rw [inner_prodAlong, inner_self_of_norm_one hφ, norm_sq_prodAlong e _ _ hφ,
    norm_sq_prodAlong e _ _ hφ]
  simp only [mul_one, surplus, gramDefectAt, variance, centered, centeredG]
  rfl

end ProperTimeAxis

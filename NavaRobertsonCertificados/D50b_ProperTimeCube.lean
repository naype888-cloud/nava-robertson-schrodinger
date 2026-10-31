/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50_ProperTimeSurplus
public import NavaRobertsonIndependent.Mathematics.D49c_RobertsonDeterminantProduct

/-!
# D50b — Proper time on the open cube: one per axis

The speed limit of the open cube is a cube, not a sphere: the maximal current state moves with
squared speed `3` while each axis is bounded by `1` (`D38`, `speed_sq_maxCurrentCubeState`). So the
proper time of the cube is not a Minkowski norm of the three velocities. It is one proper time per
axis, `τ_x, τ_y, τ_z` (`D50`), and they enter the cube only through the determinant of Robertson's
relation for the six observables (`D49c`):

  `det Σ = (τ_x² + t_x²/4)(τ_y² + t_y²/4)(τ_z² + t_z²/4)`,  `|det Ω| = (t_x t_y t_z / 8)²`.

Nothing is defined here: `τ_i² = surplus` and `D49c` is rewritten.

## Main results

- `ProperTimeCube.det_covMatrix_prod3_properTime` : `det Σ` in terms of the three proper times.
- `ProperTimeCube.robertson_det_prod3_properTime` : three positive proper times make `det|RS^N³`
  strict on a product state.
- `ProperTimeCube.properTime_cube_pos` : at the maximal current state of the cube every axis has
  positive proper time when `dx, dy, dz ≥ 4`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition NRSInequality NearMaxTension PathGraph3DNRS RobertsonDeterminant
  RobertsonDeterminant3D RobertsonDeterminantProduct ProperTime CubeSpectrum

namespace ProperTimeCube

variable {dx dy dz : ℕ} {u : Hd dx} {v : Hd dy} {w : Hd dz}
  (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)

include hu hv hw in
/-- `det Σ` of a product state in terms of the proper time and the tension of each axis. -/
theorem det_covMatrix_prod3_properTime :
    (covMatrix (pairs dx dy dz) (prod3 u v w)).det =
      (properTime dx u ^ 2 + tension dx u ^ 2 / 4) * (properTime dy v ^ 2 + tension dy v ^ 2 / 4) *
        (properTime dz w ^ 2 + tension dz w ^ 2 / 4) := by
  rw [det_covMatrix_prod3 hu hv hw, properTime_sq, properTime_sq, properTime_sq]

include hu hv hw in
/-- **A proper time on each axis makes det|RS^N³ strict.** -/
theorem robertson_det_prod3_properTime (hx : 0 < properTime dx u) (hy : 0 < properTime dy v)
    (hz : 0 < properTime dz w) :
    ((tensionG (TX dx dy dz) (PX dx dy dz) (prod3 u v w) *
        tensionG (TY dx dy dz) (PY dx dy dz) (prod3 u v w) *
          tensionG (TZ dx dy dz) (PZ dx dy dz) (prod3 u v w)) / 8) ^ 2 <
      (covMatrix (pairs dx dy dz) (prod3 u v w)).det := by
  refine robertson_det_prod3_strict hu hv hw ?_ ?_ ?_ <;>
    rw [← properTime_sq] <;> positivity

/-- **The maximal current state of the cube has a proper time on every axis** when the box has at
least `4` positions on each. -/
theorem properTime_cube_pos (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    0 < properTime dx (maxCurrentState dx) ∧ 0 < properTime dy (maxCurrentState dy) ∧
      0 < properTime dz (maxCurrentState dz) :=
  ⟨properTime_maxCurrentState_pos hx, properTime_maxCurrentState_pos hy,
    properTime_maxCurrentState_pos hz⟩

end ProperTimeCube

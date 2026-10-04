/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D46_ConeInBand
public import NavaRobertsonIndependent.Mathematics.D49c_RobertsonDeterminantProduct

/-!
# D49d — det|NRS³ in the band `Ϙ`

On a product state `Φ = u ⊗ v ⊗ w` of the cube, `det Σ = Π (s_i + t_i²/4)` (`D49c`). If the
speed of each factor lies in its band `Ϙ(d_i) = (v*(d_i), 1]`, each factor carries a
Robertson–Schrödinger surplus (`D44`), and `det|NRS³` is strict: the three defects of `x`, `y`,
`z` are positive and so is their product. The cone `|v| = 1` lies in every band for `d ≥ 4`
(`D46`), so at the cone speed on the three axes the bound is never attained.

The statement is for product states. For states entangled across axes it is not proved here.

## Main results

- `RobertsonDeterminantBand.robertson_det_band` : speeds in `Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)` give
  `(t_x t_y t_z / 8)² < det Σ`.
- `RobertsonDeterminantBand.robertson_det_cone` : the same at the cone speed, for every box
  with `dx, dy, dz ≥ 4`.
-/

@[expose] public noncomputable section

open TransportPosition NearMaxTension GroupVelocity VelocityBand ConeInBand PathGraph3DNRS
open RobertsonDeterminant RobertsonDeterminant3D RobertsonDeterminantProduct CubeSpectrum

namespace RobertsonDeterminantBand

variable {dx dy dz : ℕ} {u : Hd dx} {v : Hd dy} {w : Hd dz}

/-- **det|NRS³ in the band.** Unit factors whose speeds lie in `Ϙ(dx)`, `Ϙ(dy)`, `Ϙ(dz)` make
the bound strict. -/
theorem robertson_det_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hbx : |velocity dx u| ∈ Ϙ dx) (hby : |velocity dy v| ∈ Ϙ dy)
    (hbz : |velocity dz w| ∈ Ϙ dz) :
    ((tensionG (TX dx dy dz) (PX dx dy dz) (prod3 u v w) *
        tensionG (TY dx dy dz) (PY dx dy dz) (prod3 u v w) *
          tensionG (TZ dx dy dz) (PZ dx dy dz) (prod3 u v w)) / 8) ^ 2 <
      (covMatrix (pairs dx dy dz) (prod3 u v w)).det :=
  robertson_det_prod3_strict hu hv hw (surplus_pos_of_mem_band hx u hu hbx)
    (surplus_pos_of_mem_band hy v hv hby) (surplus_pos_of_mem_band hz w hw hbz)

/-- **det|NRS³ at the cone.** On every box with at least `4` positions on each axis, unit factors
moving at the cone speed on `x`, `y` and `z` make the bound strict. -/
theorem robertson_det_cone (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hcx : |velocity dx u| = 1) (hcy : |velocity dy v| = 1)
    (hcz : |velocity dz w| = 1) :
    ((tensionG (TX dx dy dz) (PX dx dy dz) (prod3 u v w) *
        tensionG (TY dx dy dz) (PY dx dy dz) (prod3 u v w) *
          tensionG (TZ dx dy dz) (PZ dx dy dz) (prod3 u v w)) / 8) ^ 2 <
      (covMatrix (pairs dx dy dz) (prod3 u v w)).det :=
  robertson_det_band (by omega) (by omega) (by omega) hu hv hw (hcx ▸ one_mem_band hx)
    (hcy ▸ one_mem_band hy) (hcz ▸ one_mem_band hz)

end RobertsonDeterminantBand

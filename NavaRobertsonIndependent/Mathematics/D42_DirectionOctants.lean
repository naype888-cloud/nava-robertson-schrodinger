/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D41_MandelstamTammCramerRao

/-!
# D42 — Direction is a sign; the bounds do not see it

The direction of motion of `⟨P_d⟩` is the sign of the tension `⟨K_d⟩` (`D38`). A symmetry `U`
that commutes with `L` and reverses `M` reverses the tension and keeps both variances, so the
Mandelstam–Tamm and Cramér–Rao ratio of `D41` and the NRS angle of `D37b` are the same for both
directions. The reflection `j ↦ d − 1 − j` of the path is such a symmetry for `(T_d, P_d)`: the
spectrum of `K_d` is symmetric, and `ψ*` reflected moves at velocity `−1`.

On the cube `d × d × d` the three reflections give the eight octant states: velocity `(±1, ±1, ±1)`,
one vertex of the velocity cube for each face of the octahedral cone of `D37f`, and on every axis
the same ratio `1 / C_Nava(d)²` and the same angle `θ_NRS(d)`; at `4 × 4 × 4`, `7.43°`.

## Main results

- `Direction.tensionG_anti`, `Direction.mtRatioG_anti`, `Direction.angleG_anti` : a symmetry
  that reverses `M` reverses the tension and keeps the ratio and the angle.
- `Direction.tension_reflect`, `Direction.mtRatio_reflect` : the reflection of the path.
- `Direction.KdOp_reflect_eigen` : the spectrum of `K_d` is symmetric.
- `Direction.velocities_octant`, `Direction.mtRatioG_octant_x`, `Direction.angleG_octant_x` (and
  `_y`, `_z`) : the eight octants of the cube.
- `Direction.octant_four` : at `4 × 4 × 4`, every octant misses both bounds by the same quantum.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality NearMaxTension GramStep PathGraph3DNRS CubeSpectrum
open NRSAngle GroupVelocity SpectralExtremal Gnomon

namespace Direction

/-! ## 1. A symmetry that reverses `M` -/

section General

variable {ι : Type*} [Fintype ι] (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
  {L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}

theorem meanG_comm (hL : ∀ v, L (U v) = U (L v)) (Ψ : EuclideanSpace ℂ ι) :
    meanG L (U Ψ) = meanG L Ψ := by
  rw [meanG, meanG, hL, LinearIsometryEquiv.inner_map_map]

theorem meanG_anti (hM : ∀ v, M (U v) = -U (M v)) (Ψ : EuclideanSpace ℂ ι) :
    meanG M (U Ψ) = -meanG M Ψ := by
  rw [meanG, meanG, hM, inner_neg_right, LinearIsometryEquiv.inner_map_map, Complex.neg_re]

theorem centeredG_comm (hL : ∀ v, L (U v) = U (L v)) (Ψ : EuclideanSpace ℂ ι) :
    centeredG L (U Ψ) = U (centeredG L Ψ) := by
  rw [centeredG, centeredG, meanG_comm U hL, hL, map_sub, map_smul]

theorem centeredG_anti (hM : ∀ v, M (U v) = -U (M v)) (Ψ : EuclideanSpace ℂ ι) :
    centeredG M (U Ψ) = -U (centeredG M Ψ) := by
  rw [centeredG, centeredG, meanG_anti U hM, hM, map_sub, map_smul, Complex.ofReal_neg,
    neg_smul]
  abel

theorem varianceG_comm (hL : ∀ v, L (U v) = U (L v)) (Ψ : EuclideanSpace ℂ ι) :
    varianceG L (U Ψ) = varianceG L Ψ := by
  rw [varianceG, varianceG, centeredG_comm U hL, LinearIsometryEquiv.norm_map]

theorem varianceG_anti (hM : ∀ v, M (U v) = -U (M v)) (Ψ : EuclideanSpace ℂ ι) :
    varianceG M (U Ψ) = varianceG M Ψ := by
  rw [varianceG, varianceG, centeredG_anti U hM, norm_neg, LinearIsometryEquiv.norm_map]

variable (hL : ∀ v, L (U v) = U (L v)) (hM : ∀ v, M (U v) = -U (M v))
include hL hM

/-- The tension observable anticommutes with `U`. -/
theorem observableTension_anti (v : EuclideanSpace ℂ ι) :
    observableTension L M (U v) = -U (observableTension L M v) := by
  simp only [observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, hL, hM, map_neg, map_sub, map_smul, smul_sub, smul_neg]
  abel

/-- **Direction.** `U` reverses the tension, hence the motion of `⟨M⟩`. -/
theorem tensionG_anti (Ψ : EuclideanSpace ℂ ι) : tensionG L M (U Ψ) = -tensionG L M Ψ := by
  rw [tensionG, tensionG, observableTension_anti U hL hM, inner_neg_right,
    LinearIsometryEquiv.inner_map_map, Complex.neg_re]

theorem covarianceG_anti (Ψ : EuclideanSpace ℂ ι) :
    covarianceG L M (U Ψ) = -covarianceG L M Ψ := by
  rw [covarianceG, covarianceG, centeredG_comm U hL, centeredG_anti U hM, inner_neg_right,
    LinearIsometryEquiv.inner_map_map, Complex.neg_re]

/-- **The bounds do not see direction.** The Mandelstam–Tamm and Cramér–Rao ratio is kept. -/
theorem mtRatioG_anti (Ψ : EuclideanSpace ℂ ι) : mtRatioG L M (U Ψ) = mtRatioG L M Ψ := by
  rw [mtRatioG, mtRatioG, tensionG_anti U hL hM, varianceG_comm U hL, varianceG_anti U hM,
    neg_sq]

/-- The angle between the fluctuation vectors is kept. -/
theorem angleG_anti (Ψ : EuclideanSpace ℂ ι) : angleG L M (U Ψ) = angleG L M Ψ := by
  rw [angleG, angleG, centeredG_comm U hL, centeredG_anti U hM, inner_neg_right, norm_neg,
    norm_neg, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]

/-- `U` sends an eigenvector of `i[L, M]` with eigenvalue `λ` to one with eigenvalue `−λ`. -/
theorem eigen_anti {v : EuclideanSpace ℂ ι} {c : ℝ} (h : observableTension L M v = (c : ℂ) • v) :
    observableTension L M (U v) = ((-c : ℝ) : ℂ) • U v := by
  rw [observableTension_anti U hL hM, h, map_smul, Complex.ofReal_neg, neg_smul]

end General

/-! ## 2. The reflection of the path -/

variable {d : ℕ}

/-- The reflection `j ↦ d − 1 − j` of the path. -/
def reflect (d : ℕ) : Hd d ≃ₗᵢ[ℂ] Hd d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ Fin.revPerm

theorem reflect_apply (v : Hd d) (i : Fin d) : reflect d v i = v i.rev := by
  simp [reflect]

theorem Td_rev (i j : Fin d) : Td d i.rev j = Td d i j.rev := by
  have h : MinStep i.rev j ↔ MinStep i j.rev := by
    simp only [MinStep, Fin.val_rev]
    omega
  simp only [Td, Ad, h]

theorem posCoord_rev (i : Fin d) : posCoord d i.rev = -posCoord d i := by
  have h : ((i.rev.val : ℕ) : ℝ) = d - 1 - i := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [posCoord, posCoord, h]
  ring

theorem TdOp_reflect (v : Hd d) : TdOp d (reflect d v) = reflect d (TdOp d v) := by
  ext i
  simp only [TdOp, reflect_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct]
  rw [← Equiv.sum_comp Fin.revPerm (fun j => Td d i.rev j * v j)]
  simp [Td_rev]

theorem PdOp_reflect (v : Hd d) : PdOp d (reflect d v) = -reflect d (PdOp d v) := by
  ext i
  simp [PdOp, Pd, reflect_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, posCoord_rev]

/-- The reflection reverses the direction of motion. -/
theorem tension_reflect (ψ : Hd d) : tension d (reflect d ψ) = -tension d ψ :=
  tensionG_anti (reflect d) TdOp_reflect PdOp_reflect ψ

theorem velocity_reflect (ψ : Hd d) : velocity d (reflect d ψ) = -velocity d ψ := by
  rw [velocity, velocity, tension_reflect]
  ring

/-- Both directions attain the same fraction of the Mandelstam–Tamm and Cramér–Rao bounds. -/
theorem mtRatio_reflect (ψ : Hd d) : mtRatio d (reflect d ψ) = mtRatio d ψ :=
  mtRatioG_anti (reflect d) TdOp_reflect PdOp_reflect ψ

/-- The spectrum of `K_d` is symmetric: `λ` and `−λ` come in pairs. -/
theorem KdOp_reflect_eigen {v : Hd d} {c : ℝ} (h : KdOp d v = (c : ℂ) • v) :
    KdOp d (reflect d v) = ((-c : ℝ) : ℂ) • reflect d v :=
  eigen_anti (reflect d) TdOp_reflect PdOp_reflect h

/-! ## 3. `ψ*` in both directions -/

/-- `ψ*` forward (`false`) or reflected (`true`). -/
def psiDir (d : ℕ) (b : Bool) : Hd d := bif b then reflect d (psiStar d) else psiStar d

/-- The sign of a direction. -/
def sgn (b : Bool) : ℝ := bif b then -1 else 1

theorem norm_psiDir (hd : 2 ≤ d) (b : Bool) : ‖psiDir d b‖ = 1 := by
  cases b <;> simp [psiDir, norm_psiStar hd]

theorem velocity_psiDir (hd : 2 ≤ d) (b : Bool) : velocity d (psiDir d b) = sgn b := by
  cases b <;> simp [psiDir, sgn, velocity_reflect, velocity_psiStar hd]

theorem mtRatio_psiDir (hd : 2 ≤ d) (b : Bool) :
    mtRatio d (psiDir d b) = 1 / CoherenceConstant d ^ 2 := by
  cases b <;>
    simp only [psiDir, Bool.cond_true, Bool.cond_false, mtRatio_reflect, mtRatio_psiStar hd]

theorem angle_psiDir (b : Bool) : angleG (TdOp d) (PdOp d) (psiDir d b) = angleNRS d := by
  cases b
  · rfl
  · exact angleG_anti (reflect d) TdOp_reflect PdOp_reflect _

/-! ## 4. The eight octants of the cube -/

variable {dx dy dz : ℕ}

/-- The octant state: `ψ*` on each axis, reflected on the axes marked `true`. -/
def octant (dx dy dz : ℕ) (sx sy sz : Bool) : H3D dx dy dz :=
  prod3 (psiDir dx sx) (psiDir dy sy) (psiDir dz sz)

theorem norm_rest_dir {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (s t : Bool) :
    ‖prodAlong (Equiv.refl _) (psiDir a s) (psiDir b t)‖ = 1 :=
  norm_prodAlong_eq_one _ (norm_psiDir ha s) (norm_psiDir hb t)

section Octant

variable (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (sx sy sz : Bool)
include hx hy hz

/-- The octant `(sx, sy, sz)` moves at velocity `(±1, ±1, ±1)`. -/
theorem velocities_octant :
    velocityX (octant dx dy dz sx sy sz) = sgn sx ∧ velocityY (octant dx dy dz sx sy sz) = sgn sy ∧
      velocityZ (octant dx dy dz sx sy sz) = sgn sz := by
  refine ⟨?_, ?_, ?_⟩
  · rw [velocityX, octant, prod3_eq_eX, TX, PX,
      tensionG_lift _ (norm_rest_dir hy hz sy sz)]
    exact velocity_psiDir hx sx
  · rw [velocityY, octant, prod3_eq_eY, TY, PY,
      tensionG_lift _ (norm_rest_dir hx hz sx sz)]
    exact velocity_psiDir hy sy
  · rw [velocityZ, octant, prod3_eq_eZ, TZ, PZ,
      tensionG_lift _ (norm_rest_dir hx hy sx sy)]
    exact velocity_psiDir hz sz

theorem mtRatioG_octant_x :
    mtRatioG (TX dx dy dz) (PX dx dy dz) (octant dx dy dz sx sy sz) =
      1 / CoherenceConstant dx ^ 2 := by
  have h := norm_rest_dir hy hz sy sz
  rw [mtRatioG, octant, prod3_eq_eX, TX, PX, tensionG_lift _ h, varianceG_lift _ h,
    varianceG_lift _ h]
  exact mtRatio_psiDir hx sx

theorem mtRatioG_octant_y :
    mtRatioG (TY dx dy dz) (PY dx dy dz) (octant dx dy dz sx sy sz) =
      1 / CoherenceConstant dy ^ 2 := by
  have h := norm_rest_dir hx hz sx sz
  rw [mtRatioG, octant, prod3_eq_eY, TY, PY, tensionG_lift _ h, varianceG_lift _ h,
    varianceG_lift _ h]
  exact mtRatio_psiDir hy sy

theorem mtRatioG_octant_z :
    mtRatioG (TZ dx dy dz) (PZ dx dy dz) (octant dx dy dz sx sy sz) =
      1 / CoherenceConstant dz ^ 2 := by
  have h := norm_rest_dir hx hy sx sy
  rw [mtRatioG, octant, prod3_eq_eZ, TZ, PZ, tensionG_lift _ h, varianceG_lift _ h,
    varianceG_lift _ h]
  exact mtRatio_psiDir hz sz

omit hx in
theorem angleG_octant_x :
    angleG (TX dx dy dz) (PX dx dy dz) (octant dx dy dz sx sy sz) = angleNRS dx := by
  rw [octant, prod3_eq_eX, TX, PX, angleG_lift _ (norm_rest_dir hy hz sy sz)]
  exact angle_psiDir sx

omit hy in
theorem angleG_octant_y :
    angleG (TY dx dy dz) (PY dx dy dz) (octant dx dy dz sx sy sz) = angleNRS dy := by
  rw [octant, prod3_eq_eY, TY, PY, angleG_lift _ (norm_rest_dir hx hz sx sz)]
  exact angle_psiDir sy

omit hz in
theorem angleG_octant_z :
    angleG (TZ dx dy dz) (PZ dx dy dz) (octant dx dy dz sx sy sz) = angleNRS dz := by
  rw [octant, prod3_eq_eZ, TZ, PZ, angleG_lift _ (norm_rest_dir hx hy sx sy)]
  exact angle_psiDir sz

end Octant

/-- **The base `4 × 4 × 4`.** Every octant moves at the speed limit on each axis, meets on each
axis at `θ_NRS(4) ≈ 7.43°`, and misses Mandelstam–Tamm and Cramér–Rao by the same quantum. -/
theorem octant_four (sx sy sz : Bool) :
    |velocityX (octant 4 4 4 sx sy sz)| = 1 ∧ |velocityY (octant 4 4 4 sx sy sz)| = 1 ∧
      |velocityZ (octant 4 4 4 sx sy sz)| = 1 ∧
      angleG (TX 4 4 4) (PX 4 4 4) (octant 4 4 4 sx sy sz) = angleNRS 4 ∧
      angleG (TY 4 4 4) (PY 4 4 4) (octant 4 4 4 sx sy sz) = angleNRS 4 ∧
      angleG (TZ 4 4 4) (PZ 4 4 4) (octant 4 4 4 sx sy sz) = angleNRS 4 ∧
      mtRatioG (TX 4 4 4) (PX 4 4 4) (octant 4 4 4 sx sy sz) < 1 := by
  have h4 : (2 : ℕ) ≤ 4 := by norm_num
  have habs : ∀ b, |sgn b| = 1 := fun b => by cases b <;> simp [sgn]
  obtain ⟨vx, vy, vz⟩ := velocities_octant h4 h4 h4 sx sy sz
  refine ⟨vx ▸ habs sx, vy ▸ habs sy, vz ▸ habs sz, angleG_octant_x h4 h4 sx sy sz,
    angleG_octant_y h4 h4 sx sy sz, angleG_octant_z h4 h4 sx sy sz, ?_⟩
  rw [mtRatioG_octant_x h4 h4 h4, ← mtRatio_psiStar h4]
  exact mtRatio_psiStar_lt_one le_rfl

end Direction

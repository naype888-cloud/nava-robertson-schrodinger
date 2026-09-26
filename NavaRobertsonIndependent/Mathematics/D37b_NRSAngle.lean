/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# D37b — The NRS angle

Robertson–Schrödinger is Cauchy–Schwarz for the fluctuation vectors `x = (T − ⟨T⟩)ψ`,
`y = (P − ⟨P⟩)ψ`: it saturates iff they are parallel. At `ψ*` their angle satisfies
`cos θ_NRS(d) = |⟪x, y⟫| / (‖x‖ ‖y‖) = 1 / C_Nava(d)`.

## Main results

- `NRSAngle.cos_angleNRS` : `cos θ_NRS(d) = 1 / C_Nava(d)`.
- `NRSAngle.angleNRS_eq_zero_iff` : `θ_NRS(d) = 0 ↔ d = 2 ∨ d = 3`.
- `NRSAngle.angle_floor` : for `d ≥ 4`, `0 < θ_NRS(4) ≤ θ_NRS(d) < arccos (1 / C_∞)`, with
  `θ_NRS(4) = arccos (1 / √((99 − 42√5)/5)) ≈ 7.43°` (`angleNRS_four`).
- `NRSAngle.finite_isotropy_cube` : axes with at least `D ≥ 4` sites differ in angle by less
  than `arccos (1 / C_∞) − θ_NRS(D)`.
-/

@[expose] public noncomputable section

open Real TransportPosition NRSInequality SpectralExtremal Gnomon
open PathGraph3DNRS EigenvectorSaturation

namespace NRSAngle

/-! ## 1. The angle between two fluctuation vectors -/

/-- Angle between the fluctuation vectors of `L` and `M` at `Ψ`, on any finite site set. -/
def angleG {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  arccos (‖inner ℂ (centeredG L Ψ) (centeredG M Ψ)‖ / (‖centeredG L Ψ‖ * ‖centeredG M Ψ‖))

/-- The NRS angle of `(T_d, P_d)` at `ψ*`. -/
def angleNRS (d : ℕ) : ℝ := angleG (TdOp d) (PdOp d) (psiStar d)

theorem CoherenceConstant_ge_one {d : ℕ} (hd : 2 ≤ d) : 1 ≤ CoherenceConstant d := by
  rw [CoherenceConstant_eq_one_add_geometricGap]
  linarith [geometricGap_nonneg hd]

/-- **The NRS angle.** `cos θ_NRS(d) = 1 / C_Nava(d)`. -/
theorem cos_angleNRS {d : ℕ} (hd : 2 ≤ d) :
    ‖inner ℂ (centered (TdOp d) (psiStar d)) (centered (PdOp d) (psiStar d))‖ /
        (‖centered (TdOp d) (psiStar d)‖ * ‖centered (PdOp d) (psiStar d)‖) =
      1 / CoherenceConstant d := by
  set a := ‖inner ℂ (centered (TdOp d) (psiStar d)) (centered (PdOp d) (psiStar d))‖
  set b := ‖centered (TdOp d) (psiStar d)‖ * ‖centered (PdOp d) (psiStar d)‖
  set k := (commutatorConstant d / 2) ^ 2
  have hC := CoherenceConstant_ge_one hd
  have hk : 0 < k := commutatorConstant_half_sq_pos hd
  -- `a² = k`: the Gram defect with `cov = 0` and tension `2/(d−1)`.
  have ha : a ^ 2 = k := by
    have h := NearMaxTension.surplus_eq d (psiStar d)
    rw [NearMaxTension.surplus, gramDefectAt, covariance_eq_zero hd,
      NearMaxTension.tension_psiStar hd] at h
    have hk' : k = 1 / ((d : ℝ) - 1) ^ 2 := commutatorConstant_half_sq hd
    have hd1 : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [hk']
    field_simp at h ⊢
    linarith
  -- `b² = k · C²`: `variance_mul_variance`.
  have hb : b ^ 2 = (a * CoherenceConstant d) ^ 2 := by
    have h := variance_mul_variance hd
    rw [variance, variance, ← CoherenceConstant_eq_one_add_geometricGap] at h
    rw [mul_pow, h, mul_pow, ha]
  have ha0 : 0 < a := by
    have : a = Real.sqrt k := by rw [← ha, Real.sqrt_sq (norm_nonneg _)]
    rw [this]; exact Real.sqrt_pos.mpr hk
  have hbeq : b = a * CoherenceConstant d :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hb
  rw [hbeq]
  field_simp

theorem angleNRS_eq {d : ℕ} (hd : 2 ≤ d) : angleNRS d = arccos (1 / CoherenceConstant d) := by
  rw [angleNRS, angleG]
  exact congrArg arccos (cos_angleNRS hd)

/-! ## 2. Where the angle opens -/

/-- The angle is zero exactly at the seeds `d = 2, 3`. -/
theorem angleNRS_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) : angleNRS d = 0 ↔ d = 2 ∨ d = 3 := by
  have hC := CoherenceConstant_ge_one hd
  rw [angleNRS_eq hd, arccos_eq_zero, le_div_iff₀ (by linarith), one_mul,
    ← CoherenceConstant_eq_one_iff d hd]
  constructor <;> intro h <;> linarith

/-- **The algebraic quantum as an angle.** On every axis with `4` or more sites the two
fluctuation vectors are never parallel. -/
theorem angleNRS_pos {d : ℕ} (hd : 4 ≤ d) : 0 < angleNRS d := by
  have hC : 1 < CoherenceConstant d := by
    rw [CoherenceConstant_eq_one_add_geometricGap]
    linarith [geometricGap_pos_of_four_le d hd]
  rw [angleNRS_eq (by omega), arccos_pos, div_lt_one (by linarith)]
  exact hC

theorem CoherenceConstantInf_pos : 0 < CoherenceConstantInf := by
  have := deltaInf_pos
  unfold deltaInf at this
  linarith

/-- The angle opens strictly with `d` from `4` on. -/
theorem angleNRS_strictMonoOn : StrictMonoOn angleNRS {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  have ha' : (4 : ℕ) ≤ a := ha
  have hb' : (4 : ℕ) ≤ b := hb
  have hCa := CoherenceConstant_ge_one (by omega : 2 ≤ a)
  have hCb := CoherenceConstant_ge_one (by omega : 2 ≤ b)
  have hlt : CoherenceConstant a < CoherenceConstant b := by
    have := geometricGap_strictMonoOn_ge_four ha hb hab
    simpa [geometricGap] using this
  rw [angleNRS_eq (by omega), angleNRS_eq (by omega)]
  have hb0 : 0 < 1 / CoherenceConstant b := one_div_pos.mpr (by linarith)
  apply arccos_lt_arccos (by linarith)
  · exact one_div_lt_one_div_of_lt (by linarith) hlt
  · rw [div_le_one (by linarith)]; exact hCa

/-- The angle stays strictly below `arccos (1 / C_∞)`, which no `d` attains. -/
theorem angleNRS_lt_limit {d : ℕ} (hd : 4 ≤ d) :
    angleNRS d < arccos (1 / CoherenceConstantInf) := by
  have hCd := CoherenceConstant_ge_one (by omega : 2 ≤ d)
  have hlt : CoherenceConstant d < CoherenceConstantInf := by
    have := geometricGap_lt_deltaInf d hd
    simpa [geometricGap, deltaInf] using this
  rw [angleNRS_eq (by omega)]
  apply arccos_lt_arccos (by have := one_div_pos.mpr CoherenceConstantInf_pos; linarith)
  · exact one_div_lt_one_div_of_lt (by linarith) hlt
  · rw [div_le_one (by linarith)]; exact hCd

/-- The first opening, in closed form: `θ_NRS(4) = arccos (1 / √((99 − 42√5)/5))`. -/
theorem angleNRS_four :
    angleNRS 4 = arccos (1 / Real.sqrt ((99 - 42 * Real.sqrt 5) / 5)) := by
  rw [angleNRS_eq (by norm_num), CoherenceConstant, CoherenceConstantSq_four_eq]

/-- **Universal angular floor.** Every axis with `4` or more sites opens at least `θ_NRS(4)`,
and never reaches `arccos (1 / C_∞)`. -/
theorem angle_floor {d : ℕ} (hd : 4 ≤ d) :
    0 < angleNRS 4 ∧ angleNRS 4 ≤ angleNRS d ∧
      angleNRS d < arccos (1 / CoherenceConstantInf) :=
  ⟨angleNRS_pos le_rfl,
    angleNRS_strictMonoOn.monotoneOn (show (4 : ℕ) ≤ 4 from le_rfl) hd hd,
    angleNRS_lt_limit hd⟩

/-- **Finite isotropy for two rows.** If both rows have at least `D ≥ 4` sites, their angles
differ by less than `arccos (1 / C_∞) − θ_NRS(D)`: a statement about finite rows only, with the
unattained ceiling `arccos (1 / C_∞)` as the sole reference. -/
theorem angleNRS_isotropy {D a b : ℕ} (hD : 4 ≤ D) (ha : D ≤ a) (hb : D ≤ b) :
    |angleNRS a - angleNRS b| < arccos (1 / CoherenceConstantInf) - angleNRS D := by
  have mono := angleNRS_strictMonoOn.monotoneOn
  have hDa : angleNRS D ≤ angleNRS a := mono (show 4 ≤ D from hD) (show 4 ≤ a by omega) ha
  have hDb : angleNRS D ≤ angleNRS b := mono (show 4 ≤ D from hD) (show 4 ≤ b by omega) hb
  have la := angleNRS_lt_limit (show 4 ≤ a by omega)
  have lb := angleNRS_lt_limit (show 4 ≤ b by omega)
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ## 3. One angle per axis of the cube -/

section Cubo

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
  [DecidableEq ι] [DecidableEq α] [DecidableEq β]

theorem angleG_lift (e : ι ≃ α × β) {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1)
    (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    angleG (Matrix.toEuclideanLin (liftAlong e A)) (Matrix.toEuclideanLin (liftAlong e B))
        (prodAlong e ψ φ) =
      angleG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  have hn : ∀ v : EuclideanSpace ℂ α, ‖prodAlong e v φ‖ = ‖v‖ := fun v =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (norm_sq_prodAlong e v φ hφ)
  rw [angleG, angleG, centeredG_lift e hφ, centeredG_lift e hφ, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one, hn, hn]

variable {dx dy dz : ℕ}

theorem angleG_axis_x (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    angleG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) = angleNRS dx := by
  rw [PsiStar3D_eq_eX]
  exact angleG_lift _ (norm_rest hy hz) _ _ _

theorem angleG_axis_y (hx : 2 ≤ dx) (hz : 2 ≤ dz) :
    angleG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) = angleNRS dy := by
  rw [PsiStar3D_eq_eY]
  exact angleG_lift _ (norm_rest hx hz) _ _ _

theorem angleG_axis_z (hx : 2 ≤ dx) (hy : 2 ≤ dy) :
    angleG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) = angleNRS dz := by
  rw [PsiStar3D_eq_eZ]
  exact angleG_lift _ (norm_rest hx hy) _ _ _

/-- **On the `4 × 4 × 4` cube and beyond**, all three axes carry a strictly positive angle,
each below the same unattained bound `arccos (1 / C_∞)`. -/
theorem angles_cube (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    (0 < angleG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) ∧
        angleG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) <
          arccos (1 / CoherenceConstantInf)) ∧
      (0 < angleG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) ∧
        angleG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) <
          arccos (1 / CoherenceConstantInf)) ∧
      (0 < angleG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) ∧
        angleG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) <
          arccos (1 / CoherenceConstantInf)) := by
  rw [angleG_axis_x (by omega) (by omega), angleG_axis_y (by omega) (by omega),
    angleG_axis_z (by omega) (by omega)]
  exact ⟨⟨angleNRS_pos hx, angleNRS_lt_limit hx⟩, ⟨angleNRS_pos hy, angleNRS_lt_limit hy⟩,
    ⟨angleNRS_pos hz, angleNRS_lt_limit hz⟩⟩

/-- **The angular floor on the cube.** With `4` or more sites on every axis, each of the three
axes opens at least `θ_NRS(4)`. -/
theorem angle_floor_cube (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    angleNRS 4 ≤ angleG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) ∧
      angleNRS 4 ≤ angleG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) ∧
      angleNRS 4 ≤ angleG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) := by
  rw [angleG_axis_x (by omega) (by omega), angleG_axis_y (by omega) (by omega),
    angleG_axis_z (by omega) (by omega)]
  exact ⟨(angle_floor hx).2.1, (angle_floor hy).2.1, (angle_floor hz).2.1⟩

/-- **Finite isotropy of the cube.** In any cube with at least `D ≥ 4` sites on every axis, the
angles of any two axes differ by less than `arccos (1 / C_∞) − θ_NRS(D)`. With `D = 100` this is
about `1.05°`: the three axes agree more closely the more sites each has, with no appeal
to an infinite lattice. -/
theorem finite_isotropy_cube {D : ℕ} (hD : 4 ≤ D) (hx : D ≤ dx) (hy : D ≤ dy) (hz : D ≤ dz) :
    |angleG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) -
        angleG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz)| <
        arccos (1 / CoherenceConstantInf) - angleNRS D ∧
      |angleG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) -
        angleG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz)| <
        arccos (1 / CoherenceConstantInf) - angleNRS D ∧
      |angleG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) -
        angleG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz)| <
        arccos (1 / CoherenceConstantInf) - angleNRS D := by
  rw [angleG_axis_x (by omega) (by omega), angleG_axis_y (by omega) (by omega),
    angleG_axis_z (by omega) (by omega)]
  exact ⟨angleNRS_isotropy hD hx hy, angleNRS_isotropy hD hx hz,
    angleNRS_isotropy hD hy hz⟩

end Cubo

end NRSAngle

end

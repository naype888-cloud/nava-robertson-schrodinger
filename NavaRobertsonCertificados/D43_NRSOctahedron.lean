/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D23g_MinUncertaintyUpperBound
public import NavaRobertsonIndependent.Mathematics.D42_DirectionOctants

/-!
# D43 — The Nava–Robertson–Schrödinger octahedron

The irreducible elemental dimensional quantum of uncertainty, on the base `4 × 4 × 4` of NRS³.
Transport spreads inside the octahedron `|Δx| + |Δy| + |Δz| ≤ k` (`D37f`); in each of its eight
directions the state at the speed limit meets Robertson–Schrödinger at `θ_NRS(4) ≈ 7.43°` on every
axis (`D42`), and the angle never closes for `d ≥ 4` (`D37b`).

The quantum is set by the velocity. On an axis of `4` sites, minimum uncertainty is possible up
to `v*(4) = 3(√5 − 1)/4 ≈ 0.927` of the cone, in both directions, and not beyond (`D23f`, `D23g`
and the reflection of `D42`). Past `v*(4)` the defect is forced. At the speed limit the
Mandelstam–Tamm and Cramér–Rao ratio is `5 / (99 − 42√5) ≈ 0.9833`.

## Main results

- `NRSOctahedron.abs_velocity_le_of_saturated` : minimum uncertainty moves at most at `v*(4)`.
- `NRSOctahedron.vStar_isGreatest`, `NRSOctahedron.neg_vStar_isLeast` : `±v*(4)` are attained.
- `NRSOctahedron.surplus_pos_of_vStar_lt` : beyond `v*(4)` the defect is forced.
- `NRSOctahedron.vStar_bounds`, `NRSOctahedron.mtRatio_psiStar_four_bounds` : the numbers.
- `NRSOctahedron.lightCone_rhombus` : on two axes the cone is the rhombus `|Δx| + |Δy| ≤ k`.
- `NRSOctahedron.navaRobertsonSchrodinger_octahedron` : everything at once.
-/

@[expose] public noncomputable section

open Real TransportPosition NRSInequality NearMaxTension EigenvectorSaturation SpectralExtremal
open Gnomon PathGraph3DNRS NRSAngle GroupVelocity Direction LightCone MinUncertaintyFour
open MinUncertaintyBoundFour
open PathGraph3D (Site3D)

namespace NRSOctahedron

variable {d : ℕ}

/-! ## 1. Minimum uncertainty in both directions -/

/-- The reflection keeps the Robertson–Schrödinger surplus. -/
theorem gramDefect_reflect (ψ : Hd d) :
    gramDefectAt (TdOp d) (PdOp d) (reflect d ψ) = gramDefectAt (TdOp d) (PdOp d) ψ := by
  have hT : centered (TdOp d) (reflect d ψ) = reflect d (centered (TdOp d) ψ) :=
    centeredG_comm (reflect d) TdOp_reflect ψ
  have hP : centered (PdOp d) (reflect d ψ) = -reflect d (centered (PdOp d) ψ) :=
    centeredG_anti (reflect d) PdOp_reflect ψ
  simp only [gramDefectAt, variance, hT, hP, norm_neg, inner_neg_right,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map]

/-- The velocity threshold of minimum uncertainty at `d = 4`: `v*(4) = 3(√5 − 1)/4`. -/
def vStar : ℝ := 3 * (√5 - 1) / 4

theorem velocity_four (ψ : Hd 4) : velocity 4 ψ = 3 / 2 * tension 4 ψ := by
  rw [velocity]
  norm_num

/-- **Threshold.** A minimum-uncertainty state of `H₄` moves at most at `v*(4)`, either way. -/
theorem abs_velocity_le_of_saturated (ψ : Hd 4) (hψ : ‖ψ‖ = 1)
    (hsat : gramDefectAt (TdOp 4) (PdOp 4) ψ = 0) : |velocity 4 ψ| ≤ vStar := by
  have h1 := tension_le_of_saturated ψ hψ hsat
  have h2 := tension_le_of_saturated (reflect 4 ψ) (by rw [LinearIsometryEquiv.norm_map, hψ])
    (by rw [gramDefect_reflect, hsat])
  rw [tension_reflect] at h2
  rw [velocity_four, vStar, abs_le]
  constructor <;> linarith

theorem velocity_psiSat : velocity 4 psiSat = vStar := by
  rw [velocity_four, tension_psiSat, vStar]
  ring

/-- The velocities of the minimum-uncertainty states of `H₄`. -/
def satVelocities : Set ℝ :=
  {v | ∃ ψ : Hd 4, ‖ψ‖ = 1 ∧ gramDefectAt (TdOp 4) (PdOp 4) ψ = 0 ∧ velocity 4 ψ = v}

/-- `v*(4)` is the fastest minimum-uncertainty velocity. -/
theorem vStar_isGreatest : IsGreatest satVelocities vStar :=
  ⟨⟨psiSat, norm_psiSat, saturated_psiSat, velocity_psiSat⟩,
    fun _ ⟨ψ, hψ, hs, hv⟩ => hv ▸ (le_abs_self _).trans (abs_velocity_le_of_saturated ψ hψ hs)⟩

/-- `−v*(4)` is the fastest in the other direction. -/
theorem neg_vStar_isLeast : IsLeast satVelocities (-vStar) :=
  ⟨⟨reflect 4 psiSat, by rw [LinearIsometryEquiv.norm_map, norm_psiSat],
      by rw [gramDefect_reflect, saturated_psiSat], by rw [velocity_reflect, velocity_psiSat]⟩,
    fun _ ⟨ψ, hψ, hs, hv⟩ => hv ▸ neg_le_of_abs_le (abs_velocity_le_of_saturated ψ hψ hs)⟩

/-- **The defect is forced.** Beyond `v*(4)` Robertson–Schrödinger is strict. -/
theorem surplus_pos_of_vStar_lt (ψ : Hd 4) (hψ : ‖ψ‖ = 1) (hv : vStar < |velocity 4 ψ|) :
    0 < surplus 4 ψ :=
  lt_of_le_of_ne (gramDefectAt_nonneg _ _ _) fun h =>
    absurd (abs_velocity_le_of_saturated ψ hψ h.symm) (not_le.mpr hv)

/-! ## 2. The numbers -/

/-- `0.927 < v*(4) < 0.9272`. -/
theorem vStar_bounds : 0.927 < vStar ∧ vStar < 0.9272 := by
  have h1 : (2.236 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < 2.2362 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [vStar]
  constructor <;> linarith

theorem vStar_lt_one : vStar < 1 := by linarith [vStar_bounds.2]

/-- At the speed limit, the Mandelstam–Tamm and Cramér–Rao ratio is `5 / (99 − 42√5)`. -/
theorem mtRatio_psiStar_four : mtRatio 4 (psiStar 4) = 5 / (99 - 42 * √5) := by
  have h5 : √5 < 99 / 42 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [mtRatio_psiStar (by norm_num), CoherenceConstant,
    Real.sq_sqrt (by rw [CoherenceConstantSq_four_eq]; linarith), CoherenceConstantSq_four_eq,
    one_div_div]

/-- `0.9831 < 5 / (99 − 42√5) < 0.9834`: both bounds are missed by `1.7 %`. -/
theorem mtRatio_psiStar_four_bounds :
    0.9831 < mtRatio 4 (psiStar 4) ∧ mtRatio 4 (psiStar 4) < 0.9834 := by
  have h1 : (2.23606 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √5 < 2.23607 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : 0 < 99 - 42 * √5 := by linarith
  rw [mtRatio_psiStar_four]
  constructor
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-! ## 3. The cone on two axes -/

/-- On two axes (`dz = 1`) the cone of `D37f` is the rhombus `|Δx| + |Δy| ≤ k`. -/
theorem lightCone_rhombus {dx dy : ℕ} (k : ℕ) (p q : Site3D dx dy 1)
    (h : k < distPath p.1 q.1 + distPath p.2.1 q.2.1) : (T3 dx dy 1 ^ k) p q = 0 := by
  apply lightCone_cube k p q
  have : p.2.2 = q.2.2 := Subsingleton.elim _ _
  simpa only [distCube, this, distPath_self, add_zero] using h

/-! ## 4. The octahedron -/

/-- **The Nava–Robertson–Schrödinger octahedron**: the irreducible elemental dimensional quantum
of uncertainty on the base `4 × 4 × 4` of NRS³.

1. Transport spreads inside the octahedron `|Δx| + |Δy| + |Δz| ≤ k`.
2. Each of its eight directions moves at the speed limit on every axis, meets
   Robertson–Schrödinger at `θ_NRS(4)` on every axis, and misses Mandelstam–Tamm and Cramér–Rao.
3. `θ_NRS(4) = arccos (1 / √((99 − 42√5)/5)) ≈ 7.43°` is positive, is the floor of every axis
   with `d ≥ 4` sites, and no axis reaches `arccos (1 / C_∞)`.
4. At the speed limit the Mandelstam–Tamm and Cramér–Rao ratio is `5 / (99 − 42√5) < 1`.
5. Minimum uncertainty reaches exactly `±v*(4) = ±3(√5 − 1)/4`, below the cone; beyond it the
   defect is forced. -/
theorem navaRobertsonSchrodinger_octahedron :
    (∀ (k : ℕ) (p q : Site3D 4 4 4), k < distCube p q → (T3 4 4 4 ^ k) p q = 0) ∧
    (∀ sx sy sz : Bool,
      |velocityX (octant 4 4 4 sx sy sz)| = 1 ∧ |velocityY (octant 4 4 4 sx sy sz)| = 1 ∧
      |velocityZ (octant 4 4 4 sx sy sz)| = 1 ∧
      angleG (TX 4 4 4) (PX 4 4 4) (octant 4 4 4 sx sy sz) = angleNRS 4 ∧
      angleG (TY 4 4 4) (PY 4 4 4) (octant 4 4 4 sx sy sz) = angleNRS 4 ∧
      angleG (TZ 4 4 4) (PZ 4 4 4) (octant 4 4 4 sx sy sz) = angleNRS 4 ∧
      mtRatioG (TX 4 4 4) (PX 4 4 4) (octant 4 4 4 sx sy sz) < 1) ∧
    angleNRS 4 = arccos (1 / √((99 - 42 * √5) / 5)) ∧
    (∀ d : ℕ, 4 ≤ d → 0 < angleNRS 4 ∧ angleNRS 4 ≤ angleNRS d ∧
      angleNRS d < arccos (1 / CoherenceConstantInf)) ∧
    mtRatio 4 (psiStar 4) = 5 / (99 - 42 * √5) ∧ mtRatio 4 (psiStar 4) < 1 ∧
    IsGreatest satVelocities vStar ∧ IsLeast satVelocities (-vStar) ∧ vStar < 1 ∧
    (∀ ψ : Hd 4, ‖ψ‖ = 1 → vStar < |velocity 4 ψ| → 0 < surplus 4 ψ) :=
  ⟨fun k p q h => lightCone_cube k p q h, octant_four, angleNRS_four, fun _ hd => angle_floor hd,
    mtRatio_psiStar_four, mtRatio_psiStar_lt_one le_rfl, vStar_isGreatest, neg_vStar_isLeast,
    vStar_lt_one, surplus_pos_of_vStar_lt⟩

end NRSOctahedron

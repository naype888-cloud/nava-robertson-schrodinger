/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16_ClosedSurfaceTransport

/-!
# D16b — Gauss–Bonnet: the transported defect fixes the total curvature

`D16` gives `Ω(Σ_g) = b₁ δ_∞` with `b₁ = 2g`; Gauss–Bonnet gives `∫K dA = 2πχ` with
`χ = 2 − 2g`. Eliminating `b₁`:

* `∫K dA = 4π − (2π/δ_∞) Ω(Σ_g)` (`totalCurvature_of_defect`);
* with `R = 2K`, `∫R dA = 8π − (4π/δ_∞) Ω(Σ_g)` (`scalarIntegral_of_defect`).

The relation is affine and global: defect and curvature measure the same `b₁`. It is not
local: the interior of the path has curvature `0` (`D28`, `D28b`).

`HGaussBonnet` is a declared hypothesis (Mathlib has no Gauss–Bonnet), shown satisfiable.

## Main results

- `Gnomon.totalCurvature_of_defect`, `Gnomon.scalarIntegral_of_defect`.
- `Gnomon.HGaussBonnet.torus` : curvature `0` and defect `2δ_∞ > 0`.
- `Gnomon.HGaussBonnet.defect_determines_genus`.
-/

@[expose] public noncomputable section

open Real

namespace Gnomon

/-- The Euler characteristic `χ = 2 − 2g` of `Σ_g`. -/
def eulerChar (g : ℕ) : ℝ := 1 - ((2 * g : ℕ) : ℝ) + 1

theorem eulerChar_eq (g : ℕ) : eulerChar g = 2 - 2 * g := by
  unfold eulerChar; push_cast; ring

/-- **Gauss–Bonnet (declared hypothesis).** The total curvature of `Σ_g` is `2πχ`. -/
structure HGaussBonnet where
  totalCurvature : ℕ → ℝ
  gauss_bonnet : ∀ g, totalCurvature g = 2 * π * eulerChar g

theorem hGaussBonnet_satisfiable : Nonempty HGaussBonnet :=
  ⟨⟨fun g => 2 * π * eulerChar g, fun _ => rfl⟩⟩

namespace HGaussBonnet

variable (H : HGaussBonnet)

/-- The integral of the scalar curvature in 2D, `∫R dA = 2∫K dA`. -/
def scalarIntegral (g : ℕ) : ℝ := 2 * H.totalCurvature g

/-- The total curvature is an affine function of the transported defect. -/
theorem totalCurvature_of_defect (g : ℕ) :
    H.totalCurvature g = 4 * π - (2 * π / deltaInf) * closedSurfaceDefect g := by
  rw [H.gauss_bonnet, eulerChar_eq, closedSurfaceDefect_eq_two_mul_genus_mul]
  field_simp [deltaInf_pos.ne']
  ring

/-- `∫R dA = 8π − (4π/δ_∞) Ω(Σ_g)`. -/
theorem scalarIntegral_of_defect (g : ℕ) :
    H.scalarIntegral g = 8 * π - (4 * π / deltaInf) * closedSurfaceDefect g := by
  unfold scalarIntegral
  rw [H.totalCurvature_of_defect]
  ring

/-- Sphere: curvature `4π`, defect `0`. -/
theorem sphere : H.totalCurvature 0 = 4 * π ∧ closedSurfaceDefect 0 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [H.gauss_bonnet, eulerChar_eq]; ring
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul]; simp

/-- Torus: curvature `0`, defect `2δ_∞ > 0`. -/
theorem torus :
    H.totalCurvature 1 = 0 ∧ closedSurfaceDefect 1 = 2 * deltaInf ∧
      0 < closedSurfaceDefect 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [H.gauss_bonnet, eulerChar_eq]; ring
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul]; ring
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul]; push_cast; linarith [deltaInf_pos]

/-- More genus: more defect, less curvature. -/
theorem more_genus {g₁ g₂ : ℕ} (h : g₁ < g₂) :
    closedSurfaceDefect g₁ < closedSurfaceDefect g₂ ∧
      H.totalCurvature g₂ < H.totalCurvature g₁ := by
  have hg : (g₁ : ℝ) < g₂ := by exact_mod_cast h
  have hd := deltaInf_pos
  have hp := pi_pos
  refine ⟨?_, ?_⟩
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul, closedSurfaceDefect_eq_two_mul_genus_mul]
    nlinarith
  · rw [H.gauss_bonnet, H.gauss_bonnet, eulerChar_eq, eulerChar_eq]
    nlinarith

end HGaussBonnet

/-- The defect determines the genus. -/
theorem defect_determines_genus {g₁ g₂ : ℕ}
    (h : closedSurfaceDefect g₁ = closedSurfaceDefect g₂) : g₁ = g₂ := by
  rw [closedSurfaceDefect_eq_two_mul_genus_mul, closedSurfaceDefect_eq_two_mul_genus_mul] at h
  have hd := deltaInf_pos.ne'
  have : (g₁ : ℝ) = g₂ := by
    have h2 : 2 * deltaInf * ((g₁ : ℝ) - g₂) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso; exact hd (by linarith)
    · linarith
  exact_mod_cast this

end Gnomon

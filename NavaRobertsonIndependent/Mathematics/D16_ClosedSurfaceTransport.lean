/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# D16 — The asymptotic defect on closed surfaces

The finite sum that carries `Gnomon.deltaInf` to a closed orientable surface of genus `g`.
`closedSurfaceDefect g` is defined as the sum of `δ_∞` over the `2g` cycles of `b₁(Σ_g) = 2g`;
that each essential cycle carries `δ_∞` and that `b₁ = 2g` are inputs of the definition. What
is proved is the arithmetic of the sum and its closed form.

## Main results

- `Gnomon.closedSurfaceDefect_eq_two_mul_genus_mul` : `Ω(Σ_g) = 2g δ_∞`.
- `Gnomon.closedSurface_transport_chain` : the four identities together.
-/

@[expose] public noncomputable section

open Real

namespace Gnomon

/-- The sum of the defects on `b₁` independent cycles. -/
def cycleDefectSum (b₁ : ℕ) (defect : Fin b₁ → ℝ) : ℝ :=
  ∑ i, defect i

/-- A constant defect on each cycle sums to `b₁ · defect`. -/
theorem cycleDefectSum_of_constant (b₁ : ℕ) (defect : Fin b₁ → ℝ) (c : ℝ)
    (hdefect : ∀ i, defect i = c) :
    cycleDefectSum b₁ defect = (b₁ : ℝ) * c := by
  simp [cycleDefectSum, hdefect]

/-- The defect of `Σ_g`: `δ_∞` on each of the `2g` generators of `H₁`. -/
def closedSurfaceDefect (g : ℕ) : ℝ :=
  cycleDefectSum (2 * g) fun _ => deltaInf

/-- Through the first Betti number `b₁(Σ_g) = 2g`. -/
theorem closedSurfaceDefect_eq_firstBetti_mul (g : ℕ) :
    closedSurfaceDefect g = ((2 * g : ℕ) : ℝ) * deltaInf := by
  exact cycleDefectSum_of_constant (2 * g) (fun _ => deltaInf) deltaInf fun _ => rfl

/-- By genus: `Ω(Σ_g) = 2g δ_∞`. -/
theorem closedSurfaceDefect_eq_two_mul_genus_mul (g : ℕ) :
    closedSurfaceDefect g = 2 * (g : ℝ) * deltaInf := by
  rw [closedSurfaceDefect_eq_firstBetti_mul]
  push_cast
  rfl

/-- The closed form of `δ_∞` used in the surface formula. -/
theorem deltaInf_closed_form :
    deltaInf = Real.sqrt ((π ^ 2 - 6) / 3) - 1 := by
  unfold deltaInf CoherenceConstantInf
  congr 2
  ring

/-- `Ω(Σ_g)` in fully expanded form. -/
theorem closedSurfaceDefect_closed_form (g : ℕ) :
    closedSurfaceDefect g =
      2 * (g : ℝ) * (Real.sqrt ((π ^ 2 - 6) / 3) - 1) := by
  rw [closedSurfaceDefect_eq_two_mul_genus_mul, deltaInf_closed_form]

/-- The four identities of the transport to closed surfaces. -/
theorem closedSurface_transport_chain (g : ℕ) :
    closedSurfaceDefect g =
        cycleDefectSum (2 * g) (fun _ => deltaInf) ∧
      cycleDefectSum (2 * g) (fun _ => deltaInf) = ((2 * g : ℕ) : ℝ) * deltaInf ∧
      ((2 * g : ℕ) : ℝ) * deltaInf = 2 * (g : ℝ) * deltaInf ∧
      deltaInf = Real.sqrt ((π ^ 2 - 6) / 3) - 1 := by
  refine ⟨rfl, closedSurfaceDefect_eq_firstBetti_mul g, ?_, deltaInf_closed_form⟩
  push_cast
  rfl

end Gnomon

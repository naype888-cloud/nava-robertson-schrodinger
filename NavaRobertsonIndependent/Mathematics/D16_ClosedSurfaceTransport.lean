/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# Transporte del defect asintótico a superficies cerradas

Este archivo aísla el paso de suma finita que transporta el defect universal
`Gnomon.deltaInf` a una superficie orientable cerrada de género `g`. La entrada
topológica es la identidad estándar `b₁(Σ_g) = 2g`; la entrada analítica es la
forma cerrada de `deltaInf` demostrada en `D8_Szego`.

Estatus del argumento: `closedSurfaceDefect g` se **define** como la suma de
`δ_∞` sobre `2g` ciclos. Que cada ciclo esencial cargue `δ_∞` y que `b₁(Σ_g) = 2g`
son entradas de la definición, no teoremas de este archivo; lo que se demuestra
es la aritmética de la suma y la forma cerrada.
-/

@[expose] public noncomputable section

open Real

namespace Gnomon

/-- Suma de los defects asociados a una familia de `b₁` ciclos independientes. -/
def cycleDefectSum (b₁ : ℕ) (defect : Fin b₁ → ℝ) : ℝ :=
  ∑ i, defect i

/-- Un defect constante en cada ciclo independiente suma `b₁ * defect`. -/
theorem cycleDefectSum_of_constant (b₁ : ℕ) (defect : Fin b₁ → ℝ) (c : ℝ)
    (hdefect : ∀ i, defect i = c) :
    cycleDefectSum b₁ defect = (b₁ : ℝ) * c := by
  simp [cycleDefectSum, hdefect]

/-- Defect superficial obtenido al asignar `deltaInf` a cada uno de los `2g`
generadores de la primera homología de una superficie orientable cerrada. -/
def closedSurfaceDefect (g : ℕ) : ℝ :=
  cycleDefectSum (2 * g) fun _ => deltaInf

/-- Transporte mediante el primer número de Betti `b₁(Σ_g) = 2g`. -/
theorem closedSurfaceDefect_eq_firstBetti_mul (g : ℕ) :
    closedSurfaceDefect g = ((2 * g : ℕ) : ℝ) * deltaInf := by
  exact cycleDefectSum_of_constant (2 * g) (fun _ => deltaInf) deltaInf fun _ => rfl

/-- Forma cerrada por género: `Ω(Σ_g) = 2g δ_∞`. -/
theorem closedSurfaceDefect_eq_two_mul_genus_mul (g : ℕ) :
    closedSurfaceDefect g = 2 * (g : ℝ) * deltaInf := by
  rw [closedSurfaceDefect_eq_firstBetti_mul]
  push_cast
  rfl

/-- Forma cerrada equivalente del defect asintótico usada en la fórmula superficial. -/
theorem deltaInf_closed_form :
    deltaInf = Real.sqrt ((π ^ 2 - 6) / 3) - 1 := by
  unfold deltaInf CoherenceConstantInf
  congr 2
  ring

/-- Forma completamente expandida del defect de una superficie de género `g`. -/
theorem closedSurfaceDefect_closed_form (g : ℕ) :
    closedSurfaceDefect g =
      2 * (g : ℝ) * (Real.sqrt ((π ^ 2 - 6) / 3) - 1) := by
  rw [closedSurfaceDefect_eq_two_mul_genus_mul, deltaInf_closed_form]

/-- Las cuatro igualdades que forman el transporte a superficies cerradas. -/
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

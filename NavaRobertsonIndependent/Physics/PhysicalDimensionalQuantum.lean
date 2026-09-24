import NavaRobertsonIndependent.Physics.ElementalCellStep
import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum

/-!
# El cuanto dimensional, en unidades: longitud y tiempo en cada `H_d`

Lectura física de `D25_CuantoDimensional`. `d` es la dimensión de Hilbert; cada `H_d`
tiene su cuanto `δ(d)`, y con él su paso y su tick:

* longitud: `longitudPaso d = √Ω_b · l_P · δ(d)` (calibración de `PasoElementalCelda`);
* tiempo: `tickDim d := longitudPaso d / c_lab`, lo que tarda `c` en recorrer el paso.

En `H_4` el tick es `τ_sbpk := L_sbpk / c_lab` (`tickDim_cuatro`), y es el **mínimo**
sobre toda dimensión abierta (`Tausbpk_le_tickDim`). Recorrer el camino de `H_d` son
`d − 1` aristas de `pathGraph d`; su velocidad es exactamente `c` en toda dimensión
(`velocidad_recorrido`), porque el paso y el tick llevan el mismo cuanto.

`c` es la entrada de laboratorio; lo que se obtiene es el tiempo mínimo.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace CuantoDimensionalFisico

open LimiteSubPlanckiano ColapsoSchwarzschild PasoElementalCelda

/-- El paso de `H_d` es la escala de laboratorio por el cuanto de `H_d`. -/
theorem longitudPaso_eq_cuanto (d : ℕ) :
    longitudPaso d = escalaLongitud * CuantoDimensional.cuantoDim d := rfl

theorem longitudPaso_pos {d : ℕ} (hd : 4 ≤ d) : 0 < longitudPaso d :=
  lt_of_lt_of_le Lsbpk_pos (Lsbpk_le_longitudPaso hd)

/-- El paso crece estrictamente con la dimensión. -/
theorem longitudPaso_strictMono {d₀ d₁ : ℕ} (h₀ : 4 ≤ d₀) (h : d₀ < d₁) :
    longitudPaso d₀ < longitudPaso d₁ :=
  mul_lt_mul_of_pos_left (CuantoDimensional.cuantoDim_strictMono h₀ h) escalaLongitud_pos

/-- Tick de `H_d`: lo que tarda `c` en recorrer el paso de `H_d`. -/
def tickDim (d : ℕ) : ℝ := longitudPaso d / cSI

/-- En `H_4` el tick es `τ_sbpk`. -/
theorem tickDim_cuatro : tickDim 4 = Tausbpk := by
  unfold tickDim Tausbpk; rw [longitudPaso_cuatro]; rfl

/-- **`τ_sbpk` es el tiempo mínimo**: ninguna dimensión abierta tiene un tick menor. -/
theorem Tausbpk_le_tickDim {d : ℕ} (hd : 4 ≤ d) : Tausbpk ≤ tickDim d := by
  rw [← tickDim_cuatro]; unfold tickDim
  exact div_le_div_of_nonneg_right
    (by rw [longitudPaso_cuatro]; exact Lsbpk_le_longitudPaso hd) cSI_pos.le

theorem tickDim_pos {d : ℕ} (hd : 4 ≤ d) : 0 < tickDim d :=
  div_pos (longitudPaso_pos hd) cSI_pos

theorem tickDim_strictMono {d₀ d₁ : ℕ} (h₀ : 4 ≤ d₀) (h : d₀ < d₁) :
    tickDim d₀ < tickDim d₁ :=
  div_lt_div_of_pos_right (longitudPaso_strictMono h₀ h) cSI_pos

/-- Longitud del recorrido de `H_d`: las `d − 1` aristas de `pathGraph d`. -/
def longitudRecorrido (d : ℕ) : ℝ := ((d : ℝ) - 1) * longitudPaso d

/-- Duración del recorrido de `H_d`: un tick de `H_d` por arista. -/
def duracionRecorrido (d : ℕ) : ℝ := ((d : ℝ) - 1) * tickDim d

/-- En toda dimensión el recorrido va exactamente a `c`. -/
theorem velocidad_recorrido {d : ℕ} (hd : 4 ≤ d) :
    longitudRecorrido d / duracionRecorrido d = cSI := by
  have h1 : (0:ℝ) < (d:ℝ) - 1 := by
    have : (4:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold longitudRecorrido duracionRecorrido tickDim
  field_simp [h1.ne', (longitudPaso_pos hd).ne', cSI_pos.ne']

/-- **Más dimensión, más largo y más tiempo, a la misma `c`.** -/
theorem mas_dimension_mas_tiempo {d₀ d₁ : ℕ} (h₀ : 4 ≤ d₀) (h : d₀ < d₁) :
    longitudRecorrido d₀ < longitudRecorrido d₁ ∧
    duracionRecorrido d₀ < duracionRecorrido d₁ ∧
    longitudRecorrido d₀ / duracionRecorrido d₀ = cSI ∧
    longitudRecorrido d₁ / duracionRecorrido d₁ = cSI := by
  have e0 : (0:ℝ) < (d₀:ℝ) - 1 := by
    have : (4:ℝ) ≤ d₀ := by exact_mod_cast h₀
    linarith
  have ed : (d₀:ℝ) - 1 < (d₁:ℝ) - 1 := by
    have : (d₀:ℝ) < d₁ := by exact_mod_cast h
    linarith
  refine ⟨?_, ?_, velocidad_recorrido h₀, velocidad_recorrido (by omega)⟩
  · exact mul_lt_mul'' ed (longitudPaso_strictMono h₀ h) e0.le (longitudPaso_pos h₀).le
  · exact mul_lt_mul'' ed (tickDim_strictMono h₀ h) e0.le (tickDim_pos h₀).le

end CuantoDimensionalFisico

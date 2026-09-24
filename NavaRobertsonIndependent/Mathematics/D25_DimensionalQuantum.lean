import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant

/-!
# D25 — El cuanto es dimensional

La red espectral cuántica (`pathGraph d`, `T_d:P_d`, `H₂, H₃, H₄, …`) es la gráfica
de la cota de Robertson en todas las dimensiones: la gráfica de una obstrucción
algebraica. `d` es la dimensión de Hilbert, y cada `H_d` tiene su propio cuanto

`cuantoDim d = δ_geom(d) = C_Nava(d) − 1`.

Este módulo reúne, con un solo nombre, lo que la cadena ya demuestra:

* el cuanto es cero **exactamente** en las seeds `d = 2, 3` (saturación, `D20`);
* es estrictamente positivo desde `d = 4` (`D8`);
* crece estrictamente con `d` (`D9`), con piso `cuantoDim 4`;
* queda estrictamente bajo `δ_∞ = C_∞ − 1` y tiende a él (`D8`, `D9`): el infinito
  es un límite de la familia, no una dimensión, y tampoco anula el cuanto.

Sin unidades ni constantes físicas: es Capa 1. La lectura física (longitud, tiempo y
masa del cuanto en cada `H_d`) está en la Capa 2 (`Physics/PhysicalDimensionalQuantum`).

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace CuantoDimensional

open Gnomon Filter Topology

/-- El cuanto de `H_d`. -/
def cuantoDim (d : ℕ) : ℝ := geometricGap d

/-- El cuanto se anula exactamente en las seeds `d = 2, 3`. -/
theorem cuantoDim_eq_cero_iff {d : ℕ} (hd : 2 ≤ d) : cuantoDim d = 0 ↔ d = 2 ∨ d = 3 := by
  rw [← CoherenceConstant_eq_one_iff d hd]
  unfold cuantoDim geometricGap
  constructor <;> intro h <;> linarith

/-- **`d = 3` no tiene cuanto**: Robertson satura y no hay obstrucción. -/
theorem sin_cuanto_en_d3 : cuantoDim 3 = 0 :=
  (cuantoDim_eq_cero_iff (by norm_num)).mpr (Or.inr rfl)

theorem sin_cuanto_en_d2 : cuantoDim 2 = 0 :=
  (cuantoDim_eq_cero_iff (by norm_num)).mpr (Or.inl rfl)

/-- Desde `d = 4` el cuanto es estrictamente positivo. -/
theorem cuantoDim_pos {d : ℕ} (hd : 4 ≤ d) : 0 < cuantoDim d :=
  geometricGap_pos_of_four_le d hd

/-- El cuanto crece estrictamente con la dimensión. -/
theorem cuantoDim_strictMono {d₀ d₁ : ℕ} (h₀ : 4 ≤ d₀) (h : d₀ < d₁) :
    cuantoDim d₀ < cuantoDim d₁ :=
  geometricGap_strictMonoOn_ge_four (show 4 ≤ d₀ from h₀) (show 4 ≤ d₁ by omega) h

/-- Piso: el cuanto de `H_4` es el mínimo de toda dimensión abierta. -/
theorem cuantoDim_piso {d : ℕ} (hd : 4 ≤ d) : cuantoDim 4 ≤ cuantoDim d :=
  geometricGap_four_le d hd

/-- Techo: ninguna dimensión alcanza `δ_∞`. -/
theorem cuantoDim_techo {d : ℕ} (hd : 4 ≤ d) : cuantoDim d < deltaInf :=
  geometricGap_lt_deltaInf d hd

/-- Al infinito el cuanto tiende a `δ_∞ > 0`: no se cierra. -/
theorem cuantoDim_tendsto : Tendsto cuantoDim atTop (𝓝 deltaInf) :=
  limite_defect_geometrico

/-- **Certificado del cuanto dimensional**: cero solo en las seeds, positivo y
creciente desde `H_4`, acotado por `δ_∞ > 0` y convergente a él. -/
theorem cuanto_dimensional :
    cuantoDim 2 = 0 ∧ cuantoDim 3 = 0 ∧
    (∀ d, 4 ≤ d → 0 < cuantoDim d) ∧
    (∀ d, 4 ≤ d → cuantoDim 4 ≤ cuantoDim d) ∧
    (∀ d, 4 ≤ d → cuantoDim d < deltaInf) ∧
    0 < deltaInf ∧ Tendsto cuantoDim atTop (𝓝 deltaInf) :=
  ⟨sin_cuanto_en_d2, sin_cuanto_en_d3, fun _ => cuantoDim_pos, fun _ => cuantoDim_piso,
    fun _ => cuantoDim_techo, deltaInf_pos, cuantoDim_tendsto⟩

end CuantoDimensional

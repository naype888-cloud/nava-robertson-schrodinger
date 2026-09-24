import NavaRobertsonIndependent.Physics.MaximumSpeed

/-!
# Más celdas, más tiempo: la celda no se curva, se cuenta

La celda no se curva ni se estira: mide `L_sbpk` y cuesta `τ_sbpk`. Un recorrido de
`k` celdas mide `k·L_sbpk` (`distanciaRecorrida`) y, en el proceso maximal, dura
exactamente `k·τ_sbpk` (`maximal_duracion`). Aquí `k` es el **número de celdas del
recorrido**, no la dimensión: la dimensión `d` fija la celda (`H_4`: `L_sbpk`), y la
familia en `d` vive en `CuantoDimensionalFisico`.

Resultado: un recorrido de más celdas es más largo y tarda más, y ambos van
exactamente a `c`. El costo extra es número de celdas, no una celda distinta ni otra
velocidad.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace MasCeldasMasTiempo

open LimiteSubPlanckiano ColapsoSchwarzschild VelocidadMaximaRegistrable

/-- Más celdas, recorrido más largo. -/
theorem distancia_strictMono {k₀ k₁ : ℕ} (h : k₀ < k₁) :
    distanciaRecorrida k₀ < distanciaRecorrida k₁ := by
  unfold distanciaRecorrida
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h) Lsbpk_pos

/-- Más celdas, más tiempo: el proceso maximal dura exactamente `k·τ_sbpk`. -/
theorem duracionMaximal_strictMono {k₀ k₁ : ℕ} (h : k₀ < k₁) :
    (ProcesoTransporte.maximal k₀).duracion < (ProcesoTransporte.maximal k₁).duracion := by
  rw [ProcesoTransporte.maximal_duracion, ProcesoTransporte.maximal_duracion]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h) Tausbpk_pos

/-- **Cierre: más celdas cuesta más en longitud y en tiempo, a la misma `c`.** -/
theorem mas_celdas_mas_costoso_misma_velocidad {k₀ k₁ : ℕ} (h₀ : 1 ≤ k₀) (h : k₀ < k₁) :
    distanciaRecorrida k₀ < distanciaRecorrida k₁ ∧
      (ProcesoTransporte.maximal k₀).duracion < (ProcesoTransporte.maximal k₁).duracion ∧
      (ProcesoTransporte.maximal k₀).velocidadMedia = cSI ∧
      (ProcesoTransporte.maximal k₁).velocidadMedia = cSI :=
  ⟨distancia_strictMono h, duracionMaximal_strictMono h,
    ProcesoTransporte.maximal_alcanza_c h₀,
    ProcesoTransporte.maximal_alcanza_c (le_trans h₀ h.le)⟩

#print axioms mas_celdas_mas_costoso_misma_velocidad

end MasCeldasMasTiempo

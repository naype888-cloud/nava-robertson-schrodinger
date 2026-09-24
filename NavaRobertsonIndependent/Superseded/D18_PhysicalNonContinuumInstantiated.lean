import NavaRobertsonIndependent.Superseded.PhysicalNonContinuumPincerAsubDeltaInf
import NavaRobertsonIndependent.Physics.SubPlanckianLimit

/-!
# El continuo físico completado reduce a `False`

> **Superseded (reemplazado en v14)** por `Physics/PhysicalSupportR4`; ver la nota de la
> pinza. Se conserva compilando, fuera de las cuatro capas.

Instanciación cerrada de la pinza con las cantidades ya certificadas del
paquete: `Asbpk > 0` y `Gnomon.deltaInf > 0`. La conclusión se presenta con
codominio explícito `False`; en Lean, esto es definicionalmente lo mismo que
la negación del supuesto de continuo físico completado.
-/

noncomputable section

namespace NoContinuoFisicoInstanciado

open LimiteSubPlanckiano
open PinzaAsubDeltaInfNoContinuoFisico

/-- Marco concreto del paquete Nava–Robertson–Schrödinger. -/
def marcoNava : MarcoPinza where
  Asub := Asbpk
  deltaInf := Gnomon.deltaInf
  Asub_pos := Asbpk_pos
  deltaInf_pos := Gnomon.deltaInf_pos

/-- La hipótesis de continuo físico completado contradice simultáneamente la
frontera inferior positiva y el defect asintótico positivo. -/
theorem continuo_fisico_completado_implica_false
    (h : ContinuoCompletadoHabitaFisicamente marcoNava) : False := by
  exact no_continuo_fisico_por_pinza marcoNava h

/-- Forma lógica equivalente: el continuo físico completado no habita. -/
theorem continuo_fisico_completado_no_habita :
    ¬ ContinuoCompletadoHabitaFisicamente marcoNava :=
  continuo_fisico_completado_implica_false

/-- Certificado explícito que conserva las dos contradicciones independientes:
`Asbpk ≠ 0` y `deltaInf ≠ 0`. -/
theorem doble_cierre_concreto :
    ¬ DivisibilidadSinPiso marcoNava ∧
      ¬ DefectBorradoAlInfinito marcoNava ∧
      ¬ ContinuoCompletadoHabitaFisicamente marcoNava :=
  no_continuo_fisico_por_doble_cierre marcoNava

end NoContinuoFisicoInstanciado

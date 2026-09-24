import NavaRobertsonIndependent.Physics.SubPlanckianLimit
import NavaRobertsonIndependent.Physics.ElementalCellStep

/-!
# D27 — Deformación del tiempo y el espacio de registro

> **Superseded (v14).** Este módulo supone que la celda se estira con la materia
> (`HCurv`). El mecanismo vigente es el opuesto: la celda no se curva, la curvatura
> añade celdas (`Physics/D32_WhyTimeGrows`, `HCurvaturaConteo`). Además,
> `HCurv.densidad` no la usa ningún teorema. Se conserva compilando, fuera de las
> cuatro capas.

Puente número: la deformación de la red subplanckiana y su relación con la
cuántica. Todo teorema de este módulo se deduce del paquete; la única
hipótesis declarada es `HCurv` (acoplamiento materia ↔ estiramiento), y está
etiquetada como tal en su propia firma.

Estatus: **verificado** (sin `sorry`). Los teoremas dependen solo de los tres
axiomas estándar de Mathlib.
-/

noncomputable section

open LimiteSubPlanckiano ColapsoSchwarzschild PasoElementalCelda

namespace DeformacionTiempo

/-- `Lsbpk = cSI * Tausbpk`: la celda mínima se recorre en exactamente un
tick a la velocidad máxima registrada (demostrado desde
`paso_entre_tick_es_c`). -/
theorem lsbpk_eq_c_tau : Lsbpk = cSI * Tausbpk := by
  have h := paso_entre_tick_es_c
  rw [longitudPaso_cuatro] at h
  exact (div_eq_iff (ne_of_gt Tausbpk_pos)).mp h

/-- Celda estirada por el factor `s`. -/
noncomputable def LsbpkEstirado (s : ℝ) : ℝ := s * Lsbpk

/-- Tick estirado por el mismo factor `s`: tiempo y espacio se dilatan
conjuntamente. -/
noncomputable def TausbpkEstirado (s : ℝ) : ℝ := s * Tausbpk

/-- **Conservación de c bajo estiramiento** (teorema): si longitud y tick se
estiran por el mismo factor, su cociente —la velocidad máxima registrable— no
se altera. La deformación dilata el tiempo local sin tocar la cota de la
velocidad. -/
theorem c_conservada (s : ℝ) : LsbpkEstirado s = cSI * TausbpkEstirado s := by
  unfold LsbpkEstirado TausbpkEstirado
  rw [lsbpk_eq_c_tau]
  ring

/-- **Dilatación temporal** (teorema): todo estiramiento `s > 1` dilata
estrictamente el tick. El tiempo local es función creciente del
estiramiento de la red. -/
theorem dilatacion_temporal {s : ℝ} (hs : 1 < s) :
    Tausbpk < TausbpkEstirado s := by
  unfold TausbpkEstirado
  nlinarith [Tausbpk_pos]

/-- El tick estirado por `s ≥ 1` sigue siendo registrable: queda en o por
encima del piso temporal. -/
theorem tick_estirado_registrable {s : ℝ} (hs : 1 ≤ s) :
    TiempoRegistrable (TausbpkEstirado s) := by
  unfold TausbpkEstirado TiempoRegistrable
  nlinarith [Tausbpk_pos]

/-- **Amplitud común del defect** (teorema): la longitud y el tiempo mínimos
son el MISMO factor lineal `ySbpk = δ(4)·√Ω_b` aplicado a las unidades de
Planck de su dimensión. El tiempo está medido en el defect dimensional,
exactamente como la longitud: no hay unidad de tiempo en el marco que no
sea múltiplo del defect. -/
theorem ambos_pisos_comparten_amplitud :
    Lsbpk / longitudPlanckCODATA = Tausbpk / tiempoPlanckCODATA := by
  rw [Lsbpk, Tausbpk_eq_lsub_tiempoPlanck]
  field_simp [longitudPlanckCODATA_pos.ne', tiempoPlanckCODATA_pos.ne']

/-- La igualdad de amplitudes es invariante bajo estiramiento: ambos ratios
escalan con el mismo `s`. La deformación no rompe la identificación
tiempo = espacio = defect. -/
theorem amplitud_conservada_bajo_estiramiento (s : ℝ) :
    LsbpkEstirado s / longitudPlanckCODATA
      = TausbpkEstirado s / tiempoPlanckCODATA := by
  simp only [LsbpkEstirado, TausbpkEstirado, mul_div_assoc]
  rw [ambos_pisos_comparten_amplitud]

/-- **Confinación de régimen** (teorema): solo estiramientos `s ≤ 1` mantienen
el tick por debajo del tiempo de Planck. Un estiramiento `s > 1` escapa del
régimen subplanckiano: la deformación fuerte cambia de régimen, no solo de
escala. -/
theorem estirado_sigue_subplanckiano {s : ℝ} (hs : s ≤ 1) :
    TausbpkEstirado s < tiempoPlanckCODATA := by
  unfold TausbpkEstirado
  nlinarith [Tausbpk_pos, Tausbpk_lt_tiempoPlanckCODATA]

/-- **H-CURV (HIPÓTESIS DECLARADA, no teorema)**: la acumulación material con
densidad `ρ > 0` acopla con el factor de estiramiento `s > 1` de la celda.
Sin acumulación, `s = 1` (red sin deformar). Esta estructura es el precio de
entrada del puente materia ↔ geometría; todo lo demás en este módulo se
deduce de ella y del paquete. -/
structure HCurv where
  densidad : ℝ
  factor : ℝ
  densidad_pos : 0 < densidad
  estiramiento : 1 < factor

/-- Bajo H-CURV, el tiempo local está dilatado: la materia deforma el reloj
de la red (teorema condicional, deducido de la hipótesis y la dilatación
temporal pura). -/
theorem materia_dilata_el_tiempo (h : HCurv) :
    Tausbpk < TausbpkEstirado h.factor :=
  dilatacion_temporal h.estiramiento

/-- Y aun con materia acumulada, la velocidad máxima registrable sigue siendo
exactamente `c`: la deformación nunca permite superar la cota. El puente
materia → tiempo respeta la cota de la luz por construcción del par
espacio-tiempo, no por ajuste. -/
theorem c_conservada_con_materia (h : HCurv) :
    LsbpkEstirado h.factor = cSI * TausbpkEstirado h.factor :=
  c_conservada h.factor

/-- **El cuánto viaja con el estiramiento** (teorema): bajo H-CURV, la celda
deformada sigue siendo `ySbpk·s` veces la unidad de Planck — el defect
dimensional, no una escala externa, es lo que se transporta. -/
theorem cuanto_viaja_con_el_estiramiento (h : HCurv) :
    LsbpkEstirado h.factor / longitudPlanckCODATA
      = h.factor * (Lsbpk / longitudPlanckCODATA) := by
  unfold LsbpkEstirado
  rw [mul_div_assoc]

#print axioms lsbpk_eq_c_tau
#print axioms c_conservada
#print axioms dilatacion_temporal
#print axioms tick_estirado_registrable
#print axioms ambos_pisos_comparten_amplitud
#print axioms amplitud_conservada_bajo_estiramiento
#print axioms estirado_sigue_subplanckiano
#print axioms materia_dilata_el_tiempo
#print axioms c_conservada_con_materia
#print axioms cuanto_viaja_con_el_estiramiento

end DeformacionTiempo

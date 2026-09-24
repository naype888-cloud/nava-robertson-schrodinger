import NavaRobertsonIndependent.Mathematics.D13_FirstCombinatorialRupture
import NavaRobertsonIndependent.Ontology.D31_MeasurableExistenceBand
import NavaRobertsonIndependent.Ontology.D33_TorusPhaseThick

/-!
# D34 — Registro en un eón abierto

La cadena de la Capa 4, con contenido matemático en cada campo:

1. **D4 no saturado → fase toro.** La ruptura fuerza `4 ≤ d` (`D13`); en ese
   régimen el thick es el defect geométrico positivo de `D33`.
2. **Eón abierto → dinámica elemental con defect.** Es el postulado de esta
   capa, declarado en la firma: el camino del canal medido está en ruptura
   (`PrimeraRuptura.RupturaCamino d`, `D13`). De ahí sale `4 ≤ d`
   (`cuatro_le`): las cuatro dimensiones mínimas no se suponen, se derivan de
   la ruptura.
3. **El observador registra lo real.** Cada lectura es una `MedicionEspectral`
   (`D29`): un autovalor `2·cos θ` de `A_d`, probado en `D6`. Es un número
   real y estrictamente dentro de `(−2, 2)` (`lectura_real_acotada`), y el
   observador nunca es el canal medido (`observador_no_es_el_medido`).
4. **Agregar dimensiones no acerca a la perfección.** El defect registrado
   vive en la banda `δ_geom(4) ≤ δ_geom(d) < δ_geom(4) + Δ` (`D31`) y nunca es
   `0` (`nunca_perfeccion`). El defect no depende de las lecturas: lo fija la
   dinámica (`d`), no el observador.

`registro_satisfacible` construye un registro con lecturas espectrales
reales (no con campos `True`). `cierre_eon_abierto` incluye la identidad
thick-defect además de las consecuencias registrales.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib. Capa 4: el postulado es el campo `ruptura`, y la lectura
térmica del thick es la de `D33`.
-/

noncomputable section

namespace EonAbierto

open ObservadorMedicionEspectral FaseToroThick TransportePosicion

/-- **Registro en un eón abierto** (hipótesis de la Capa 4, con contenido).
`d` es el canal medido y `d'` el observador. -/
structure RegistroEonAbierto (d d' : ℕ) where
  /-- Fase del proceso (`D33`). -/
  fase : FaseThick
  /-- Postulado: el eón abierto exige dinámica elemental con defect, es decir,
  el camino del canal medido está en ruptura (`D13`). -/
  ruptura : PrimeraRuptura.RupturaCamino d
  /-- Thick/defect no nulo del proceso. En d≥4, `D33` identifica este dato
  con `δ_geom(d)`. -/
  sin_cero_absoluto : thickFase fase d ≠ 0
  /-- Número de ticks registrados. -/
  ticks : ℕ
  ticks_pos : 0 < ticks
  /-- En cada tick, una medición espectral real del canal `d` (`D29`). -/
  lectura : Fin ticks → MedicionEspectral d d'

namespace RegistroEonAbierto

variable {d d' : ℕ}

theorem dos_le (R : RegistroEonAbierto d d') : 2 ≤ d :=
  (R.lectura ⟨0, R.ticks_pos⟩).hd

/-- Las cuatro dimensiones mínimas se derivan de la ruptura (`D13`). -/
theorem cuatro_le (R : RegistroEonAbierto d d') : 4 ≤ d :=
  (PrimeraRuptura.ruptura_camino_iff_cuatro_le d R.dos_le).1 R.ruptura

/-- El thick no nulo de un registro en ruptura fuerza la fase toro. -/
theorem fase_es_toro (R : RegistroEonAbierto d d') : R.fase = .toro :=
  sin_cero_absoluto_implica_toro R.sin_cero_absoluto

/-- En un registro, thick y defect geométrico son el mismo dato. -/
theorem thick_es_defect (R : RegistroEonAbierto d d') :
    thickFase R.fase d = ENNReal.ofReal (Gnomon.geometricGap d) := by
  rw [R.fase_es_toro]
  rfl

/-- El observador nunca es el canal medido (`D29`). -/
theorem observador_no_es_el_medido (R : RegistroEonAbierto d d') (t : Fin R.ticks) :
    d' ≠ d :=
  (R.lectura t).distinto_del_medido

/-- Todo lo registrado es un autovalor real `2·cos θ` de `A_d`, estrictamente
dentro de `(−2, 2)`: lo medido es real y nunca toca los extremos. -/
theorem lectura_real_acotada (R : RegistroEonAbierto d d') (t : Fin R.ticks) :
    -2 < 2 * Real.cos (R.lectura t).valorReal ∧ 2 * Real.cos (R.lectura t).valorReal < 2 := by
  have hd := R.dos_le
  rw [(R.lectura t).valorReal_eq_angulo]
  have habs := abs_cos_anguloModo_le_cos_fiedler hd (R.lectura t).resultado
  have hF : Real.cos (anguloFiedler d) < 1 := by
    have h0 : (0 : ℝ) < anguloFiedler d := by unfold anguloFiedler; positivity
    have hpi : anguloFiedler d ≤ Real.pi := by
      unfold anguloFiedler
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hpi h0
  constructor <;> linarith [abs_le.mp (habs.trans hF.le), (abs_lt.mp (lt_of_le_of_lt habs hF))]

/-- El defect registrado vive en la banda de `D31`. -/
theorem defect_en_banda (R : RegistroEonAbierto d d') :
    Gnomon.geometricGap 4 ≤ Gnomon.geometricGap d
      ∧ Gnomon.geometricGap d - Gnomon.geometricGap 4 < GapCuatroAsintota.gapCuatroInf
      ∧ 0 < Gnomon.geometricGap 4 :=
  BandaExistenciaMedible.banda_del_defect d R.cuatro_le

/-- Nunca perfección: el defect de un registro en eón abierto es positivo. -/
theorem nunca_perfeccion (R : RegistroEonAbierto d d') : 0 < Gnomon.geometricGap d :=
  Gnomon.geometricGap_pos_of_four_le d R.cuatro_le

/-- **La hipótesis es satisfacible con contenido**: un registro de un tick,
en fase toro, sobre el canal `4` con observador `5`, cuya lectura es una
medición espectral real de `A_4`. -/
theorem registro_satisfacible : Nonempty (RegistroEonAbierto 4 5) :=
  ⟨{ fase := .toro
     ruptura := PrimeraRuptura.ruptura_camino_cuatro
     sin_cero_absoluto := thick_toro_no_cero 4 (by norm_num)
     ticks := 1
     ticks_pos := Nat.one_pos
     lectura := fun _ =>
       (medicionEspectral_canonica 4 5 (by norm_num) (by norm_num) (by norm_num) 0).some }⟩

/-- **Cierre del eón abierto**: todo registro ocurre en el toro, sobre al menos
cuatro dimensiones, con lecturas reales en `(−2, 2)`, y con defect en la banda
`[δ_geom(4), δ_geom(4) + Δ)`, nunca `0`. -/
theorem cierre_eon_abierto (R : RegistroEonAbierto d d') :
    R.fase = .toro ∧ 4 ≤ d
      ∧ thickFase R.fase d = ENNReal.ofReal (Gnomon.geometricGap d)
      ∧ (∀ t, -2 < 2 * Real.cos (R.lectura t).valorReal
              ∧ 2 * Real.cos (R.lectura t).valorReal < 2)
      ∧ Gnomon.geometricGap 4 ≤ Gnomon.geometricGap d
      ∧ Gnomon.geometricGap d - Gnomon.geometricGap 4 < GapCuatroAsintota.gapCuatroInf
      ∧ 0 < Gnomon.geometricGap d :=
  ⟨R.fase_es_toro, R.cuatro_le, R.thick_es_defect, R.lectura_real_acotada,
    (R.defect_en_banda).1, (R.defect_en_banda).2.1, R.nunca_perfeccion⟩

end RegistroEonAbierto

end EonAbierto

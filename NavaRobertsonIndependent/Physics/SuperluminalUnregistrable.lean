import NavaRobertsonIndependent.Physics.PhysicalSupportR4
import NavaRobertsonIndependent.Physics.MaximumSpeed

/-!
# Lo superluminal existe en ℝ, pero no se registra

Principio de instanciación (`PhysicalSupportR4`): el ℝ de Cantor es matemática
demostrada y se usa, pero no se importa entero al mundo físico. Este archivo pone la
frontera para la velocidad.

* **En ℝ existe.** A velocidad `v > c`, cruzar la celda tarda
  `tiempoCruce v = L_sbpk / v`, un número real estrictamente entre `0` y `τ_sbpk`
  (`tiempoCruce_en_hueco`). A `n·c` es exactamente `τ_sbpk / n`
  (`tiempoCruce_n_veces_c`). Cuando `v → ∞`, `tiempoCruce v → 0` en ℝ
  (`tiempoCruce_tendsto_cero`).
* **En el mundo físico no.** Ese número no es ningún tiempo registrado
  (`superluminal_no_registrado`) ni la duración de ningún paso admisible de ningún
  soporte (`superluminal_no_es_paso`): todo paso cuesta al menos un tick. Todo el
  tramo `v > c`, incluido el límite `v → ∞`, cae en el hueco `(0, τ_sbpk)`.

La frontera no la pone un observador: `τ_sbpk` es el defect de `H₄`
(`FlechaDelTiempo.tick_es_defect`).

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace SuperluminalNoRegistrable

open Filter Topology
open LimiteSubPlanckiano CierreRegistroTiempoEnergiaSbpk VelocidadMaximaRegistrable
  SoporteFisicoR4

/-- Tiempo para cruzar una celda a velocidad `v` (un número de ℝ). -/
def tiempoCruce (v : ℝ) : ℝ := Lsbpk / v

/-- A velocidad `c` el cruce dura exactamente un tick. -/
theorem tiempoCruce_c : tiempoCruce velocidadMaximaRegistrada = Tausbpk := rfl

/-- **En ℝ existe**: por encima de `c`, el cruce cae en el hueco `(0, τ_sbpk)`. -/
theorem tiempoCruce_en_hueco {v : ℝ} (hv : velocidadMaximaRegistrada < v) :
    tiempoCruce v ∈ Set.Ioo 0 Tausbpk := by
  have hc := velocidadMaximaRegistrada_pos
  have hv0 : 0 < v := hc.trans hv
  exact ⟨div_pos Lsbpk_pos hv0, div_lt_div_of_pos_left Lsbpk_pos hc hv⟩

/-- A `n·c`, el cruce dura `τ_sbpk / n`. -/
theorem tiempoCruce_n_veces_c (n : ℝ) (hn : 0 < n) :
    tiempoCruce (n * velocidadMaximaRegistrada) = Tausbpk / n := by
  unfold tiempoCruce Tausbpk
  have := velocidadMaximaRegistrada_pos
  field_simp

/-- En ℝ, el cruce tiende a `0` cuando `v → ∞`. -/
theorem tiempoCruce_tendsto_cero : Tendsto tiempoCruce atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

/-- **Frontera 1**: el cruce superluminal no es ningún tiempo registrado. -/
theorem superluminal_no_registrado {v : ℝ} (hv : velocidadMaximaRegistrada < v) :
    tiempoCruce v ∉ tiemposRegistrados := by
  rintro ⟨n, hn⟩
  exact nada_bajo_el_tick n (hn ▸ tiempoCruce_en_hueco hv)

/-- **Frontera 2**: ningún paso admisible de ningún soporte dura eso. -/
theorem superluminal_no_es_paso {v : ℝ} (hv : velocidadMaximaRegistrada < v)
    {k : ℕ} (P : ProcesoTransporte k) (i : Fin k) :
    P.tau i ≠ tiempoCruce v := by
  intro h
  have h1 := P.paso_dura_un_tick i
  have h2 := (tiempoCruce_en_hueco hv).2
  linarith

/-- **Cierre**: todo el tramo superluminal existe en ℝ y ninguno de sus tiempos se
registra; eventualmente (`v → ∞`) queda tan cerca de `0` como se quiera, sin tocarlo
y sin salir del hueco. -/
theorem superluminal_en_R_no_en_fisica {v : ℝ} (hv : velocidadMaximaRegistrada < v) :
    tiempoCruce v ∈ Set.Ioo 0 Tausbpk ∧ tiempoCruce v ∉ tiemposRegistrados :=
  ⟨tiempoCruce_en_hueco hv, superluminal_no_registrado hv⟩

#print axioms superluminal_en_R_no_en_fisica
#print axioms superluminal_no_es_paso

end SuperluminalNoRegistrable

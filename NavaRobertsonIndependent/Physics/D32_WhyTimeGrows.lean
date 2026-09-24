import NavaRobertsonIndependent.Physics.MoreCellsMoreTime

/-!
# D32 — Por qué crece el tiempo donde se curva el espacio

Mecanismo:

1. **La celda no se curva.** Mide `L_sbpk` y cuesta `τ_sbpk`, siempre.
2. **La curvatura añade celdas.** Entre los mismos extremos, el que va recto recorre
   `k₀` celdas y el que va por la curva `k₁ > k₀`. Esta es la hipótesis física
   declarada, `HCurvaturaConteo`, y se usa en cada teorema.
3. **Las celdas son la medida del tiempo.** Cada celda cuesta al menos un tick
   (`k_pasos_cuestan_k_ticks`); más celdas es más conteo de `τ_sbpk`.

Resultados:

* `curva_tarda_mas`: **todo** proceso admisible por la curva tarda estrictamente más
  que el recto a velocidad máxima; no solo el proceso maximal.
* `cuanto_tarda`: a velocidad máxima, el cociente de tiempos es exactamente
  `k₁/k₀`, un racional de enteros, y ambos van a `c`.

No se deriva la gravedad ni las ecuaciones de Einstein: se demuestra, dada la
hipótesis de conteo, por qué y cuánto crece el tiempo.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace PorQueCreceElTiempo

open LimiteSubPlanckiano ColapsoSchwarzschild VelocidadMaximaRegistrable

/-- **H-CURVATURA-CONTEO (hipótesis declarada).** La curvatura añade celdas: el
recorrido curvo tiene más celdas que el recto. Las celdas no cambian. -/
structure HCurvaturaConteo where
  kRecto : ℕ
  kCurvo : ℕ
  recto_pos : 1 ≤ kRecto
  curvatura_anade_celdas : kRecto < kCurvo

/-- La hipótesis es satisfacible. -/
theorem hCurvaturaConteo_satisfacible : Nonempty HCurvaturaConteo :=
  ⟨⟨1, 2, le_rfl, by norm_num⟩⟩

/-- **El que va por la curva tarda más**, cualquiera que sea el proceso admisible
por la curva. -/
theorem curva_tarda_mas (H : HCurvaturaConteo) (P : ProcesoTransporte H.kCurvo) :
    (ProcesoTransporte.maximal H.kRecto).duracion < P.duracion := by
  rw [ProcesoTransporte.maximal_duracion]
  have hk : (H.kRecto : ℝ) < H.kCurvo := by exact_mod_cast H.curvatura_anade_celdas
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hk Tausbpk_pos) P.k_pasos_cuestan_k_ticks

/-- **Cuánto**: el cociente de tiempos maximales es el cociente de celdas. -/
theorem tiempo_proporcional_al_conteo (k₀ k₁ : ℕ) (hk₀ : 1 ≤ k₀) :
    (ProcesoTransporte.maximal k₁).duracion / (ProcesoTransporte.maximal k₀).duracion =
      (k₁ : ℝ) / k₀ := by
  rw [ProcesoTransporte.maximal_duracion, ProcesoTransporte.maximal_duracion]
  have hk : (k₀ : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk₀)
  field_simp [hk, Tausbpk_pos.ne']

/-- **Tesis principal.** Bajo `HCurvaturaConteo`: la curva tarda más que el recto (en
todo proceso admisible), el cociente de tiempos es `k₁/k₀`, y ambos van a `c`. -/
theorem por_que_crece_el_tiempo (H : HCurvaturaConteo) :
    (∀ P : ProcesoTransporte H.kCurvo,
        (ProcesoTransporte.maximal H.kRecto).duracion < P.duracion) ∧
    (ProcesoTransporte.maximal H.kCurvo).duracion /
        (ProcesoTransporte.maximal H.kRecto).duracion = (H.kCurvo : ℝ) / H.kRecto ∧
    (ProcesoTransporte.maximal H.kRecto).velocidadMedia = cSI ∧
    (ProcesoTransporte.maximal H.kCurvo).velocidadMedia = cSI :=
  ⟨curva_tarda_mas H, tiempo_proporcional_al_conteo _ _ H.recto_pos,
    ProcesoTransporte.maximal_alcanza_c H.recto_pos,
    ProcesoTransporte.maximal_alcanza_c (le_trans H.recto_pos H.curvatura_anade_celdas.le)⟩

#print axioms curva_tarda_mas
#print axioms por_que_crece_el_tiempo

end PorQueCreceElTiempo

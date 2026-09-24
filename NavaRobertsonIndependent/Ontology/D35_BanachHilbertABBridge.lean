import Mathlib.Analysis.InnerProductSpace.l2Space
import NavaRobertsonIndependent.Mathematics.D13_FirstCombinatorialRupture
import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality
import NavaRobertsonIndependent.Ontology.D34_OpenEonRegistration

/-!
# D35 — De la separación Banach `q` a la germinación A–B en Hilbert

Este módulo hace explícita la interpretación del hilo:

* El dato relacional es `q(A,B)`, la distancia inducida por la norma. La ley
  relacional se expresa como una respuesta que factoriza por `q`; igualdad de
  separaciones da igualdad de lecturas. Esto declara con precisión la regla
  importada por el modelo; no atribuye esa regla a todo espacio de Banach.
* Un espacio de Hilbert completo satisface las hipótesis de espacio de Banach.
  El modelo espacial usa `H3 = ℝ³`; al registrar la separación `q(A,B)` se
  añade una coordenada relacional y se representa el estado en `H4 = ℝ⁴`.
* D13 demuestra que la ruptura empieza exactamente en `d = 4`. El modelo
  activa la fase toro a partir de esa ruptura; D33 identifica el thick con el
  mismo defect geométrico `δ_geom`.
* Dos eones seed son objetos completos con conjuntos finitos y discretos de
  ticks. Una población puede tener cualquier tipo de cardinalidad con al menos
  dos miembros, incluidas poblaciones infinitas; cada eón sigue siendo finito.

* Generalización `H(3+1+k) = EuclideanSpace ℝ (Fin (3+1+k))`: largo, alto,
  ancho, `q(A,B)` y `k` observables independientes más (temperaturas, dureza,
  peso específico, …); `H4` es `k = 0`. Para todo `k` hay ruptura y fase toro.
* Ruta térmica (`sin_cero_absoluto_abre_ruptura`): thick `≠ 0` fuerza toro y
  `d ≥ 4`, porque en `d = 2, 3` se tiene `C_Nava = 1`, `δ_geom = 0` (`D20`,
  `D21`); de ahí la ruptura de `T_d:P_d` (`D13`).
* `distincion_cancela_cero_e_infinito`: en `H3` sin distinción el cero absoluto
  es admisible (seed, thick `0`, sin ruptura); al distinguir B de A, para
  todo `k` el thick en `d = 3+1+k` es `δ_geom(d)`, positivo, finito y en la
  banda de `D31`.

La regla “la relación depende sólo de q” y la coordenada relacional adicional
son parte explícita del modelo. La prueba de dimensión usa el espacio
euclidiano finito que las representa; D13 aporta el resultado espectral para
el path graph del mismo parámetro `d`.
-/

noncomputable section

open scoped NNReal ENNReal lp

namespace PuenteBanachHilbertAB

/-! ## Ley relacional basada en distancia -/

/-- Separación `q` en un espacio métrico normado. -/
def q {E : Type*} [PseudoMetricSpace E] (a b : E) : ℝ := dist a b

/-- Lectura relacional cuyo único argumento geométrico es `q`. -/
def lecturaPorQ {E : Type*} [PseudoMetricSpace E]
    (respuesta : ℝ → ℝ) (a b : E) : ℝ := respuesta (q a b)

/-- La lectura factoriza por `q`: dos pares con la misma separación dan la
misma lectura. -/
theorem lectura_depende_solo_de_q {E : Type*} [PseudoMetricSpace E]
    (respuesta : ℝ → ℝ) (a b c d : E) (h : q a b = q c d) :
    lecturaPorQ respuesta a b = lecturaPorQ respuesta c d := by
  simp [lecturaPorQ, h]

/-- Instancia del argumento en cualquier espacio de Banach real: la distancia
es la inducida por la norma y la lectura sólo usa esa distancia. -/
theorem lectura_Banach_depende_de_q {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (respuesta : ℝ → ℝ) (a b c d : E) (h : q a b = q c d) :
    lecturaPorQ respuesta a b = lecturaPorQ respuesta c d :=
  lectura_depende_solo_de_q respuesta a b c d h

/-- Especialización directa del mismo argumento a Hilbert: la hipótesis de
completitud hace que la norma del producto interno sea una norma de Banach. -/
theorem lectura_Hilbert_depende_de_q {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (respuesta : ℝ → ℝ) (a b c d : E) (h : q a b = q c d) :
    lecturaPorQ respuesta a b = lecturaPorQ respuesta c d :=
  lectura_Banach_depende_de_q respuesta a b c d h

/-- En un espacio normado, `q` es la norma de la diferencia. -/
theorem q_eq_norm_sub {E : Type*} [NormedAddCommGroup E] (a b : E) :
    q a b = ‖b - a‖ := by
  simp [q, dist_eq_norm_sub']

/-! ## Seeds y eones finitos completos -/

abbrev Hilbert3 := EuclideanSpace ℝ (Fin 3)
abbrev Hilbert4 := EuclideanSpace ℝ (Fin 4)

/-- Una seed sitúa su presupuesto y sus tres fermiones fundamentales en un
mismo punto de `H3`. Los indicadores de proceso seed son cero. -/
structure Seed where
  id : ℕ
  puntoHilbert : Hilbert3
  presupuestoCosmologico : ℝ
  puntoPresupuesto : Hilbert3
  presupuesto_en_punto : puntoPresupuesto = puntoHilbert
  puntoFermion : Fin 3 → Hilbert3
  fermiones_en_punto : ∀ i, puntoFermion i = puntoHilbert

def seedTime (_ : Seed) : ℝ := 0
def seedTransport (_ : Seed) : ℝ := 0
def seedTemperature (_ : Seed) : ℝ := 0
def defectSeed (_ : Seed) : ℝ := 0

theorem indicadores_seed_cero (S : Seed) :
    seedTime S = 0 ∧ seedTransport S = 0 ∧
      seedTemperature S = 0 ∧ defectSeed S = 0 := by
  simp [seedTime, seedTransport, seedTemperature, defectSeed]

/-- Un eón germinado es completo y finito: su tiempo está indexado por todos
los `Fin numeroTicks`, sin intervalo continuo ni subeón fraccionario. -/
structure EonFinitoCompleto where
  id : ℕ
  numeroTicks : ℕ
  ticks_positivos : 0 < numeroTicks

abbrev EonFinitoCompleto.ticks (e : EonFinitoCompleto) := Fin e.numeroTicks

theorem EonFinitoCompleto.ticks_finitos (e : EonFinitoCompleto) :
    Finite e.ticks := by
  infer_instance

theorem EonFinitoCompleto.card_ticks (e : EonFinitoCompleto) :
    Fintype.card e.ticks = e.numeroTicks := by
  simp [EonFinitoCompleto.ticks]

/-- Dos seeds distinguibles, cada una con su eón finito completo. -/
structure SeedGermination where
  A : Seed
  B : Seed
  seeds_distintas : A.id ≠ B.id
  centros_distintos : A.puntoHilbert ≠ B.puntoHilbert
  eonA : EonFinitoCompleto
  eonB : EonFinitoCompleto
  eones_distintos : eonA.id ≠ eonB.id

/-- Distancia `q` entre las seeds A y B en el Hilbert espacial `H3`. -/
def qAB (P : SeedGermination) : ℝ := q P.A.puntoHilbert P.B.puntoHilbert

theorem qAB_positivo (P : SeedGermination) : 0 < qAB P := by
  exact dist_pos.mpr P.centros_distintos

/-- Estado relacional: conserva las tres coordenadas de A y añade `q(A,B)`
como cuarta coordenada Hilbert. -/
def estadoRelacionalAB (P : SeedGermination) : Hilbert4 :=
  WithLp.toLp 2 (fun i : Fin 4 =>
    if h : i.val < 3 then P.A.puntoHilbert ⟨i.val, h⟩ else qAB P)

theorem coordenada_relacional_es_q (P : SeedGermination) :
    estadoRelacionalAB P ⟨3, by omega⟩ = qAB P := by
  simp [estadoRelacionalAB]

theorem finrank_H3 : Module.finrank ℝ Hilbert3 = 3 := by
  simp [Hilbert3]

theorem finrank_H4 : Module.finrank ℝ Hilbert4 = 4 := by
  simp [Hilbert4]

/-- A sola ocupa el espacio espacial H3. -/
theorem dimension_seed_A : Module.finrank ℝ Hilbert3 = 3 := finrank_H3

/-- La relación medida A–B se representa en H4: tres ejes y la coordenada q. -/
theorem dimension_relacion_AB : Module.finrank ℝ Hilbert4 = 4 := finrank_H4

/-- La nueva distinción añade exactamente un grado relacional: 3 + 1 = 4. -/
theorem H3_mas_distincion_es_H4 :
    Module.finrank ℝ Hilbert3 + 1 = Module.finrank ℝ Hilbert4 := by
  rw [finrank_H3, finrank_H4]

/-! ## D4, ruptura y activación de la fase toro -/

noncomputable def faseDesdeRuptura (d : ℕ) : FaseToroThick.FaseThick := by
  classical
  exact if PrimeraRuptura.RupturaCamino d then .toro else .seed

theorem seed_H3_sin_ruptura :
    faseDesdeRuptura (Module.finrank ℝ Hilbert3) = .seed := by
  have hnot : ¬ PrimeraRuptura.RupturaCamino 3 := by
    intro h
    have h4 := (PrimeraRuptura.ruptura_camino_iff_cuatro_le 3 (by norm_num)).mp h
    omega
  simp [faseDesdeRuptura, hnot]

theorem H4_primera_ruptura : PrimeraRuptura.EsPrimeraRuptura 4 := by
  exact (PrimeraRuptura.primera_ruptura_iff_dimension_cuatro 4).2 rfl

theorem H4_no_satura : PrimeraRuptura.RupturaCamino 4 :=
  PrimeraRuptura.ruptura_camino_cuatro

theorem llega_B_activa_toro (P : SeedGermination) :
    faseDesdeRuptura (Module.finrank ℝ Hilbert4) = .toro ∧
      0 < qAB P ∧
      estadoRelacionalAB P ⟨3, by omega⟩ = qAB P := by
  refine ⟨?_, qAB_positivo P, coordenada_relacional_es_q P⟩
  simp [faseDesdeRuptura, H4_no_satura]

theorem thick_toro_es_defect_H4 :
    FaseToroThick.thickFase .toro 4 =
      ENNReal.ofReal (Gnomon.geometricGap 4) := rfl

theorem thick_positivo_al_germinar :
    0 < FaseToroThick.thickFase .toro 4 :=
  FaseToroThick.thick_toro_positivo 4 (by norm_num)

/-- Un par A–B junto con su coordenada `q` y el registro espectral que activa. -/
structure RegistroAB (P : SeedGermination) where
  q : ℝ
  q_correcto : q = qAB P
  q_positivo : 0 < q
  estado : Hilbert4
  coordenada_q : estado ⟨3, by omega⟩ = q
  dimension_Hilbert : ℕ
  dimension_correcta : dimension_Hilbert = Module.finrank ℝ Hilbert4
  ruptura_pathGraph : PrimeraRuptura.RupturaCamino (Module.finrank ℝ Hilbert4)
  registro : EonAbierto.RegistroEonAbierto 4 5
  fase_registro : registro.fase = FaseToroThick.FaseThick.toro
  fase_generada_por_ruptura :
    faseDesdeRuptura (Module.finrank ℝ Hilbert4) = registro.fase
  thick_es_defect : FaseToroThick.thickFase registro.fase 4 =
    ENNReal.ofReal (Gnomon.geometricGap 4)

/-- Construcción explícita del registro interno generado por cada relación A–B. -/
def registroGerminado (P : SeedGermination) : RegistroAB P where
  q := qAB P
  q_correcto := rfl
  q_positivo := qAB_positivo P
  estado := estadoRelacionalAB P
  coordenada_q := coordenada_relacional_es_q P
  dimension_Hilbert := 4
  dimension_correcta := by simp
  ruptura_pathGraph := by simpa [finrank_H4] using H4_no_satura
  registro := {
    fase := .toro
    ruptura := PrimeraRuptura.ruptura_camino_cuatro
    sin_cero_absoluto := FaseToroThick.thick_toro_no_cero 4 (by norm_num)
    ticks := 1
    ticks_pos := Nat.one_pos
    lectura := fun _ =>
      (ObservadorMedicionEspectral.medicionEspectral_canonica
        4 5 (by norm_num) (by norm_num) (by norm_num) 0).some
  }
  fase_registro := rfl
  fase_generada_por_ruptura := (llega_B_activa_toro P).1
  thick_es_defect := by
    exact EonAbierto.RegistroEonAbierto.thick_es_defect _

theorem registroGerminado_en_toro (P : SeedGermination) :
    (registroGerminado P).registro.fase = .toro :=
  (registroGerminado P).fase_registro

theorem registroGerminado_thick_defect (P : SeedGermination) :
    FaseToroThick.thickFase (registroGerminado P).registro.fase 4 =
      ENNReal.ofReal (Gnomon.geometricGap 4) := by
  exact EonAbierto.RegistroEonAbierto.thick_es_defect
    (registroGerminado P).registro

/-- Registradores internos discretos preservan H4 en todos los ticks naturales.
Cada registro local es finito; la sucesión de registros no introduce un
continuo temporal. -/
def registradoresInternos (_P : SeedGermination) :
    ℕ → RegistroAB _P :=
  fun _ => registroGerminado _P

theorem dimension4_permanente (P : SeedGermination) (n : ℕ) :
    (registradoresInternos P n).dimension_Hilbert = 4 := by
  rw [(registradoresInternos P n).dimension_correcta]
  exact finrank_H4

theorem todo_registro_interno_en_toro (P : SeedGermination) (n : ℕ) :
    (registradoresInternos P n).registro.fase = .toro ∧
      PrimeraRuptura.RupturaCamino (Module.finrank ℝ Hilbert4) := by
  exact ⟨(registradoresInternos P n).fase_registro,
    (registradoresInternos P n).ruptura_pathGraph⟩

/-! ## Una población admite dos o infinitos eones completos -/

/-- Población discreta de eones completos. El índice de eones es un tipo, no
un número real; la población contiene al menos A y B, y cada eón tiene una
cantidad positiva y finita de ticks. -/
structure PoblacionEones where
  Eon : Type
  A : Eon
  B : Eon
  distintos : A ≠ B
  numeroTicks : Eon → ℕ
  ticks_positivos : ∀ e, 0 < numeroTicks e

abbrev PoblacionEones.ticks (P : PoblacionEones) (e : P.Eon) :=
  Fin (P.numeroTicks e)

theorem PoblacionEones.eon_finito (P : PoblacionEones) (e : P.Eon) :
    Finite (P.ticks e) := by
  infer_instance

/-- Poblaciones finitas: cualquier entero `n ≥ 2` es representable. -/
def poblacionFinita (n : ℕ) (hn : 2 ≤ n) : PoblacionEones where
  Eon := Fin n
  A := ⟨0, by omega⟩
  B := ⟨1, by omega⟩
  distintos := by
    intro h
    have hv : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
    omega
  numeroTicks := fun _ => 1
  ticks_positivos := by intro e; norm_num

/-- También es admisible una familia infinita de eones, cada uno individualmente
finito; `Nat` indexa la sucesión discreta de eones. -/
def poblacionInfinita : PoblacionEones where
  Eon := ℕ
  A := 0
  B := 1
  distintos := by norm_num
  numeroTicks := fun _ => 1
  ticks_positivos := by intro e; norm_num

theorem hay_poblacion_infinita : Infinite poblacionInfinita.Eon := by
  change Infinite ℕ
  infer_instance

/-- Hilbert global `ℓ²(ℕ)` aloja una familia infinita de marcadores de eón
ortonormales; el PathGraph H3/H4 anterior describe la dinámica local A–B. -/
abbrev HilbertEonHost := lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞)

def marcadorEon (n : ℕ) : HilbertEonHost :=
  lp.single (2 : ℝ≥0∞) n (1 : ℝ)

theorem marcadorEon_injective : Function.Injective marcadorEon := by
  intro i j hij
  by_contra hne
  have hval := congrArg (fun v : HilbertEonHost => v i) hij
  have hi : marcadorEon i i = 1 := by
    simp [marcadorEon]
  have hj : marcadorEon j i = 0 := by
    simp [marcadorEon, hne]
  rw [hi, hj] at hval
  norm_num at hval

theorem HilbertEonHost_infinito : Infinite HilbertEonHost :=
  Infinite.of_injective marcadorEon marcadorEon_injective

theorem eones_infinito_embebidos :
    ∃ f : poblacionInfinita.Eon → HilbertEonHost, Function.Injective f :=
  ⟨marcadorEon, marcadorEon_injective⟩

/-- El índice por `Fin` enumera ticks completos: no hay una fracción de tick ni
una fracción de eón en la representación. -/
theorem eon_ticks_completos (P : PoblacionEones) (e : P.Eon) :
    Fintype.card (P.ticks e) = P.numeroTicks e := by
  simp [PoblacionEones.ticks]

/-! ## Generalización `H(3+1+k)`: tres ejes, `q` y `k` observables -/

/-- Hilbert relacional: largo, alto, ancho, la separación `q(A,B)` y `k`
observables independientes más (temperaturas, dureza, peso específico, …).
`H4` es el caso `k = 0`. -/
abbrev HilbertRel (k : ℕ) := EuclideanSpace ℝ (Fin (3 + 1 + k))

theorem HilbertRel_cero_es_H4 : HilbertRel 0 = Hilbert4 := rfl

theorem finrank_HilbertRel (k : ℕ) :
    Module.finrank ℝ (HilbertRel k) = 3 + 1 + k := by
  simp [HilbertRel]

theorem cuatro_le_finrank_HilbertRel (k : ℕ) :
    4 ≤ Module.finrank ℝ (HilbertRel k) := by
  rw [finrank_HilbertRel]
  omega

/-- Estado relacional general: coordenadas `0,1,2` de A, coordenada `3` igual a
`q(A,B)` y coordenadas `4, …, 3+k` iguales a los observables. -/
def estadoRelacionalGen (P : SeedGermination) (k : ℕ) (obs : Fin k → ℝ) :
    HilbertRel k :=
  WithLp.toLp 2 (fun i : Fin (3 + 1 + k) =>
    if h : i.val < 3 then P.A.puntoHilbert ⟨i.val, h⟩
    else if h' : i.val = 3 then qAB P
    else obs ⟨i.val - 4, by have := i.isLt; omega⟩)

theorem coordenada_q_gen (P : SeedGermination) (k : ℕ) (obs : Fin k → ℝ) :
    estadoRelacionalGen P k obs ⟨3, by omega⟩ = qAB P := by
  simp [estadoRelacionalGen]

theorem coordenada_observable (P : SeedGermination) (k : ℕ) (obs : Fin k → ℝ)
    (j : Fin k) :
    estadoRelacionalGen P k obs ⟨4 + j.val, by have := j.isLt; omega⟩ = obs j := by
  simp [estadoRelacionalGen, show ¬ (4 + (j : ℕ) < 3) by omega,
    show 4 + (j : ℕ) ≠ 3 by omega]

theorem estadoRelacionalGen_cero (P : SeedGermination) (obs : Fin 0 → ℝ) :
    estadoRelacionalGen P 0 obs = estadoRelacionalAB P := by
  ext i
  fin_cases i <;> simp [estadoRelacionalGen, estadoRelacionalAB]

theorem ruptura_HilbertRel (k : ℕ) :
    PrimeraRuptura.RupturaCamino (Module.finrank ℝ (HilbertRel k)) :=
  (PrimeraRuptura.ruptura_camino_iff_cuatro_le _
    (by have := cuatro_le_finrank_HilbertRel k; omega)).2
    (cuatro_le_finrank_HilbertRel k)

theorem toro_HilbertRel (k : ℕ) :
    faseDesdeRuptura (Module.finrank ℝ (HilbertRel k)) = .toro := by
  unfold faseDesdeRuptura
  exact if_pos (ruptura_HilbertRel k)

/-! ## Ruta térmica: sin cero absoluto hay ruptura -/

/-- Si el thick del toro no es `0`, el canal está en `d ≥ 4`: en `d = 2, 3`
se tiene `C_Nava = 1` (`D20`), es decir `δ_geom = 0` (`D21`). -/
theorem cuatro_le_de_sin_cero_absoluto {d : ℕ} (hd : 2 ≤ d)
    (h : FaseToroThick.thickFase .toro d ≠ 0) : 4 ≤ d := by
  by_contra hlt
  have hC := (Gnomon.CoherenceConstant_eq_one_iff d hd).2 (by omega)
  rw [Gnomon.CoherenceConstant_eq_one_add_geometricGap] at hC
  have hδ : Gnomon.geometricGap d = 0 := by linarith
  exact h (by simp [FaseToroThick.thickFase, hδ])

/-- Sin cero absoluto hay movimiento: la fase es toro, `d ≥ 4` y el camino
`T_d:P_d` está en ruptura (`D33` + `D20` + `D21` + `D13`). -/
theorem sin_cero_absoluto_abre_ruptura {fase : FaseToroThick.FaseThick} {d : ℕ}
    (hd : 2 ≤ d) (h : FaseToroThick.thickFase fase d ≠ 0) :
    fase = .toro ∧ 4 ≤ d ∧ PrimeraRuptura.RupturaCamino d := by
  obtain rfl := FaseToroThick.sin_cero_absoluto_implica_toro h
  have h4 := cuatro_le_de_sin_cero_absoluto hd h
  exact ⟨rfl, h4, (PrimeraRuptura.ruptura_camino_iff_cuatro_le d hd).2 h4⟩

/-! ## La distinción cancela el cero y el infinito -/

theorem sin_ruptura_tres : ¬ PrimeraRuptura.RupturaCamino 3 := by
  rw [PrimeraRuptura.ruptura_camino_iff_cuatro_le 3 (by norm_num)]
  omega

/-- **La distinción cancela el cero y el infinito.**

* En `H3`, sin distinción, el cero absoluto es admisible: la seed tiene
  thick `0` y el camino no está en ruptura.
* Distinguir B de A añade `q(A,B) > 0` como cuarto eje.
* Con `k` observables más, el canal vive en `d = 3+1+k ≥ 4`. Para todo `k`:
  ruptura, fase toro, `0 < thick < ∞` con thick `= δ_geom(d)`, y el defect
  en la banda `δ_geom(4) ≤ δ_geom(d) < δ_geom(4) + Δ` de `D31`. Añadir ejes no
  devuelve el defect a `0` ni lo lleva a `∞`. -/
theorem distincion_cancela_cero_e_infinito (P : SeedGermination) (k : ℕ) :
    (FaseToroThick.thickFase .seed 3 = 0 ∧ ¬ PrimeraRuptura.RupturaCamino 3)
    ∧ (0 < qAB P ∧ ∀ obs, estadoRelacionalGen P k obs ⟨3, by omega⟩ = qAB P)
    ∧ Module.finrank ℝ (HilbertRel k) = 3 + 1 + k
    ∧ PrimeraRuptura.RupturaCamino (3 + 1 + k)
    ∧ faseDesdeRuptura (3 + 1 + k) = .toro
    ∧ 0 < FaseToroThick.thickFase .toro (3 + 1 + k)
    ∧ FaseToroThick.thickFase .toro (3 + 1 + k) ≠ ⊤
    ∧ FaseToroThick.thickFase .toro (3 + 1 + k) =
        ENNReal.ofReal (Gnomon.geometricGap (3 + 1 + k))
    ∧ Gnomon.geometricGap 4 ≤ Gnomon.geometricGap (3 + 1 + k)
    ∧ Gnomon.geometricGap (3 + 1 + k) - Gnomon.geometricGap 4
        < GapCuatroAsintota.gapCuatroInf := by
  have h4 : 4 ≤ 3 + 1 + k := by omega
  have hR := ruptura_HilbertRel k
  have hT := toro_HilbertRel k
  rw [finrank_HilbertRel] at hR hT
  have hB := BandaExistenciaMedible.banda_del_defect (3 + 1 + k) h4
  exact ⟨⟨rfl, sin_ruptura_tres⟩, ⟨qAB_positivo P, coordenada_q_gen P k⟩,
    finrank_HilbertRel k, hR, hT,
    FaseToroThick.thick_toro_positivo _ h4, FaseToroThick.thick_toro_no_infinito _,
    rfl, hB.1, hB.2.1⟩

end PuenteBanachHilbertAB

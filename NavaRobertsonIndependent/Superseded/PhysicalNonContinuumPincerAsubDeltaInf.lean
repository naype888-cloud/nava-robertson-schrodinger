import Mathlib.Tactic
import Mathlib.Logic.Function.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import NavaRobertsonIndependent.Mathematics.D2_Robertson

/-!
# Pinza Asub--deltaInf: no-continuo fisico

> **Superseded (reemplazado en v14).** El "no continuo" de este archivo se reduce a
> `x > 0 ⇒ x ≠ 0`, y Cantor aparece solo como campo. El contenido real está en
> `Physics/PhysicalSupportR4` (soporte finito, discreto y acotado en ℝ⁴; tiempos
> numerables que no son el continuo de Cantor; sucesiones convergentes eventualmente
> constantes). Se conserva compilando, fuera de las cuatro capas.

Companion Lean 4 para `PAPER_Asub_DeltaInf_NoContinuo_Fisico.tex`.

Dos anclas permanecen verificadas en todo momento dentro de este modulo:

* La MQ de Robertson--Schroedinger 1929--1930: en este paquete es el teorema
  demostrado en `D2_Robertson` (piso lineal, cota cuadratica y saturacion como
  igualdad) y su puente con dos vectores cualesquiera de un espacio de Hilbert
  complejo (`evaluacionSchrodingerDeGram`, cota por Gram). No entra como
  hipotesis ni como campo.
* `3 < pi` (mathlib, `Real.pi_gt_three`): ancla aritmetica permanente.

El archivo separa tres niveles:

* **Lado matematico:** la MQ de Robertson--Schroedinger 1929--1930 y
  Cantor no se refutan. Cantor es `cantor_surjective` de mathlib (teorema
  real, no marcador); la MQ 1929--1930 es el teorema de `D2_Robertson` y se
  conserva con sus tres formas.
* **Lado del teorema (lectura fisica):** lo que el algebra cierra es
  `False` en las lecturas no pagadas: `DivisibilidadSinPiso M -> False` y
  `DefectBorradoAlInfinito M -> False` son exactamente
  `cierre_inferior_Asub` y `cierre_superior_deltaInf`.
* `Asub` queda certificado como frontera inferior cuando proviene de una
  cadena de factores positivos; `deltaInf > 0` queda certificado como
  frontera superior: el limite no repone defect cero.

La conclusion formal es la "pinza": un continuo fisico completado que
exige simultaneamente `Asub = 0` (divisibilidad sin piso) y
`deltaInf = 0` (defect borrado al infinito) no habita en un marco con
`Asub > 0` y `deltaInf > 0`.
-/

universe u

namespace PinzaAsubDeltaInfNoContinuoFisico

/-! ## Ancla I: MQ de Robertson--Schroedinger 1929--1930 (lado matematico) -/

open Robertson1929

/-- La MQ 1929--1930 conservada por el cierre: piso lineal (Robertson),
cota cuadratica (Schroedinger) y saturacion como igualdad. Es la conjuncion de
tres teoremas de `D2_Robertson`; no hay campos hipoteticos. -/
theorem mq_conservada (S : EvaluacionSchrodinger) :
    pisoSchrodinger S ≤ S.sigmaA * S.sigmaB ∧
      S.covarianza ^ 2 + S.conmutador ^ 2 ≤ S.sigmaA ^ 2 * S.sigmaB ^ 2 ∧
      (SaturadaSchrodinger S ↔
        S.sigmaA ^ 2 * S.sigmaB ^ 2 = S.covarianza ^ 2 + S.conmutador ^ 2) :=
  ⟨pisoSchrodinger_le_producto S, S.cota_cuadratica, saturadaSchrodinger_iff S⟩

/-- La evaluacion no es un supuesto: cualquier par de vectores de un espacio de
Hilbert complejo produce una, con dispersiones `‖x‖`, `‖y‖` y la cota cuadratica
demostrada por Gram (`D2_Robertson`, `evaluacionSchrodingerDeGram`). -/
theorem mq_realizada {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) :
    ∃ S : EvaluacionSchrodinger, S.sigmaA = ‖x‖ ∧ S.sigmaB = ‖y‖ :=
  ⟨ObstruccionGramUnificada.evaluacionSchrodingerDeGram x y, rfl, rfl⟩

/-! ## Ancla II: Cantor (lado matematico) y `3 < pi` (ancla aritmetica) -/

/-- Cantor matematico, tal como esta demostrado en mathlib
(`cantor_surjective`): no existe funcion sobreyectiva `α → Set α`. Este
modulo no lo niega ni lo reemplaza; del lado del teorema solo se niega la
lectura fisica no pagada. -/
theorem cantor_matematico (α : Type u) (f : α → Set α) :
    ¬Function.Surjective f :=
  Function.cantor_surjective f

/-- Ancla aritmetica permanente del modulo: `3 < pi` (mathlib,
`Real.pi_gt_three`). -/
theorem ancla_pi_mayor_que_tres : 3 < Real.pi :=
  Real.pi_gt_three

/-- Cadena algebraica que produce `Asub` desde factores positivos. -/
structure CadenaAsub where
  qQ : ℝ
  OmegaB : ℝ
  APlanck : ℝ
  qsub : ℝ
  Asub : ℝ
  qsub_eq : qsub = OmegaB * qQ
  Asub_eq : Asub = qsub * APlanck
  qQ_pos : 0 < qQ
  OmegaB_pos : 0 < OmegaB
  APlanck_pos : 0 < APlanck

/-- La cadena positiva fuerza `Asub > 0`. -/
theorem cadena_Asub_pos (C : CadenaAsub) : 0 < C.Asub := by
  have hqsub : 0 < C.qsub := by
    rw [C.qsub_eq]
    exact mul_pos C.OmegaB_pos C.qQ_pos
  rw [C.Asub_eq]
  exact mul_pos hqsub C.APlanck_pos

/-- Por tanto, `Asub` no puede ser cero dentro de la cadena certificada. -/
theorem Asub_ne_zero (C : CadenaAsub) : C.Asub ≠ 0 :=
  ne_of_gt (cadena_Asub_pos C)

/-- Marco de pinza: frontera inferior `Asub` y frontera superior `deltaInf`. -/
structure MarcoPinza where
  Asub : ℝ
  deltaInf : ℝ
  Asub_pos : 0 < Asub
  deltaInf_pos : 0 < deltaInf

/-- Construccion del marco de pinza desde una cadena `Asub` y un certificado
externo de `deltaInf > 0` proveniente del limite de Szego. -/
def MarcoPinza.ofCadena
    (C : CadenaAsub) (deltaInf : ℝ) (hdelta : 0 < deltaInf) :
    MarcoPinza where
  Asub := C.Asub
  deltaInf := deltaInf
  Asub_pos := cadena_Asub_pos C
  deltaInf_pos := hdelta

/-- Lectura fisica prohibida por abajo: divisibilidad sin piso de registro. -/
def DivisibilidadSinPiso (M : MarcoPinza) : Prop :=
  M.Asub = 0

/-- Lectura fisica prohibida por arriba: el infinito borra el defect. -/
def DefectBorradoAlInfinito (M : MarcoPinza) : Prop :=
  M.deltaInf = 0

/-- El continuo completado habita fisicamente solo si exige simultaneamente
divisibilidad sin piso y defect cero al infinito. -/
def ContinuoCompletadoHabitaFisicamente (M : MarcoPinza) : Prop :=
  DivisibilidadSinPiso M ∧ DefectBorradoAlInfinito M

/-- `Asub > 0` cierra por abajo: del lado del teorema, la lectura fisica no
pagada devuelve exactamente `False`. -/
theorem cierre_inferior_Asub (M : MarcoPinza) :
    ¬ DivisibilidadSinPiso M := by
  intro hzero
  exact (ne_of_gt M.Asub_pos) hzero

/-- `deltaInf > 0` cierra por arriba: del lado del teorema, la lectura
fisica no pagada devuelve exactamente `False`. -/
theorem cierre_superior_deltaInf (M : MarcoPinza) :
    ¬ DefectBorradoAlInfinito M := by
  intro hzero
  exact (ne_of_gt M.deltaInf_pos) hzero

/-- Teorema de pinza: el continuo completado no habita como estado fisico
cuando el marco tiene `Asub > 0` y `deltaInf > 0`. -/
theorem no_continuo_fisico_por_pinza (M : MarcoPinza) :
    ¬ ContinuoCompletadoHabitaFisicamente M := by
  intro h
  exact cierre_inferior_Asub M h.1

/-- Version simetrica: la exclusion conserva explicitamente las dos fronteras. -/
theorem no_continuo_fisico_por_doble_cierre (M : MarcoPinza) :
    ¬ DivisibilidadSinPiso M ∧
      ¬ DefectBorradoAlInfinito M ∧
      ¬ ContinuoCompletadoHabitaFisicamente M :=
  ⟨cierre_inferior_Asub M,
    cierre_superior_deltaInf M,
    no_continuo_fisico_por_pinza M⟩

/-- Certificado editorial citable por el paper. Las dos anclas — la MQ
1929--1930 conservada (teorema de `D2_Robertson`) y `3 < pi` — estan presentes
en todo momento, junto con el Cantor matematico de mathlib. -/
structure CertificadoPinza where
  evaluacion : EvaluacionSchrodinger
  mq_conservada :
    pisoSchrodinger evaluacion ≤ evaluacion.sigmaA * evaluacion.sigmaB ∧
      evaluacion.covarianza ^ 2 + evaluacion.conmutador ^ 2 ≤
        evaluacion.sigmaA ^ 2 * evaluacion.sigmaB ^ 2 ∧
      (SaturadaSchrodinger evaluacion ↔
        evaluacion.sigmaA ^ 2 * evaluacion.sigmaB ^ 2 =
          evaluacion.covarianza ^ 2 + evaluacion.conmutador ^ 2)
  pi_mayor_que_tres : 3 < Real.pi
  cantor_matematico : ∀ (α : Type u) (f : α → Set α), ¬Function.Surjective f
  marco : MarcoPinza
  Asub_no_cero : marco.Asub ≠ 0
  deltaInf_no_cero : marco.deltaInf ≠ 0
  no_continuo_fisico : ¬ ContinuoCompletadoHabitaFisicamente marco

/-- Cualquier evaluacion Robertson--Schroedinger y cualquier marco de pinza
producen el certificado completo del paper, con ambas anclas verificadas. -/
theorem certificado_desde_marco
    (S : EvaluacionSchrodinger) (M : MarcoPinza) :
    Nonempty CertificadoPinza :=
  ⟨{
    evaluacion := S
    mq_conservada := mq_conservada S
    pi_mayor_que_tres := ancla_pi_mayor_que_tres
    cantor_matematico := fun α f ↦ cantor_matematico α f
    marco := M
    Asub_no_cero := ne_of_gt M.Asub_pos
    deltaInf_no_cero := ne_of_gt M.deltaInf_pos
    no_continuo_fisico := no_continuo_fisico_por_pinza M
  }⟩

end PinzaAsubDeltaInfNoContinuoFisico

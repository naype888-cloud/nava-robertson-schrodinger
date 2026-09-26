/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D2_Robertson
public import NavaRobertsonIndependent.Mathematics.D7_Niven

/-!
# Defect intrínseco de una dinámica elemental posición–transporte

Este módulo separa la existencia algebraica del defect de cualquier acto de
observación. Una dinámica aporta una evaluación Robertson–Schrödinger y el
puente que identifica su condición de saturación con la condición espectral
del par elemental de posición–transporte `(T_d, P_d)`. Desde `d = 4`, Niven
obstruye esa igualdad; por tanto, el defect cuadrático es estrictamente
positivo. Ningún observador aparece en las definiciones ni en las hipótesis.
-/

@[expose] public noncomputable section

namespace DinamicaElemental

open Robertson1929

/-- Diferencia intrínseca entre el producto cuadrático de dispersiones y el
piso de Robertson–Schrödinger. Depende exclusivamente de los datos algebraicos
de la evaluación. -/
def defectIntrinseco (S : EvaluacionSchrodinger) : ℝ :=
  S.sigmaA ^ 2 * S.sigmaB ^ 2 -
    (S.covarianza ^ 2 + S.conmutador ^ 2)

/-- El defect intrínseco nunca es negativo. -/
theorem defectIntrinseco_nonneg (S : EvaluacionSchrodinger) :
    0 ≤ defectIntrinseco S := by
  unfold defectIntrinseco
  linarith [S.cota_cuadratica]

/-- El defect se anula exactamente cuando la desigualdad se satura. -/
theorem defectIntrinseco_eq_zero_iff (S : EvaluacionSchrodinger) :
    defectIntrinseco S = 0 ↔ SaturadaSchrodinger S := by
  unfold defectIntrinseco SaturadaSchrodinger
  constructor <;> intro h <;> linarith

/-- La no-saturación equivale a un defect estrictamente positivo. -/
theorem defectIntrinseco_pos_iff (S : EvaluacionSchrodinger) :
    0 < defectIntrinseco S ↔ ¬ SaturadaSchrodinger S := by
  have hnonneg := defectIntrinseco_nonneg S
  rw [← defectIntrinseco_eq_zero_iff]
  constructor
  · exact ne_of_gt
  · intro hne
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Interfaz algebraica de cualquier sistema cuya dinámica elemental de
posición y transporte realiza la geometría espectral del par `(T_d, P_d)`.
El campo de transporte no describe una medición: identifica dos condiciones
de saturación internas al sistema. -/
structure PosicionTransporte (d : ℕ) where
  evaluacion : EvaluacionSchrodinger
  saturacion_iff_camino :
    SaturadaSchrodinger evaluacion ↔
      Real.cos (Real.pi / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4

/-- Defect propio de una dinámica elemental posición–transporte. -/
def PosicionTransporte.defect {d : ℕ} (D : PosicionTransporte d) : ℝ :=
  defectIntrinseco D.evaluacion

/-- Desde cuatro dimensiones, ninguna dinámica que realice el par elemental
`(T_d, P_d)` puede saturar Robertson–Schrödinger. -/
theorem PosicionTransporte.no_saturacion {d : ℕ} (D : PosicionTransporte d)
    (hd : 4 ≤ d) : ¬ SaturadaSchrodinger D.evaluacion := by
  intro hsat
  exact Gnomon.no_reposición_saturacion_camino d hd
    (D.saturacion_iff_camino.mp hsat)

/-- **Obstrucción intrínseca.** Toda dinámica elemental posición–transporte
que realiza `(T_d, P_d)` en dimensión `d ≥ 4` posee defect estrictamente
positivo. El resultado no contiene observador, medición ni colapso. -/
theorem PosicionTransporte.defect_pos {d : ℕ} (D : PosicionTransporte d)
    (hd : 4 ≤ d) : 0 < D.defect := by
  exact (defectIntrinseco_pos_iff D.evaluacion).2 (D.no_saturacion hd)

/-- El certificado conjunto deja explícito que la positividad es uniforme
para toda realización algebraica del transporte elemental en `d ≥ 4`. -/
theorem defect_intrinseco_en_toda_dinamica_TdPd :
    ∀ (d : ℕ), 4 ≤ d → ∀ D : PosicionTransporte d, 0 < D.defect := by
  intro d hd D
  exact D.defect_pos hd

end DinamicaElemental

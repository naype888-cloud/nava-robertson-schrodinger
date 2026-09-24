import NavaRobertsonIndependent.Physics.MaximumSpeed
import NavaRobertsonIndependent.Physics.PhysicalDimensionalQuantum

/-!
# Flecha del tiempo: ningún paso resta tiempo

Cadena, toda ya demostrada en el corpus salvo el último eslabón, que es este archivo:

1. **El defect fija el tick.** `τ_sbpk = tickDim 4 = escalaLongitud · δ(4) / c`
   (`tick_es_defect`), y `δ(4) > 0` (`D25`, `D8`). El tick es positivo porque el
   defect de `H₄` es positivo.
2. **Cada paso cuesta al menos un tick** (`ProcesoTransporte.paso_dura_un_tick`).
   Ningún paso dura `0` ni menos (`paso_pos`).
3. **Las duraciones solo se suman.** El tiempo registrado tras `j` pasos,
   `tiempoTras P j`, crece al menos un tick por paso (`flecha_cuantitativa`) y es
   estrictamente creciente en `j` (`flecha`).
4. **No hay retorno.** Ningún paso posterior recupera un tiempo anterior
   (`no_retorno`).
5. **La dirección espacial no invierte el tiempo.** `ProcesoTransporte` no tiene
   campo de dirección: recorrer los mismos pasos en orden inverso (`reverso`) es otro
   proceso admisible con la misma duración (`duracion_reverso`), y ir y volver suma
   tiempo, nunca lo cancela (`ida_y_vuelta`).

No se usa entropía: la flecha sale del piso del tick y de la aditividad.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace FlechaDelTiempo

open LimiteSubPlanckiano ColapsoSchwarzschild VelocidadMaximaRegistrable CuantoDimensionalFisico

/-- **El tick es el defect de `H₄`** en unidades de laboratorio. -/
theorem tick_es_defect :
    Tausbpk = PasoElementalCelda.escalaLongitud * CuantoDimensional.cuantoDim 4 / cSI := by
  rw [← tickDim_cuatro]; rfl

/-- El defect de `H₄` y el tick son positivos a la vez. -/
theorem defect_y_tick_pos : 0 < CuantoDimensional.cuantoDim 4 ∧ 0 < Tausbpk :=
  ⟨CuantoDimensional.cuantoDim_pos le_rfl, Tausbpk_pos⟩

variable {k : ℕ} (P : ProcesoTransporte k)

/-- Ningún paso dura cero ni menos. -/
theorem paso_pos (i : Fin k) : 0 < P.tau i :=
  lt_of_lt_of_le Tausbpk_pos (P.paso_dura_un_tick i)

/-- Tiempo registrado tras los primeros `j` pasos. -/
def tiempoTras (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < j), P.tau i

theorem tiempoTras_cero : tiempoTras P 0 = 0 := by
  simp [tiempoTras]

theorem tiempoTras_total : tiempoTras P k = P.duracion := by
  simp [tiempoTras, ProcesoTransporte.duracion]

/-- Dar el paso `j` suma exactamente su duración. -/
theorem tiempoTras_succ {j : ℕ} (hj : j < k) :
    tiempoTras P (j + 1) = tiempoTras P j + P.tau ⟨j, hj⟩ := by
  unfold tiempoTras
  have hs : Finset.univ.filter (fun i : Fin k => (i : ℕ) < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin k => (i : ℕ) < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  rw [hs, Finset.sum_insert (by simp), add_comm]

/-- **Flecha, forma cuantitativa**: `m` pasos más suman al menos `m` ticks. -/
theorem flecha_cuantitativa (j m : ℕ) (h : j + m ≤ k) :
    tiempoTras P j + (m : ℝ) * Tausbpk ≤ tiempoTras P (j + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hjm : j + m < k := by omega
    have := ih (by omega)
    rw [← add_assoc, tiempoTras_succ P hjm]
    have := P.paso_dura_un_tick ⟨j + m, hjm⟩
    push_cast
    linarith

/-- **Flecha del tiempo**: el tiempo registrado es estrictamente creciente en el
número de pasos. -/
theorem flecha {j₁ j₂ : ℕ} (h : j₁ < j₂) (hk : j₂ ≤ k) :
    tiempoTras P j₁ < tiempoTras P j₂ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  have hq := flecha_cuantitativa P j₁ (m + 1) (by omega)
  have : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * Tausbpk :=
    mul_pos (by exact_mod_cast Nat.succ_pos m) Tausbpk_pos
  rw [show j₁ + m + 1 = j₁ + (m + 1) by omega]
  linarith

/-- **No hay retorno**: después de avanzar, nunca se vuelve a un tiempo anterior ni
al mismo. -/
theorem no_retorno {j₁ j₂ : ℕ} (h : j₁ < j₂) (hk : j₂ ≤ k) :
    ¬ tiempoTras P j₂ ≤ tiempoTras P j₁ :=
  not_le.mpr (flecha P h hk)

/-- Tras al menos un paso, el tiempo registrado es positivo. -/
theorem tiempoTras_pos {j : ℕ} (hj : 1 ≤ j) (hk : j ≤ k) : 0 < tiempoTras P j := by
  have := flecha P (Nat.lt_of_lt_of_le Nat.zero_lt_one hj) hk
  rwa [tiempoTras_cero] at this

/-- Los mismos pasos en orden inverso: otro proceso admisible. -/
def reverso : ProcesoTransporte k where
  tau i := P.tau i.rev
  deltaH i := P.deltaH i.rev
  tau_nonneg i := P.tau_nonneg i.rev
  mt i := P.mt i.rev
  admisible i := P.admisible i.rev

/-- Invertir el orden no cambia la duración. -/
theorem duracion_reverso : (reverso P).duracion = P.duracion := by
  unfold ProcesoTransporte.duracion reverso
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

/-- **Ir y volver suma tiempo**: el regreso no cancela la ida. -/
theorem ida_y_vuelta (hk : 1 ≤ k) :
    2 * ((k : ℝ) * Tausbpk) ≤ P.duracion + (reverso P).duracion ∧
      P.duracion < P.duracion + (reverso P).duracion := by
  rw [duracion_reverso]
  have h := P.k_pasos_cuestan_k_ticks
  have hp := P.duracion_pos hk
  constructor <;> linarith

#print axioms flecha
#print axioms ida_y_vuelta

end FlechaDelTiempo

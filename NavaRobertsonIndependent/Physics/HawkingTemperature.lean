import NavaRobertsonIndependent.Physics.DimensionalMassGap
import NavaRobertsonIndependent.Physics.TimeEnergyRegistrationClosure

/-!
# Temperatura de Hawking: piso, techo y valor en la celda

Las tres magnitudes del horizonte (radio, temperatura, entropía) quedan ligadas por el
mismo piso `L_sbpk`.

## Hipótesis declaradas

* **Ley de área** (Bekenstein–Hawking): la entropía del horizonte es
  `S = k_B c³ A / (4 ħ G)`, con `A = 4π R_s²`. Aquí es la **definición**
  `entropiaBH`; que esa sea la entropía física es la hipótesis.
* **Primera ley** con `E = M c²`: `dE = T dS`, es decir `T = c² / (dS/dM)`. Aquí es
  la **definición** `temperaturaPrimeraLey`.
* Para el valor en la celda: `G > 0` y `RelacionPlanckNewton` (como en
  `SchwarzschildCollapse`).

## Teoremas

* `temperaturaPrimeraLey_eq_hawking`: de la ley de área y la primera ley sale
  `T = ħ c³ / (8π G k_B M)`, no se supone.
* **Piso (tercera ley)**: `T > 0` para toda masa finita (`temperaturaHawking_pos`);
  `T` solo tiende a `0` cuando `M → ∞` (`temperaturaHawking_tendsto_cero`), y el
  soporte físico es finito (`PhysicalSupportR4`). El cero absoluto queda en la
  seed, que no se registra (`D36`).
* `temperaturaHawking_strictAnti`: más masa, más frío.
* **Techo**: el horizonte no mide menos que `L_sbpk`, así que `M ≥ sbpkMassGap` y
  `T ≤ T(sbpkMassGap)` (`temperaturaHawking_le_celda`).
* **Valor en la celda**: `T(sbpkMassGap) = T_P / (4π y)`, con `y = lsubCanal` y
  `T_P = M_P c² / k_B` la temperatura de Planck del paquete
  (`temperaturaHawking_celda`). Numéricamente `≈ 42.2 · T_P`; aquí se prueba
  `T_P < T(celda)` (`celda_supera_Planck`). Nada del corpus acota la temperatura por
  `T_P`: lo sub-Planckiano son las magnitudes de registro, no la temperatura.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace TemperaturaHawking

open Real Filter Topology
open LimiteSubPlanckiano ColapsoSchwarzschild SaltoMasaDimensional
  CierreRegistroTiempoEnergiaSbpk

/-- Área del horizonte de masa `M`: `A = 4π R_s²`, `R_s = 2GM/c²`. -/
def areaHorizonte (G M : ℝ) : ℝ := 4 * π * (2 * G * M / cSI ^ 2) ^ 2

/-- **Ley de área** (hipótesis declarada como definición):
`S = k_B c³ A / (4 ħ G)`. -/
def entropiaBH (G M : ℝ) : ℝ :=
  kBSI * cSI ^ 3 * areaHorizonte G M / (4 * hbarSI * G)

/-- **Primera ley** con `E = M c²` (hipótesis declarada como definición):
`T = c² / (dS/dM)`. -/
def temperaturaPrimeraLey (G M : ℝ) : ℝ := cSI ^ 2 / deriv (entropiaBH G) M

/-- Forma cerrada de Hawking. -/
def temperaturaHawking (G M : ℝ) : ℝ := hbarSI * cSI ^ 3 / (8 * π * G * kBSI * M)

/-- Temperatura de Planck del paquete: `T_P = M_P c² / k_B`. -/
def temperaturaPlanckSbpk : ℝ := masaPlanckSbpk * cSI ^ 2 / kBSI

/-- La ley de área es cuadrática en la masa: `S = (4π G k_B / (ħ c)) M²`. -/
theorem entropiaBH_eq {G : ℝ} (hG : 0 < G) (M : ℝ) :
    entropiaBH G M = 4 * π * G * kBSI / (hbarSI * cSI) * M ^ 2 := by
  unfold entropiaBH areaHorizonte
  field_simp [hG.ne', hbarSI_pos.ne', cSI_pos.ne']
  ring

theorem hasDerivAt_entropiaBH {G : ℝ} (hG : 0 < G) (M : ℝ) :
    HasDerivAt (entropiaBH G) (8 * π * G * kBSI / (hbarSI * cSI) * M) M := by
  have hf : entropiaBH G = fun M => 4 * π * G * kBSI / (hbarSI * cSI) * M ^ 2 :=
    funext (entropiaBH_eq hG)
  rw [hf]
  have := (hasDerivAt_pow 2 M).const_mul (4 * π * G * kBSI / (hbarSI * cSI))
  refine this.congr_deriv ?_
  norm_num
  ring

/-- **Hawking desde la ley de área y la primera ley.** -/
theorem temperaturaPrimeraLey_eq_hawking {G M : ℝ} (hG : 0 < G) (hM : 0 < M) :
    temperaturaPrimeraLey G M = temperaturaHawking G M := by
  unfold temperaturaPrimeraLey temperaturaHawking
  rw [(hasDerivAt_entropiaBH hG M).deriv]
  have := pi_pos
  field_simp [hG.ne', hM.ne', hbarSI_pos.ne', cSI_pos.ne', kBSI_pos.ne']

/-- **Piso (tercera ley)**: toda masa finita tiene temperatura positiva. -/
theorem temperaturaHawking_pos {G M : ℝ} (hG : 0 < G) (hM : 0 < M) :
    0 < temperaturaHawking G M := by
  unfold temperaturaHawking
  have := pi_pos
  exact div_pos (mul_pos hbarSI_pos (pow_pos cSI_pos 3))
    (by have := kBSI_pos; positivity)

/-- El cero solo es límite: `T → 0` únicamente cuando `M → ∞`. -/
theorem temperaturaHawking_tendsto_cero {G : ℝ} (hG : 0 < G) :
    Tendsto (temperaturaHawking G) atTop (𝓝 0) := by
  have hk : 0 < 8 * π * G * kBSI := by have := pi_pos; have := kBSI_pos; positivity
  have h : temperaturaHawking G =
      fun M => hbarSI * cSI ^ 3 / (8 * π * G * kBSI) / M := by
    funext M; unfold temperaturaHawking; rw [div_div, mul_assoc (8 * π * G) kBSI M]
  rw [h]
  exact tendsto_const_nhds.div_atTop tendsto_id

/-- Más masa, más frío. -/
theorem temperaturaHawking_strictAnti {G M₁ M₂ : ℝ} (hG : 0 < G) (h₁ : 0 < M₁)
    (h : M₁ < M₂) : temperaturaHawking G M₂ < temperaturaHawking G M₁ := by
  unfold temperaturaHawking
  have hk : 0 < 8 * π * G * kBSI := by have := pi_pos; have := kBSI_pos; positivity
  apply div_lt_div_of_pos_left (mul_pos hbarSI_pos (pow_pos cSI_pos 3))
    (mul_pos hk h₁) (mul_lt_mul_of_pos_left h hk)

/-- **Techo**: si el horizonte mide al menos `L_sbpk`, la temperatura no supera la de
la celda. -/
theorem temperaturaHawking_le_celda {G M : ℝ} (hG : 0 < G)
    (hPlanck : RelacionPlanckNewton G longitudPlanckCODATA)
    (hR : Lsbpk ≤ 2 * G * M / cSI ^ 2) :
    temperaturaHawking G M ≤ temperaturaHawking G sbpkMassGap := by
  have hM : sbpkMassGap ≤ M := by
    rw [← sbpkMassGap_eq_masaSchwarzschild_Lsbpk hG hPlanck]
    unfold masaSchwarzschild
    have hc : 0 < cSI ^ 2 := pow_pos cSI_pos 2
    rw [le_div_iff₀ hc] at hR
    rw [div_le_iff₀ (by positivity)]
    linarith
  rcases hM.lt_or_eq with hlt | heq
  · exact (temperaturaHawking_strictAnti hG sbpkMassGap_pos hlt).le
  · rw [heq]

/-- **Valor en la celda**: `T(sbpkMassGap) = T_P / (4π y)`. -/
theorem temperaturaHawking_celda {G : ℝ} (hG : 0 < G)
    (hPlanck : RelacionPlanckNewton G longitudPlanckCODATA) :
    temperaturaHawking G sbpkMassGap = temperaturaPlanckSbpk / (4 * π * lsubCanal) := by
  unfold RelacionPlanckNewton at hPlanck
  unfold temperaturaHawking temperaturaPlanckSbpk sbpkMassGap masaPlanckSbpk energiaPlanck
  have hl := longitudPlanckCODATA_pos
  have hy := lsubCanal_pos
  have := pi_pos
  have hGe : G = longitudPlanckCODATA ^ 2 * cSI ^ 3 / hbarSI := by
    rw [hPlanck]; field_simp [hbarSI_pos.ne', cSI_pos.ne']
  rw [hGe]
  field_simp [hbarSI_pos.ne', cSI_pos.ne', kBSI_pos.ne', hl.ne', hy.ne']
  ring

/-- `4π y < 1`: el factor `1/(4π y)` supera `1`. -/
theorem cuatro_pi_lsubCanal_lt_uno : 4 * π * lsubCanal < 1 := by
  have hq : channelSubQuantum < 0.0012 := by
    unfold channelSubQuantum Omega_b
    have h0 := deltaD4_pos
    have h1 := deltaD4_lt
    nlinarith
  have hl : lsubCanal < 0.035 := by
    nlinarith [lsubCanal_sq, lsubCanal_pos]
  have hp := pi_lt_d2
  nlinarith [lsubCanal_pos, pi_pos]

/-- **La celda supera la temperatura de Planck**: nada lo prohíbe. -/
theorem celda_supera_Planck {G : ℝ} (hG : 0 < G)
    (hPlanck : RelacionPlanckNewton G longitudPlanckCODATA) :
    temperaturaPlanckSbpk < temperaturaHawking G sbpkMassGap := by
  rw [temperaturaHawking_celda hG hPlanck]
  have hT : 0 < temperaturaPlanckSbpk :=
    div_pos (mul_pos masaPlanckSbpk_pos (pow_pos cSI_pos 2)) kBSI_pos
  have hd : 0 < 4 * π * lsubCanal := by have := pi_pos; have := lsubCanal_pos; positivity
  rw [lt_div_iff₀ hd]
  nlinarith [cuatro_pi_lsubCanal_lt_uno]

#print axioms temperaturaPrimeraLey_eq_hawking
#print axioms temperaturaHawking_le_celda
#print axioms celda_supera_Planck

end TemperaturaHawking

import Mathlib

/-!
# D26 — Baryogénesis espejo (módulo independiente, autosuficiente)

Epistemic status: **formalmente verificado** (sin `sorry`). Todo lo que se
afirma aquí está demostrado desde Mathlib. La afirmación numérica de alta
precisión (acuerdo de `g_s * exp(-1/CoherenceConstantInf)` con `0.049543679`) **no se
certifica en este archivo** — eso vive en `D26b_EncierroOmegaB.lean`, con
su propio margen probado en Lean (`< 1.12×10⁻¹⁰` absoluto, `< 2.3×10⁻⁹`
relativo; el `2×10⁻⁹` citado antes era un redondeo hacia abajo de la
distancia real `≈ 2.26×10⁻⁹` y no es demostrable como cota).
-/

namespace BaryogenesisEspejo

open Real

/-- Espectro del grafo camino: coseno de la k-ésima raíz de Chebyshev en dimensión d. -/
noncomputable def c (k d : ℕ) : ℝ := Real.cos (k * Real.pi / (d + 1))

/-- **Espejo espectral** (estado: demostrado). El espectro del grafo camino
    es simétrico bajo k ↦ (d+1) − k: la fase espejo reproduce el sector
    positivo con signo negativo exacto. -/
theorem espejo_espectral {k d : ℕ} (hk : k ≤ d + 1) :
    c (d + 1 - k) d = - c k d := by
  unfold c
  rw [Nat.cast_sub hk]
  push_cast
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  have hkey : ((d : ℝ) + 1 - k) * Real.pi / ((d : ℝ) + 1)
      = Real.pi - (k : ℝ) * Real.pi / ((d : ℝ) + 1) := by
    field_simp
  rw [hkey, Real.cos_pi_sub]

/-- **Registro ciego al signo** (estado: demostrado, seed formal de
    "el sector espejo negativo no es registrable"): la cota de
    Robertson–Schrödinger solo ve el cuadrado del conmutador; el sector
    espejo negativo proyecta la misma sombra medible que el positivo. -/
theorem registro_ciego_al_signo (x : ℝ) : x ^ 2 / 4 = (-x) ^ 2 / 4 := by ring

/-- Acoplamiento de Szegő C∞ = sqrt(π²/3 − 2) (estado: definición formal). -/
noncomputable def CoherenceConstantInf : ℝ := Real.sqrt (Real.pi ^ 2 / 3 - 2)

/-- Factor de acoplamiento g_s = 1 − 1/C∞ (estado: definición formal). -/
noncomputable def g_s : ℝ := 1 - 1 / CoherenceConstantInf

/-- C∞ > 0 (estado: demostrado, lema auxiliar). -/
theorem CoherenceConstantInf_pos : 0 < CoherenceConstantInf := by
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d4]
  have h1 : (0 : ℝ) ^ 2 < Real.pi ^ 2 / 3 - 2 := by nlinarith
  exact Real.lt_sqrt_of_sq_lt h1

/-- C∞ > 1 (estado: demostrado). -/
theorem one_lt_CoherenceConstantInf : 1 < CoherenceConstantInf := by
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d4]
  have h1 : (1 : ℝ) ^ 2 < Real.pi ^ 2 / 3 - 2 := by nlinarith
  exact Real.lt_sqrt_of_sq_lt h1

/-- C∞ < 1.15 (estado: demostrado, encerramiento racional vía π < 3.1416). -/
theorem CoherenceConstantInf_lt_115 : CoherenceConstantInf < 1.15 := by
  rw [CoherenceConstantInf, Real.sqrt_lt' (show (0:ℝ) < 1.15 by norm_num)]
  nlinarith [Real.pi_lt_d4, Real.pi_gt_d4]

/-- g_s > 0 (estado: demostrado). -/
theorem gs_pos : 0 < g_s := by
  have hC : 0 < CoherenceConstantInf := CoherenceConstantInf_pos
  show 0 < 1 - 1 / CoherenceConstantInf
  rw [sub_pos, div_lt_one hC]
  exact one_lt_CoherenceConstantInf

/-- g_s < 0.15 (estado: demostrado). -/
theorem gs_lt : g_s < 0.15 := by
  have hC : 0 < CoherenceConstantInf := CoherenceConstantInf_pos
  have hrec : (0.85 : ℝ) < 1 / CoherenceConstantInf := by
    rw [lt_div_iff₀ hC]
    have h115 := CoherenceConstantInf_lt_115
    nlinarith
  show 1 - 1 / CoherenceConstantInf < 0.15
  linarith

/-- Factor de Boltzmann exp(−1/C∞) (estado: definición formal). Nota de
    corpus: el acuerdo decimal de `g_s * boltzmann` con `0.049543679`
    **NO** se certifica aquí: el encierro racional certificado está en
    `D26b_EncierroOmegaB` (`omegaBar_encierro`, `< 1.12×10⁻¹⁰` absoluto,
    `< 2.3×10⁻⁹` relativo). -/
noncomputable def boltzmann : ℝ := Real.exp (-1 / CoherenceConstantInf)

/-- Sector observable tras el peaje exponencial (estado: definición formal). -/
noncomputable def omegaBar : ℝ := g_s * boltzmann

/-- "Impuesto" de Boltzmann: diferencia entre el acoplamiento crudo y el
    observable (estado: definición formal). -/
noncomputable def deltaImpuesto : ℝ := g_s - omegaBar

/-- boltzmann > 0 (estado: demostrado). -/
theorem boltzmann_pos : 0 < boltzmann := Real.exp_pos _

/-- boltzmann < 1 (estado: demostrado; −1/C∞ < 0 pues C∞ > 0). -/
theorem boltzmann_lt_one : boltzmann < 1 := by
  rw [boltzmann, Real.exp_lt_one_iff]
  have hC : 0 < CoherenceConstantInf := CoherenceConstantInf_pos
  have hp : (0 : ℝ) < 1 / CoherenceConstantInf := div_pos zero_lt_one hC
  rw [neg_div]
  exact neg_lt_zero.mpr hp

/-- omegaBar > 0 (estado: demostrado). -/
theorem omegaBar_pos : 0 < omegaBar := mul_pos gs_pos boltzmann_pos

/-- **Peaje estricto** (estado: demostrado): el sector espejo observable es
    estrictamente menor que el acoplamiento crudo. -/
theorem peaje_estricto : omegaBar < g_s := by
  have h := mul_lt_mul_of_pos_left boltzmann_lt_one gs_pos
  rw [mul_one] at h
  exact h

/-- El impuesto de Boltzmann es estrictamente positivo (estado: demostrado). -/
theorem impuesto_positivo : 0 < deltaImpuesto := by
  rw [deltaImpuesto, sub_pos]
  exact peaje_estricto

/-- **Cadena de baryogénesis espejo** (estado: demostrado): 0 < g_s,
    boltzmann < 1, omegaBar < g_s, 0 < deltaImpuesto. El sector espejo
    negativo es formalmente invisible (registro_ciego_al_signo) y el sector
    positivo paga un peaje exponencial estricto. -/
theorem cadena_baryogenesis :
    0 < g_s ∧ boltzmann < 1 ∧ omegaBar < g_s ∧ 0 < deltaImpuesto :=
  ⟨gs_pos, boltzmann_lt_one, peaje_estricto, impuesto_positivo⟩

#print axioms espejo_espectral
#print axioms registro_ciego_al_signo
#print axioms CoherenceConstantInf_pos
#print axioms one_lt_CoherenceConstantInf
#print axioms CoherenceConstantInf_lt_115
#print axioms gs_pos
#print axioms gs_lt
#print axioms boltzmann_pos
#print axioms boltzmann_lt_one
#print axioms omegaBar_pos
#print axioms peaje_estricto
#print axioms impuesto_positivo
#print axioms cadena_baryogenesis

end BaryogenesisEspejo

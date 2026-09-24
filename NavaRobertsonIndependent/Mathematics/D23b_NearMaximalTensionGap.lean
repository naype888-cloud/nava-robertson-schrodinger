import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation

/-!
# D23b — El sobrante en los estados intermedios

`D21` calcula el sobrante de Robertson–Schrödinger en los estados de máxima tensión,
`⟨K_d⟩ = 2/(d−1)`: es el defect de Gram `defectGram d`. `D23` muestra que por debajo del
máximo hay estados que saturan (sobrante `0`). Aquí se estudia el sobrante en **todo**
estado unitario, en función de su tensión `⟨K_d⟩`:

* `sobrante_eq`: en todo estado,
  `sobrante ψ = Var T_d · Var P_d − (cov² + ⟨K_d⟩²/4)`; el piso lo fija la tensión del estado.
* `sobrante_fase`: el sobrante no depende de la fase global.
* `sobrante_psiStar`: en `ψ*`, el sobrante es `defectGram d`.
* `tension_le`: en todo estado unitario, `⟨K_d⟩ ≤ 2/(d−1)`.
* `sobrante_cerca_del_maximo`: **continuidad en el máximo.** Para todo `η > 0` hay `ε > 0` tal
  que todo estado unitario con `⟨K_d⟩ > 2/(d−1) − ε` tiene sobrante a menos de `η` de
  `defectGram d`.
* `desigualdad_estricta_banda`: para `d ≥ 4` la desigualdad de Robertson–Schrödinger es
  estricta en toda una banda de estados intermedios, `2/(d−1) − ε < ⟨K_d⟩`, no solo en el
  máximo.

El `ε` se obtiene por compacidad de la esfera unidad; no se da en forma cerrada.
-/

noncomputable section

namespace SobranteIntermedio

open NavaRobertsonSchrodingerEDUI TransportePosicion SaturacionAutovectores
  EscalonGramCoherenceConstant ConstructorEspectralTP

/-- Tensión del estado: `⟨K_d⟩ = Re ⟨ψ, K_d ψ⟩`. -/
def tension (d : ℕ) (ψ : Hd d) : ℝ :=
  (inner ℂ ψ (KdOp d ψ)).re

/-- Sobrante de Robertson–Schrödinger de `(T_d, P_d)` en `ψ`: el defect de Gram. -/
abbrev sobrante (d : ℕ) (ψ : Hd d) : ℝ :=
  defectGramEn (TdOp d) (PdOp d) ψ

/-! ## 1. Forma del sobrante -/

/-- El sobrante con el piso propio del estado, `⟨K_d⟩²/4`. -/
theorem sobrante_eq (d : ℕ) (ψ : Hd d) :
    sobrante d ψ =
      varianza (TdOp d) ψ * varianza (PdOp d) ψ -
        (covarianza (TdOp d) (PdOp d) ψ ^ 2 + tension d ψ ^ 2 / 4) := by
  rw [sobrante, defectGramEn_eq_gap,
    parteImaginaria_eq_im_inner (TdOp_simetrico d) (PdOp_simetrico d), tension, re_inner_KdOp]
  ring

theorem sobrante_fase {d : ℕ} (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    sobrante d (c • ψ) = sobrante d ψ := by
  unfold sobrante defectGramEn
  rw [varianza_fase _ _ _ hc, varianza_fase _ _ _ hc, centrado_fase _ _ _ hc,
    centrado_fase _ _ _ hc, inner_smul_left, inner_smul_right, norm_mul, norm_mul,
    Complex.norm_conj, hc]
  simp

theorem tension_psiStar {d : ℕ} (hd : 2 ≤ d) : tension d (psiStar d) = 2 / ((d : ℝ) - 1) := by
  unfold tension
  rw [KdOp_vectorFiedlerExplicito d hd, inner_smul_right, inner_self_eq_norm_sq_to_K,
    norma_psiStar hd]
  simpa using Complex.ofReal_re (2 / ((d : ℝ) - 1))

theorem sobrante_psiStar {d : ℕ} (hd : 2 ≤ d) : sobrante d (psiStar d) = defectGram d := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  rw [← gap_eq_defectGram hd, sobrante_eq, tension_psiStar hd, commutatorConstant_half_sq hd]
  field_simp
  ring

/-- La tensión de un estado unitario no pasa del máximo `2/(d−1)`. -/
theorem tension_le {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    tension d ψ ≤ 2 / ((d : ℝ) - 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  have hle := expectativa_le_radio (KdOp d) (KdOp_simetrico d) ψ hψ
  rw [radioEspectral_KdOp_eq_paso d hd] at hle
  exact (Complex.re_le_norm _).trans hle

/-! ## 2. Continuidad -/

theorem continuous_media {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) : Continuous (media A) :=
  Complex.continuous_re.comp (continuous_id.inner (LinearMap.continuous_of_finiteDimensional A))

theorem continuous_centrado {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) : Continuous (centrado A) :=
  (LinearMap.continuous_of_finiteDimensional A).sub
    ((Complex.continuous_ofReal.comp (continuous_media A)).smul continuous_id)

theorem continuous_varianza {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) : Continuous (varianza A) :=
  (continuous_centrado A).norm.pow 2

theorem continuous_tension (d : ℕ) : Continuous (tension d) :=
  Complex.continuous_re.comp
    (continuous_id.inner (LinearMap.continuous_of_finiteDimensional (KdOp d)))

theorem continuous_sobrante (d : ℕ) : Continuous (sobrante d) :=
  ((continuous_varianza _).mul (continuous_varianza _)).sub
    (((continuous_centrado _).inner (continuous_centrado _)).norm.pow 2)

/-! ## 3. El sobrante cerca del máximo -/

/-- **Continuidad del sobrante en el máximo.** Los estados unitarios con tensión cerca de
`2/(d−1)` tienen sobrante cerca de `defectGram d`. -/
theorem sobrante_cerca_del_maximo {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ ψ : Hd d, ‖ψ‖ = 1 → 2 / ((d : ℝ) - 1) - ε < tension d ψ →
      |sobrante d ψ - defectGram d| < η := by
  set S : Set (Hd d) :=
    Metric.sphere 0 1 ∩ {ψ | η ≤ |sobrante d ψ - defectGram d|} with hS
  have hSc : IsCompact S :=
    (isCompact_sphere 0 1).inter_right
      (isClosed_le continuous_const ((continuous_sobrante d).sub continuous_const).abs)
  have hfuera : ∀ ψ : Hd d, ‖ψ‖ = 1 → ψ ∉ S → |sobrante d ψ - defectGram d| < η := by
    intro ψ hψ hnS
    by_contra h
    exact hnS ⟨by simpa using hψ, le_of_not_gt h⟩
  rcases S.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ψ hψ _ => hfuera ψ hψ (by simp [he])⟩
  obtain ⟨ψ₀, hψ₀S, hmax⟩ := hSc.exists_isMaxOn hne (continuous_tension d).continuousOn
  have hψ₀ : ‖ψ₀‖ = 1 := by simpa using hψ₀S.1
  have hlt : tension d ψ₀ < 2 / ((d : ℝ) - 1) := by
    refine lt_of_le_of_ne (tension_le hd ψ₀ hψ₀) fun heq => ?_
    obtain ⟨c, hc, rfl⟩ := estado_maxima_tension_es_fase hd ψ₀ hψ₀ heq
    have h := hψ₀S.2
    simp only [Set.mem_ofPred_eq, sobrante_fase _ c hc, sobrante_psiStar hd, sub_self,
      abs_zero] at h
    linarith
  refine ⟨2 / ((d : ℝ) - 1) - tension d ψ₀, by linarith, fun ψ hψ hK => hfuera ψ hψ ?_⟩
  intro hψS
  have := hmax hψS
  simp only [Set.mem_ofPred_eq] at this
  linarith

/-- **Desigualdad estricta en una banda de estados intermedios.** Para `d ≥ 4` hay `ε > 0`
tal que todo estado unitario con `⟨K_d⟩ > 2/(d−1) − ε` cumple Robertson–Schrödinger de
forma estricta, con su propio piso `⟨K_d⟩²/4`. -/
theorem desigualdad_estricta_banda {d : ℕ} (hd : 4 ≤ d) :
    ∃ ε > 0, ∀ ψ : Hd d, ‖ψ‖ = 1 → 2 / ((d : ℝ) - 1) - ε < tension d ψ →
      covarianza (TdOp d) (PdOp d) ψ ^ 2 + tension d ψ ^ 2 / 4 <
        varianza (TdOp d) ψ * varianza (PdOp d) ψ := by
  obtain ⟨ε, hε, h⟩ := sobrante_cerca_del_maximo (by omega : 2 ≤ d) (escalon_gram_pos hd)
  refine ⟨ε, hε, fun ψ hψ hK => ?_⟩
  have h1 := h ψ hψ hK
  have h2 : 0 < sobrante d ψ := by
    have := neg_abs_le (sobrante d ψ - defectGram d)
    linarith
  rw [sobrante_eq] at h2
  linarith

end SobranteIntermedio

end

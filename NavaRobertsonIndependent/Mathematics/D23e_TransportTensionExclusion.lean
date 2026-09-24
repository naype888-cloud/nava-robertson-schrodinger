import NavaRobertsonIndependent.Mathematics.D23d_BandWidth

/-!
# D23e — Transporte máximo y tensión máxima se excluyen

Sobre `H_d = ℂ^d` con `T_d = A_d/ρ_d` (`D3`) y `K_d = i[T_d, P_d]` (`D5`) hay dos topes:

* **transporte:** `⟨T_d⟩ ≤ 1` en todo estado unitario (`media_T_le_one`), y el tope se
  alcanza en el modo seno fundamental sin fase (`media_T_vectorSeno`);
* **tensión:** `⟨K_d⟩ ≤ 2/(d−1)` (`tension_le`, `D23b`), alcanzado en `ψ*` (`D21`).

Ningún estado alcanza los dos:

* `tension_de_transporte_maximo`: si `⟨T_d⟩ = 1`, entonces `T_d ψ = ψ` y `⟨K_d⟩ = 0`;
* `transporte_de_tension_maxima`: si `⟨K_d⟩ = 2/(d−1)`, entonces `⟨T_d⟩ = 0`;
* `no_ambos_maximos`: ningún estado unitario tiene `⟨T_d⟩ = 1` y `⟨K_d⟩ = 2/(d−1)`.

En cada tope la otra cantidad vale `0`.
-/

noncomputable section

namespace ExclusionTransporteTension

open NavaRobertsonSchrodingerEDUI TransportePosicion SaturacionAutovectores SobranteIntermedio
  ConstructorEspectralTP AnchoFranja

/-! ## 1. Tope del transporte y estado que lo alcanza -/

theorem media_T_le_one {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    media (TdOp d) ψ ≤ 1 :=
  le_of_abs_le (abs_media_le (norm_TdOp_le hd) hψ)

/-- Modo seno fundamental, sin fase, sin normalizar. -/
def vectorSenoCrudo (d : ℕ) (hd : 1 ≤ d) : Hd d :=
  WithLp.toLp 2 (modoSeno d ⟨0, hd⟩)

/-- Modo seno fundamental normalizado. -/
def vectorSeno (d : ℕ) (hd : 1 ≤ d) : Hd d :=
  ((‖vectorSenoCrudo d hd‖ : ℂ)⁻¹) • vectorSenoCrudo d hd

theorem vectorSenoCrudo_ne_zero {d : ℕ} (hd : 1 ≤ d) : vectorSenoCrudo d hd ≠ 0 := by
  intro h
  apply modoSeno_ne_zero hd ⟨0, hd⟩
  simpa [vectorSenoCrudo] using congrArg WithLp.ofLp h

theorem norm_vectorSeno {d : ℕ} (hd : 1 ≤ d) : ‖vectorSeno d hd‖ = 1 := by
  have hn : ‖vectorSenoCrudo d hd‖ ≠ 0 := norm_ne_zero_iff.mpr (vectorSenoCrudo_ne_zero hd)
  rw [vectorSeno, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

/-- El modo seno fundamental es punto fijo del transporte: `T_d v = v`. -/
theorem TdOp_vectorSenoCrudo {d : ℕ} (hd : 2 ≤ d) :
    TdOp d (vectorSenoCrudo d (by omega)) = vectorSenoCrudo d (by omega) := by
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  have hA := Ad_modoSeno (d := d) (by omega) ⟨0, by omega⟩
  have hang : (2 * Real.cos (anguloModo d ⟨0, by omega⟩) : ℂ) = (rho d : ℂ) := by
    simp [anguloModo, rho]
  rw [hang] at hA
  apply (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).injective
  change (Td d).mulVec (modoSeno d ⟨0, by omega⟩) = modoSeno d ⟨0, by omega⟩
  rw [Td_eq_smul_Ad, Matrix.smul_mulVec, hA]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem TdOp_vectorSeno {d : ℕ} (hd : 2 ≤ d) :
    TdOp d (vectorSeno d (by omega)) = vectorSeno d (by omega) := by
  rw [vectorSeno, map_smul, TdOp_vectorSenoCrudo hd]

/-- El tope del transporte se alcanza. -/
theorem media_T_vectorSeno {d : ℕ} (hd : 2 ≤ d) : media (TdOp d) (vectorSeno d (by omega)) = 1 := by
  unfold media
  rw [TdOp_vectorSeno hd, inner_self_eq_norm_sq_to_K, norm_vectorSeno]
  simp

/-! ## 2. Transporte máximo ⇒ tensión nula -/

/-- Si `⟨T_d⟩ = 1` en un estado unitario, ese estado es punto fijo de `T_d`. -/
theorem punto_fijo_de_transporte_maximo {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : media (TdOp d) ψ = 1) : TdOp d ψ = ψ := by
  have hre : (inner ℂ (TdOp d ψ) ψ).re = 1 := by
    rw [← inner_conj_symm, Complex.conj_re]
    exact h
  have hT := norm_TdOp_le hd ψ
  rw [hψ] at hT
  have hsq : ‖TdOp d ψ - ψ‖ ^ 2 ≤ 0 := by
    rw [@norm_sub_sq ℂ, RCLike.re_to_complex, hre, hψ]
    nlinarith [norm_nonneg (TdOp d ψ)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (TdOp d ψ - ψ)]))

/-- **Transporte máximo ⇒ tensión nula.** -/
theorem tension_de_transporte_maximo {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : media (TdOp d) ψ = 1) : tension d ψ = 0 := by
  have hfix := punto_fijo_de_transporte_maximo hd hψ h
  have h0 := valor_esperado_conmutador_cero (TdOp d) (PdOp d) (TdOp_simetrico d) (a := 1)
    (by rw [hfix, Complex.ofReal_one, one_smul])
  unfold tension KdOp observableTension conmutador
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right,
    h0, mul_zero, Complex.zero_re]

/-! ## 3. Tensión máxima ⇒ transporte nulo -/

/-- **Tensión máxima ⇒ transporte nulo.** -/
theorem transporte_de_tension_maxima {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (h : tension d ψ = 2 / ((d : ℝ) - 1)) : media (TdOp d) ψ = 0 := by
  obtain ⟨c, hc, rfl⟩ := estado_maxima_tension_es_fase hd ψ hψ h
  rw [media_fase _ _ c hc, media_T hd]

/-! ## 4. Exclusión -/

/-- **Transporte máximo y tensión máxima se excluyen.** Ningún estado unitario tiene a la vez
`⟨T_d⟩ = 1` (tope del transporte) y `⟨K_d⟩ = 2/(d−1)` (tope de la tensión). -/
theorem no_ambos_maximos {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    ¬ (media (TdOp d) ψ = 1 ∧ tension d ψ = 2 / ((d : ℝ) - 1)) := by
  rintro ⟨hT, hK⟩
  have := transporte_de_tension_maxima hd hψ hK
  rw [hT] at this
  exact one_ne_zero this

end ExclusionTransporteTension

end

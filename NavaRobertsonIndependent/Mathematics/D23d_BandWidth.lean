import NavaRobertsonIndependent.Mathematics.D23c_TensionSpectralGap

/-!
# D23d — Ancho explícito de la franja de desigualdad estricta

`D23b` prueba que la desigualdad de Robertson–Schrödinger es estricta en una franja
`2/(d−1) − ε < ⟨K_d⟩` sin dar `ε`. Aquí se da `ε` en forma cerrada:

* `norm_TdOp_le`, `norm_PdOp_le`: `‖T_d ψ‖ ≤ ‖ψ‖`, `‖P_d ψ‖ ≤ ‖ψ‖`.
* `sobrante_lipschitz`: para estados unitarios, `|sobrante ψ − sobrante ψ'| ≤ 32 ‖ψ − ψ'‖`.
* `sobrante_franja`: para todo estado unitario,
  `brechaK d · (sobrante ψ − defectGram d)² ≤ 2048 · (2/(d−1) − ⟨K_d⟩_ψ)`.
* `anchoFranja d = brechaK d · defectGram d² / 2048`, y
  `desigualdad_estricta_franja`: para `d ≥ 4`, todo estado unitario con
  `⟨K_d⟩ > 2/(d−1) − anchoFranja d` cumple Robertson–Schrödinger de forma estricta.

Las constantes `32` y `2048` no son óptimas; salen de cotas directas.
-/

noncomputable section

namespace AnchoFranja

open NavaRobertsonSchrodingerEDUI TransportePosicion SaturacionAutovectores SobranteIntermedio
  ConstructorEspectralTP EscalonGramCoherenceConstant

/-! ## 1. `T_d` y `P_d` no alargan vectores -/

theorem norm_le_of_autovalores {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] [Nontrivial H] (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue A μ → ‖μ‖ ≤ 1) (v : H) : ‖A v‖ ≤ ‖v‖ := by
  have hv := norma_aplicacion_le_radio_mul_norma A hA v
  have hR : radioEspectral A hA ≤ 1 := by
    have := h _ (hA.hasEigenvalue_eigenvalues rfl (indiceExtremal A hA))
    simpa [radioEspectral, autovalorExtremal, Complex.norm_real, Real.norm_eq_abs] using this
  calc ‖A v‖ ≤ radioEspectral A hA * ‖v‖ := hv
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = ‖v‖ := one_mul _

theorem Td_eq_smul_Ad (d : ℕ) : Td d = ((rho d : ℂ)⁻¹) • Ad d := by
  ext i j
  simp [Td, div_eq_inv_mul]

theorem norm_TdOp_le {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) : ‖TdOp d ψ‖ ≤ ‖ψ‖ := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  refine norm_le_of_autovalores _ (TdOp_simetrico d) (fun μ hμ => ?_) ψ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hρ := rho_pos d hd
  have hTv : TdOp d v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hA : Matrix.toLin' (Ad d) (WithLp.ofLp v) = ((rho d : ℂ) * μ) • WithLp.ofLp v := by
    have h1 : WithLp.ofLp (TdOp d v) = WithLp.ofLp (μ • v) := by rw [hTv]
    simp only [TdOp, Matrix.toLpLin_apply, Td_eq_smul_Ad, Matrix.smul_mulVec,
      WithLp.ofLp_toLp, WithLp.ofLp_smul] at h1
    rw [Matrix.toLin'_apply, mul_smul, ← h1, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ.ne'),
      one_smul]
  have hne : WithLp.ofLp v ≠ 0 := fun h0 => hv.2 (by simpa using congrArg (WithLp.toLp 2) h0)
  have hEig : Module.End.HasEigenvalue (Matrix.toLin' (Ad d)) ((rho d : ℂ) * μ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hA, hne⟩
  obtain ⟨k, hk⟩ := autovalorAd_agota_espectro (by omega) hEig
  have hb := norma_autovalorAd_le_rho hd k
  rw [← hk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hb
  nlinarith [norm_nonneg μ]

theorem abs_posicionCoord_le {d : ℕ} (hd : 2 ≤ d) (j : Fin d) : |posicionCoord d j| ≤ 1 := by
  unfold posicionCoord
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hj : (j.val : ℝ) + 1 ≤ d := by exact_mod_cast (show j.val + 1 ≤ d by omega)
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (d : ℝ) - 1), div_le_one (by linarith)]
  rw [abs_le]
  constructor <;> linarith

theorem norm_PdOp_le {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) : ‖PdOp d ψ‖ ≤ ‖ψ‖ := by
  have hsq : ‖PdOp d ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : (PdOp d ψ) j = (posicionCoord d j : ℂ) * ψ j := by
      simp [PdOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Pd]
    rw [hj, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have h1 := abs_posicionCoord_le hd j
    have h2 : |posicionCoord d j| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (posicionCoord d j)]
    nlinarith [sq_nonneg ‖ψ j‖]
  nlinarith [norm_nonneg (PdOp d ψ), norm_nonneg ψ]

/-! ## 2. Cotas del vector centrado -/

section Centrado

variable {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d}

theorem abs_media_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ : Hd d} (hψ : ‖ψ‖ = 1) : |media A ψ| ≤ 1 := by
  unfold media
  calc |(inner ℂ ψ (A ψ)).re| ≤ ‖inner ℂ ψ (A ψ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ψ‖ * ‖A ψ‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by rw [hψ, one_mul, ← hψ]; exact hc ψ

theorem abs_media_sub_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ ψ' : Hd d} (hψ : ‖ψ‖ = 1)
    (hψ' : ‖ψ'‖ = 1) : |media A ψ - media A ψ'| ≤ 2 * ‖ψ - ψ'‖ := by
  have e : inner ℂ ψ (A ψ) - inner ℂ ψ' (A ψ') =
      inner ℂ (ψ - ψ') (A ψ) + inner ℂ ψ' (A (ψ - ψ')) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  unfold media
  rw [← Complex.sub_re, e]
  calc |(inner ℂ (ψ - ψ') (A ψ) + inner ℂ ψ' (A (ψ - ψ'))).re|
      ≤ ‖inner ℂ (ψ - ψ') (A ψ) + inner ℂ ψ' (A (ψ - ψ'))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (ψ - ψ') (A ψ)‖ + ‖inner ℂ ψ' (A (ψ - ψ'))‖ := norm_add_le _ _
    _ ≤ ‖ψ - ψ'‖ * ‖A ψ‖ + ‖ψ'‖ * ‖A (ψ - ψ')‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖ψ - ψ'‖ * 1 + 1 * ‖ψ - ψ'‖ := by
        rw [hψ']
        gcongr
        · exact (hc ψ).trans hψ.le
        · exact hc _
    _ = 2 * ‖ψ - ψ'‖ := by ring

theorem norm_centrado_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) : ‖centrado A ψ‖ ≤ 1 := by
  have hre : (inner ℂ (A ψ) ψ).re = media A ψ := by
    rw [← inner_conj_symm, Complex.conj_re]
    rfl
  have hsq : ‖centrado A ψ‖ ^ 2 = ‖A ψ‖ ^ 2 - media A ψ ^ 2 := by
    unfold centrado
    rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul, hψ, Complex.norm_real, Real.norm_eq_abs,
      mul_one, sq_abs, RCLike.re_to_complex, Complex.re_ofReal_mul, hre]
    ring
  have h1 : ‖A ψ‖ ≤ 1 := (hc ψ).trans hψ.le
  have h2 : ‖centrado A ψ‖ ^ 2 ≤ 1 := by
    rw [hsq]
    nlinarith [norm_nonneg (A ψ), sq_nonneg (media A ψ)]
  nlinarith [norm_nonneg (centrado A ψ)]

theorem norm_centrado_sub_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ ψ' : Hd d} (hψ : ‖ψ‖ = 1)
    (hψ' : ‖ψ'‖ = 1) : ‖centrado A ψ - centrado A ψ'‖ ≤ 4 * ‖ψ - ψ'‖ := by
  have e : centrado A ψ - centrado A ψ' =
      A (ψ - ψ') - (((media A ψ - media A ψ' : ℝ) : ℂ) • ψ + (media A ψ' : ℂ) • (ψ - ψ')) := by
    unfold centrado
    rw [map_sub]
    push_cast
    rw [sub_smul, smul_sub]
    abel
  have hm := abs_media_sub_le hc hψ hψ'
  have hm' := abs_media_le hc hψ'
  rw [e]
  calc ‖A (ψ - ψ') - (((media A ψ - media A ψ' : ℝ) : ℂ) • ψ + (media A ψ' : ℂ) • (ψ - ψ'))‖
      ≤ ‖A (ψ - ψ')‖ + (‖((media A ψ - media A ψ' : ℝ) : ℂ) • ψ‖ +
          ‖(media A ψ' : ℂ) • (ψ - ψ')‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ = ‖A (ψ - ψ')‖ + (|media A ψ - media A ψ'| + |media A ψ'| * ‖ψ - ψ'‖) := by
        rw [norm_smul, norm_smul, hψ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_one]
    _ ≤ ‖ψ - ψ'‖ + (2 * ‖ψ - ψ'‖ + 1 * ‖ψ - ψ'‖) := by
        gcongr
        · exact hc _
    _ = 4 * ‖ψ - ψ'‖ := by ring

end Centrado

/-! ## 3. El determinante de Gram es Lipschitz -/

theorem gram_lipschitz_real {x x' y y' i i' α β : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hx' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hy' : 0 ≤ y') (hy1' : y' ≤ 1)
    (hi : 0 ≤ i) (hi1 : i ≤ 1) (hi' : 0 ≤ i') (hi1' : i' ≤ 1)
    (hxa : |x - x'| ≤ α) (hyb : |y - y'| ≤ β) (hiab : |i - i'| ≤ α + β) :
    |(x ^ 2 * y ^ 2 - i ^ 2) - (x' ^ 2 * y' ^ 2 - i' ^ 2)| ≤ 4 * (α + β) := by
  have sq_le : ∀ {u u' γ : ℝ}, 0 ≤ u → u ≤ 1 → 0 ≤ u' → u' ≤ 1 → |u - u'| ≤ γ →
      |u ^ 2 - u' ^ 2| ≤ 2 * γ := by
    intro u u' γ hu hu1 hu' hu1' h
    rw [show u ^ 2 - u' ^ 2 = (u - u') * (u + u') by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + u')]
    nlinarith [abs_nonneg (u - u')]
  have hX := sq_le hx hx1 hx' hx1' hxa
  have hY := sq_le hy hy1 hy' hy1' hyb
  have hI := sq_le hi hi1 hi' hi1' hiab
  have e : (x ^ 2 * y ^ 2 - i ^ 2) - (x' ^ 2 * y' ^ 2 - i' ^ 2) =
      (x ^ 2 - x' ^ 2) * y ^ 2 + x' ^ 2 * (y ^ 2 - y' ^ 2) - (i ^ 2 - i' ^ 2) := by ring
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hx2 : x' ^ 2 ≤ 1 := by nlinarith
  rw [e]
  calc |(x ^ 2 - x' ^ 2) * y ^ 2 + x' ^ 2 * (y ^ 2 - y' ^ 2) - (i ^ 2 - i' ^ 2)|
      ≤ |x ^ 2 - x' ^ 2| * y ^ 2 + x' ^ 2 * |y ^ 2 - y' ^ 2| + |i ^ 2 - i' ^ 2| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y), abs_of_nonneg (sq_nonneg x')]
    _ ≤ 2 * α * 1 + 1 * (2 * β) + 2 * (α + β) := by
        have hα : 0 ≤ α := (abs_nonneg _).trans hxa
        have h1 := mul_le_mul hX hy2 (sq_nonneg y) (by linarith)
        have h2 := mul_le_mul hx2 hY (abs_nonneg _) (by norm_num)
        linarith
    _ = 4 * (α + β) := by ring

theorem sobrante_lipschitz {d : ℕ} (hd : 2 ≤ d) {ψ ψ' : Hd d} (hψ : ‖ψ‖ = 1) (hψ' : ‖ψ'‖ = 1) :
    |sobrante d ψ - sobrante d ψ'| ≤ 32 * ‖ψ - ψ'‖ := by
  have hT := norm_TdOp_le hd
  have hP := norm_PdOp_le hd
  set a := centrado (TdOp d) ψ
  set a' := centrado (TdOp d) ψ'
  set b := centrado (PdOp d) ψ
  set b' := centrado (PdOp d) ψ'
  have ha := norm_centrado_le hT hψ
  have ha' := norm_centrado_le hT hψ'
  have hb := norm_centrado_le hP hψ
  have hb' := norm_centrado_le hP hψ'
  have hda := norm_centrado_sub_le hT hψ hψ'
  have hdb := norm_centrado_sub_le hP hψ hψ'
  have hi : ‖inner ℂ a b‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg a, norm_nonneg b])
  have hi' : ‖inner ℂ a' b'‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg a', norm_nonneg b'])
  have hdi : |‖inner ℂ a b‖ - ‖inner ℂ a' b'‖| ≤ ‖a - a'‖ + ‖b - b'‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have e : inner ℂ a b - inner ℂ a' b' = inner ℂ (a - a') b + inner ℂ a' (b - b') := by
      rw [inner_sub_left, inner_sub_right]
      ring
    rw [e]
    calc ‖inner ℂ (a - a') b + inner ℂ a' (b - b')‖
        ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ ‖a - a'‖ * 1 + 1 * ‖b - b'‖ := by gcongr
      _ = ‖a - a'‖ + ‖b - b'‖ := by ring
  have key := gram_lipschitz_real (norm_nonneg a) ha (norm_nonneg a') ha' (norm_nonneg b) hb
    (norm_nonneg b') hb' (norm_nonneg _) hi (norm_nonneg _) hi' (abs_norm_sub_norm_le a a')
    (abs_norm_sub_norm_le b b') hdi
  have hs : ∀ φ : Hd d, sobrante d φ =
      ‖centrado (TdOp d) φ‖ ^ 2 * ‖centrado (PdOp d) φ‖ ^ 2 -
        ‖inner ℂ (centrado (TdOp d) φ) (centrado (PdOp d) φ)‖ ^ 2 := fun φ => rfl
  rw [hs ψ, hs ψ']
  calc _ ≤ 4 * (‖a - a'‖ + ‖b - b'‖) := key
    _ ≤ 4 * (4 * ‖ψ - ψ'‖ + 4 * ‖ψ - ψ'‖) := by gcongr
    _ = 32 * ‖ψ - ψ'‖ := by ring

/-! ## 4. Distancia a la órbita de fase de `ψ*` -/

/-- Todo estado unitario está a distancia `≤ √2 ‖φ‖` de una fase de `ψ*`. -/
theorem existe_fase_cercana {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖ψ - c • psiStar d‖ ^ 2 ≤ 2 * ‖componenteOrtogonal d ψ‖ ^ 2 := by
  set a := inner ℂ (psiStar d) ψ
  set φ := componenteOrtogonal d ψ
  have hn : 1 = ‖a‖ ^ 2 + ‖φ‖ ^ 2 := by
    have := norm_sq_descomp hd ψ
    rwa [hψ, one_pow] at this
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, sq_nonneg ‖φ‖]
  -- `ψ − c ψ* = φ + (a − c) ψ*`, con `φ ⊥ ψ*`
  have hdist : ∀ c : ℂ, ‖ψ - c • psiStar d‖ ^ 2 = ‖φ‖ ^ 2 + ‖a - c‖ ^ 2 := by
    intro c
    have e : ψ - c • psiStar d = φ + (a - c) • psiStar d := by
      simp only [φ, componenteOrtogonal, sub_smul]
      abel
    have h0 : inner ℂ φ ((a - c) • psiStar d) = 0 := by
      rw [inner_smul_right, ← inner_conj_symm, componenteOrtogonal_perp hd, map_zero, mul_zero]
    rw [e, @norm_add_sq ℂ, h0, norm_smul, norma_psiStar hd]
    simp
  by_cases ha0 : a = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [hdist, ha0, zero_sub, norm_neg, norm_one]
    rw [ha0, norm_zero] at hn
    nlinarith
  · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    refine ⟨((‖a‖ : ℂ))⁻¹ * a, ?_, ?_⟩
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
        inv_mul_cancel₀ hpos.ne']
    · have hac : a - ((‖a‖ : ℂ))⁻¹ * a = (((1 - ‖a‖⁻¹ : ℝ)) : ℂ) * a := by
        push_cast
        ring
      rw [hdist, hac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have e2 : |1 - ‖a‖⁻¹| * ‖a‖ = 1 - ‖a‖ := by
        rw [abs_of_nonpos (by rw [sub_nonpos]; exact one_le_inv_iff₀.mpr ⟨hpos, ha1⟩)]
        field_simp
        ring
      rw [e2]
      nlinarith [norm_nonneg a]

/-! ## 5. Ancho de la franja -/

/-- **El sobrante en la franja, con constantes explícitas.** Para todo estado unitario,
`brechaK d · (sobrante ψ − defectGram d)² ≤ 2048 · (2/(d−1) − ⟨K_d⟩_ψ)`. -/
theorem sobrante_franja {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    brechaK d * (sobrante d ψ - defectGram d) ^ 2 ≤
      2048 * (2 / ((d : ℝ) - 1) - tension d ψ) := by
  obtain ⟨c, hc, hdist⟩ := existe_fase_cercana hd ψ hψ
  have hcψ : ‖c • psiStar d‖ = 1 := by rw [norm_smul, hc, norma_psiStar hd, one_mul]
  have hL := sobrante_lipschitz hd hψ hcψ
  rw [sobrante_fase _ c hc, sobrante_psiStar hd] at hL
  have hD := distancia_le_deficit hd ψ hψ
  have hg := brechaK_pos hd
  have h1 : (sobrante d ψ - defectGram d) ^ 2 ≤ 1024 * ‖ψ - c • psiStar d‖ ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le hL) (le_of_abs_le hL)
    nlinarith
  nlinarith

/-- Ancho de la franja de desigualdad estricta. -/
def anchoFranja (d : ℕ) : ℝ := brechaK d * defectGram d ^ 2 / 2048

theorem anchoFranja_pos {d : ℕ} (hd : 4 ≤ d) : 0 < anchoFranja d :=
  div_pos (mul_pos (brechaK_pos (by omega)) (pow_pos (escalon_gram_pos hd) 2)) (by norm_num)

/-- **Desigualdad estricta en la franja de ancho explícito.** Para `d ≥ 4`, todo estado
unitario con `⟨K_d⟩ > 2/(d−1) − anchoFranja d` cumple Robertson–Schrödinger de forma
estricta, con su propio piso `⟨K_d⟩²/4`. -/
theorem desigualdad_estricta_franja {d : ℕ} (hd : 4 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1)
    (hK : 2 / ((d : ℝ) - 1) - anchoFranja d < tension d ψ) :
    covarianza (TdOp d) (PdOp d) ψ ^ 2 + tension d ψ ^ 2 / 4 <
      varianza (TdOp d) ψ * varianza (PdOp d) ψ := by
  have hd2 : 2 ≤ d := by omega
  have hF := sobrante_franja hd2 ψ hψ
  have hg := brechaK_pos hd2
  have hDpos := escalon_gram_pos hd
  have hsq : (sobrante d ψ - defectGram d) ^ 2 < defectGram d ^ 2 := by
    unfold anchoFranja at hK
    by_contra h
    push Not at h
    nlinarith
  have hs : 0 < sobrante d ψ := by nlinarith
  rw [sobrante_eq] at hs
  linarith

end AnchoFranja

end

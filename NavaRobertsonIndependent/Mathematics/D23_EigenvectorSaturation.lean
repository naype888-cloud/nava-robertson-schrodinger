import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality

/-!
# D23 — Saturación de Robertson–Schrödinger en autovectores de `A − iλB`

Sobre vectores de `Hd d`, con la media, el vector centrado, la varianza y la
covarianza de `D21`. La desigualdad de Robertson–Schrödinger es una desigualdad:
la igualdad está permitida y queda caracterizada por el defect de Gram

`defectGramEn A B ψ = Var A · Var B − ‖⟨Ãψ, B̃ψ⟩‖² = Var A · Var B − (cov² + Im²)`.

* `defectGramEn_eq_zero_iff`: el defect se anula si y solo si `Var B = 0` o
  `Ãψ = c • B̃ψ` para algún `c : ℂ`.
* `saturacion_autovector`: si `ψ` es unitario y `(A − iλB)ψ = μψ` con `λ` real y
  `A`, `B` simétricos, entonces `cov = 0` y `Var A · Var B = Im²`.
* `autovector_no_maxima_tension`: para `d ≥ 4`, ningún autovector unitario de
  `T_d − iλP_d` es un estado de máxima tensión, `⟨K_d⟩ = 2/(d−1)`. Es la
  contraparte de `desigualdad_estricta_estado_maximo` (`D21`): la gap estricta
  es propia de esos estados, no de todo estado.
* `producto_varianzas_pos_of_K_ne_zero`: en todo estado con transporte, `⟨K_d⟩ ≠ 0`, la
  incertidumbre es estrictamente positiva: `Var T · Var P ≥ ⟨K_d⟩²/4 > 0`.
* `valor_esperado_conmutador_cero`, `no_conmutan_y_producto_cero`: si `Aψ = aψ`, entonces
  `⟨[A,B]⟩ = 0`. Así, los vectores de la base canónica, con `⟨K_d⟩ = 0`, tienen producto de
  varianzas `0` aunque `T_d` y `P_d` no conmutan; están fuera del dominio con transporte.
-/

noncomputable section

namespace SaturacionAutovectores

open NavaRobertsonSchrodingerEDUI TransportePosicion ConstructorEspectralTP

/-- Parte imaginaria `Im ⟨Ãψ, B̃ψ⟩`; para `A`, `B` simétricos,
`⟨ψ,[A,B]ψ⟩ = 2i · Im ⟨Ãψ, B̃ψ⟩`. -/
def parteImaginaria {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  (inner ℂ (centrado A ψ) (centrado B ψ)).im

/-- Defect de Gram de los vectores centrados: la gap de Robertson–Schrödinger. -/
def defectGramEn {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  varianza A ψ * varianza B ψ - ‖inner ℂ (centrado A ψ) (centrado B ψ)‖ ^ 2

/-! ## 1. El defect de Gram -/

theorem defectGramEn_eq_gap {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    defectGramEn A B ψ =
      varianza A ψ * varianza B ψ - (covarianza A B ψ ^ 2 + parteImaginaria A B ψ ^ 2) := by
  unfold defectGramEn covarianza parteImaginaria
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem defectGramEn_nonneg {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    0 ≤ defectGramEn A B ψ := by
  unfold defectGramEn varianza
  have h := norm_inner_le_norm (𝕜 := ℂ) (centrado A ψ) (centrado B ψ)
  have h2 : ‖inner ℂ (centrado A ψ) (centrado B ψ)‖ ^ 2 ≤
      (‖centrado A ψ‖ * ‖centrado B ψ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [h2]

/-- Si `Ãψ = c • B̃ψ`, el defect de Gram se anula. -/
theorem defectGramEn_eq_zero_of_aniquilado {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d)
    (c : ℂ) (h : centrado A ψ = c • centrado B ψ) : defectGramEn A B ψ = 0 := by
  unfold defectGramEn varianza
  rw [h, inner_smul_left, norm_smul, norm_mul, inner_self_eq_norm_sq_to_K]
  simp [mul_pow]
  ring

/-- El defect de Gram se anula si y solo si `B` no fluctúa en `ψ` o `Ãψ = c • B̃ψ`. -/
theorem defectGramEn_eq_zero_iff {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    defectGramEn A B ψ = 0 ↔
      varianza B ψ = 0 ∨ ∃ c : ℂ, centrado A ψ = c • centrado B ψ := by
  constructor
  · intro h
    unfold defectGramEn varianza at h
    rw [sub_eq_zero] at h
    have hn : ‖inner ℂ (centrado B ψ) (centrado A ψ)‖ = ‖centrado B ψ‖ * ‖centrado A ψ‖ := by
      rw [norm_inner_symm, mul_comm]
      exact ((sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp (by rw [mul_pow]; exact h)).symm
    rcases ((norm_inner_eq_norm_tfae ℂ _ _).out 1 3).mp hn with hw | ⟨r, hr⟩
    · left
      unfold varianza
      rw [hw, norm_zero]
      norm_num
    · exact Or.inr ⟨r, hr⟩
  · rintro (hb | ⟨c, hc⟩)
    · unfold varianza at hb
      have hw : centrado B ψ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
      unfold defectGramEn varianza
      rw [hw]
      simp
    · exact defectGramEn_eq_zero_of_aniquilado A B ψ c hc

/-! ## 2. Autovectores de `A − iλB` -/

theorem covarianza_eq_zero_of_aniquilado_imaginario {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d)
    (lam : ℝ) (h : centrado A ψ = (Complex.I * lam) • centrado B ψ) :
    covarianza A B ψ = 0 := by
  unfold covarianza
  rw [h, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Para `A` simétrico, `⟨ψ, Aψ⟩` es real. -/
theorem inner_simetrico_real {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} (hA : A.IsSymmetric) (ψ : Hd d) :
    inner ℂ ψ (A ψ) = ((media A ψ : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (inner ℂ ψ (A ψ)) = inner ℂ ψ (A ψ) := by
    rw [inner_conj_symm]
    exact hA ψ ψ
  exact (Complex.conj_eq_iff_re.mp h).symm

/-- Un autovector de `A − iλB` es aniquilado por `Ã − iλ B̃`. -/
theorem aniquilado_de_autovector {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : Hd d} (hψ : ‖ψ‖ = 1) (lam : ℝ) (μ : ℂ)
    (h : A ψ - (Complex.I * lam) • B ψ = μ • ψ) :
    centrado A ψ = (Complex.I * lam) • centrado B ψ := by
  have hμ : μ = (media A ψ : ℂ) - (Complex.I * lam) * (media B ψ : ℂ) := by
    have h1 : inner ℂ ψ (A ψ - (Complex.I * lam) • B ψ) = μ := by
      rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
      simp
    rw [← h1, inner_sub_right, inner_smul_right, inner_simetrico_real hA,
      inner_simetrico_real hB]
  have h2 : A ψ - (Complex.I * lam) • B ψ =
      ((media A ψ : ℂ) - (Complex.I * lam) * (media B ψ : ℂ)) • ψ := by
    rw [h, hμ]
  unfold centrado
  calc A ψ - (media A ψ : ℂ) • ψ
      = (A ψ - (Complex.I * lam) • B ψ) + (Complex.I * lam) • B ψ - (media A ψ : ℂ) • ψ := by
        abel
    _ = ((media A ψ : ℂ) - (Complex.I * lam) * (media B ψ : ℂ)) • ψ +
          (Complex.I * lam) • B ψ - (media A ψ : ℂ) • ψ := by rw [h2]
    _ = (Complex.I * lam) • (B ψ - (media B ψ : ℂ) • ψ) := by
        simp only [sub_smul, mul_smul, smul_sub]
        abel

/-- **Saturación en autovectores.** Si `ψ` es unitario y `(A − iλB)ψ = μψ` con `λ` real y
`A`, `B` simétricos, la covarianza se anula y la desigualdad de Robertson se cumple con
igualdad, `Var A · Var B = Im²`; en particular la de Robertson–Schrödinger. -/
theorem saturacion_autovector {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : Hd d} (hψ : ‖ψ‖ = 1) (lam : ℝ) (μ : ℂ)
    (h : A ψ - (Complex.I * lam) • B ψ = μ • ψ) :
    covarianza A B ψ = 0 ∧ varianza A ψ * varianza B ψ = parteImaginaria A B ψ ^ 2 := by
  have hc := aniquilado_de_autovector hA hB hψ lam μ h
  have hcov := covarianza_eq_zero_of_aniquilado_imaginario A B ψ lam hc
  have hg := defectGramEn_eq_zero_of_aniquilado A B ψ _ hc
  rw [defectGramEn_eq_gap, hcov] at hg
  exact ⟨hcov, by linarith⟩

/-! ## 3. Los autovectores de `T_d − iλP_d` no son estados de máxima tensión -/

/-- Para `A`, `B` simétricos, `Im ⟨Ãψ, B̃ψ⟩ = Im ⟨Aψ, Bψ⟩`: centrar solo resta términos reales. -/
theorem parteImaginaria_eq_im_inner {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : Hd d) :
    parteImaginaria A B ψ = (inner ℂ (A ψ) (B ψ)).im := by
  have ha : inner ℂ (A ψ) ψ = ((media A ψ : ℝ) : ℂ) := by
    rw [← inner_conj_symm (A ψ) ψ, inner_simetrico_real hA]
    simp
  have hb : inner ℂ ψ (B ψ) = ((media B ψ : ℝ) : ℂ) := inner_simetrico_real hB ψ
  have hn : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have key : inner ℂ (centrado A ψ) (centrado B ψ) =
      inner ℂ (A ψ) (B ψ) - ((media A ψ * media B ψ * (2 - ‖ψ‖ ^ 2) : ℝ) : ℂ) := by
    unfold centrado
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, ha, hb, hn,
      Complex.conj_ofReal]
    push_cast
    ring
  unfold parteImaginaria
  rw [key, Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- `Re ⟨ψ, K_d ψ⟩ = −2 · Im ⟨T_d ψ, P_d ψ⟩` para `K_d = i[T_d, P_d]`. -/
theorem re_inner_KdOp (d : ℕ) (ψ : Hd d) :
    (inner ℂ ψ (KdOp d ψ)).re = -2 * (inner ℂ (TdOp d ψ) (PdOp d ψ)).im := by
  have h1 : inner ℂ ψ (TdOp d (PdOp d ψ)) = inner ℂ (TdOp d ψ) (PdOp d ψ) :=
    (TdOp_simetrico d ψ (PdOp d ψ)).symm
  have h2 : inner ℂ ψ (PdOp d (TdOp d ψ)) = inner ℂ (PdOp d ψ) (TdOp d ψ) :=
    (PdOp_simetrico d ψ (TdOp d ψ)).symm
  have h3 : (inner ℂ (PdOp d ψ) (TdOp d ψ)).im = -(inner ℂ (TdOp d ψ) (PdOp d ψ)).im := by
    rw [← inner_conj_symm (PdOp d ψ) (TdOp d ψ), Complex.conj_im]
  unfold KdOp observableTension conmutador
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right,
    inner_sub_right, h1, h2]
  simp [Complex.mul_re, Complex.sub_im]
  linarith [h3]

/-- **Los autovectores de `T_d − iλP_d` no son estados de máxima tensión.** Para `d ≥ 4`, si
`ψ` es unitario y `(T_d − iλP_d)ψ = μψ` con `λ` real, entonces `⟨K_d⟩ ≠ 2/(d−1)`. En los
estados de máxima tensión la desigualdad de Robertson–Schrödinger es estricta
(`desigualdad_estricta_estado_maximo`); en estos autovectores es una igualdad. -/
theorem autovector_no_maxima_tension {d : ℕ} (hd : 4 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (lam : ℝ) (μ : ℂ) (h : TdOp d ψ - (Complex.I * lam) • PdOp d ψ = μ • ψ) :
    (inner ℂ ψ (KdOp d ψ)).re ≠ 2 / ((d : ℝ) - 1) := by
  intro hK
  obtain ⟨hcov, hprod⟩ := saturacion_autovector (TdOp_simetrico d) (PdOp_simetrico d) hψ lam μ h
  have hstrict := desigualdad_estricta_estado_maximo hd ψ hψ hK
  rw [hcov, hprod, parteImaginaria_eq_im_inner (TdOp_simetrico d) (PdOp_simetrico d)] at hstrict
  have hIm : (inner ℂ (TdOp d ψ) (PdOp d ψ)).im = -(1 / ((d : ℝ) - 1)) := by
    have h4 := re_inner_KdOp d ψ
    rw [hK, show 2 / ((d : ℝ) - 1) = 2 * (1 / ((d : ℝ) - 1)) by ring] at h4
    linarith
  rw [hIm, commutatorConstant_half_sq (by omega), show (-(1 / ((d : ℝ) - 1))) ^ 2 = 1 / ((d : ℝ) -
      1) ^ 2 by
    rw [neg_sq, div_pow, one_pow]] at hstrict
  simp at hstrict

/-! ## 4. Con transporte, incertidumbre positiva; vectores con `⟨K_d⟩ = 0` -/

/-- **Con transporte, incertidumbre positiva.** Para todo estado,
`Var T_d · Var P_d ≥ ⟨K_d⟩²/4`. -/
theorem producto_varianzas_ge_K (d : ℕ) (ψ : Hd d) :
    ((inner ℂ ψ (KdOp d ψ)).re) ^ 2 / 4 ≤ varianza (TdOp d) ψ * varianza (PdOp d) ψ := by
  have hg := defectGramEn_nonneg (TdOp d) (PdOp d) ψ
  rw [defectGramEn_eq_gap,
    parteImaginaria_eq_im_inner (TdOp_simetrico d) (PdOp_simetrico d)] at hg
  rw [re_inner_KdOp d ψ]
  nlinarith [sq_nonneg (covarianza (TdOp d) (PdOp d) ψ)]

/-- Si `⟨K_d⟩ ≠ 0` (hay transporte en el estado), el producto de varianzas es estrictamente
positivo: la incertidumbre no puede ser `0`. -/
theorem producto_varianzas_pos_of_K_ne_zero (d : ℕ) (ψ : Hd d)
    (h : (inner ℂ ψ (KdOp d ψ)).re ≠ 0) :
    0 < varianza (TdOp d) ψ * varianza (PdOp d) ψ :=
  lt_of_lt_of_le (by positivity) (producto_varianzas_ge_K d ψ)

/-- Un autovector unitario con autovalor real tiene vector centrado nulo. -/
theorem centrado_autovector {d : ℕ} {A : Hd d →ₗ[ℂ] Hd d} {ψ : Hd d} (hψ : ‖ψ‖ = 1) (a : ℝ)
    (h : A ψ = (a : ℂ) • ψ) : centrado A ψ = 0 := by
  have hm : media A ψ = a := by
    unfold media
    rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp
  unfold centrado
  rw [hm, h, sub_self]

/-- Si `A ψ = a ψ` con `A` simétrico y `a` real, entonces `⟨ψ, [A,B] ψ⟩ = 0` para todo `B`. La
contrapositiva: si `⟨[A,B]⟩ ≠ 0`, `ψ` no es autovector de `A`. -/
theorem valor_esperado_conmutador_cero {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (hA : A.IsSymmetric)
    {ψ : Hd d} (a : ℝ) (h : A ψ = (a : ℂ) • ψ) :
    inner ℂ ψ (A (B ψ) - B (A ψ)) = 0 := by
  have h1 : inner ℂ ψ (A (B ψ)) = inner ℂ (A ψ) (B ψ) := (hA ψ (B ψ)).symm
  rw [inner_sub_right, h1, h, inner_smul_left, map_smul, inner_smul_right]
  simp

/-- Cada vector de la base canónica es autovector de la posición `P_d`. -/
theorem Pd_base (d : ℕ) (j : Fin d) :
    PdOp d (EuclideanSpace.single j 1) =
      ((posicionCoord d j : ℝ) : ℂ) • (EuclideanSpace.single j (1 : ℂ) : Hd d) := by
  ext i
  simp [PdOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Pd]
  by_cases h : i = j <;> simp [h]

/-- En cada vector de la base canónica, `Var P_d = 0` y el defect de Gram es `0`. -/
theorem estado_base_satura (d : ℕ) (j : Fin d) :
    varianza (PdOp d) (EuclideanSpace.single j 1) = 0 ∧
      defectGramEn (TdOp d) (PdOp d) (EuclideanSpace.single j 1) = 0 := by
  have hn : ‖(EuclideanSpace.single j (1 : ℂ) : Hd d)‖ = 1 := by simp
  have hc := centrado_autovector hn (posicionCoord d j) (Pd_base d j)
  have hv : varianza (PdOp d) (EuclideanSpace.single j 1) = 0 := by
    unfold varianza
    rw [hc]
    simp
  exact ⟨hv, (defectGramEn_eq_zero_iff _ _ _).mpr (Or.inl hv)⟩

/-- `T_d` y `P_d` no conmutan y, aun así, existe un vector unitario, con `⟨K_d⟩ = 0`, en el que
el producto de varianzas es `0`. Está fuera del dominio con transporte de
`producto_varianzas_pos_of_K_ne_zero`. -/
theorem no_conmutan_y_producto_cero (d : ℕ) (hd : 2 ≤ d) :
    conmutador (TdOp d) (PdOp d) ≠ 0 ∧
      ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ varianza (TdOp d) ψ * varianza (PdOp d) ψ = 0 := by
  constructor
  · intro hC
    have hK : KdOp d = 0 := by
      unfold KdOp observableTension
      rw [hC, smul_zero]
    have h1 := KdOp_vectorFiedlerExplicito d hd
    rw [hK, LinearMap.zero_apply] at h1
    have hn := norma_psiStar hd
    have h2 : ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) = 0 ∨ vectorFiedlerExplicito d = 0 :=
      smul_eq_zero.mp h1.symm
    rcases h2 with h2 | h2
    · have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have : (2 / ((d : ℝ) - 1) : ℝ) = 0 := by exact_mod_cast h2
      have hpos : (0 : ℝ) < 2 / ((d : ℝ) - 1) := div_pos (by norm_num) hd1
      linarith
    · have : ‖psiStar d‖ = 0 := by
        change ‖vectorFiedlerExplicito d‖ = 0
        rw [h2, norm_zero]
      linarith
  · let j : Fin d := ⟨0, by omega⟩
    refine ⟨EuclideanSpace.single j 1, by simp, ?_⟩
    rw [(estado_base_satura d j).1, mul_zero]

end SaturacionAutovectores

end

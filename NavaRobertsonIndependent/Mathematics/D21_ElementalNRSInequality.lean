import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
import NavaRobertsonIndependent.Mathematics.D6_Fiedler
import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# D21 — Nava–Robertson–Schrödinger: Elemental Dimensional Uncertainty Inequality

Sobre las matrices concretas `T_d` (transporte) y `P_d` (posición) del grafo
camino y el estado de máxima tensión `ψ* = ψ_d` (modo fundamental de Fiedler con
fase `(−i)^j`), con `K_d = i[T_d, P_d]` y `c = −2/(d−1)`:

* `cov(T_d, P_d) = 0` y las medias son nulas en `ψ*`;
* `Var T_d · Var P_d = (c/2)² · (1 + δ_geom d)²` (igualdad exacta);
* la gap de Robertson–Schrödinger
  `Var T · Var P − (cov² + (c/2)²) = (c/2)² · δ_geom(d) · (2 + δ_geom(d))`
  es el defect de Gram `(C_Nava(d)² − 1)/(d−1)²`;
* la gap es `0` exactamente en `d = 2, 3` y `> 0` desde `d = 4`;
* el autovalor superior `2/(d−1)` de `K_d` es simple, de modo que todo estado
  unitario con `⟨K_d⟩ = 2/(d−1)` es una fase de `ψ*`, y la desigualdad es
  estricta en **todo** estado de máxima tensión.

Media, varianza y covarianza se definen aquí sobre vectores centrados,
`Var_ψ(A) = ‖Aψ − ⟨A⟩ψ‖²` y `cov_ψ(A,B) = Re ⟨Ãψ, B̃ψ⟩`, con `⟨A⟩ = Re ⟨ψ, Aψ⟩`.
-/

noncomputable section

namespace Gnomon

theorem CoherenceConstant_eq_one_add_geometricGap (d : ℕ) : CoherenceConstant d = 1 + geometricGap d
    := by
  unfold geometricGap
  ring

end Gnomon

open Gnomon TransportePosicion RNavaVarianzaFiedler EscalonGramCoherenceConstant
    ConstructorEspectralTP

namespace NavaRobertsonSchrodingerEDUI

/-- El estado de máxima tensión `ψ*`: modo fundamental de Fiedler explícito. -/
abbrev psiStar (d : ℕ) : Hd d := vectorFiedlerExplicito d

/-- Valor esperado `Re ⟨ψ, Aψ⟩`. -/
def media {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  (inner ℂ ψ (A ψ)).re

/-- Vector centrado `Aψ − ⟨A⟩ψ`. -/
def centrado {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : Hd d :=
  A ψ - (media A ψ : ℂ) • ψ

/-- Varianza `‖Aψ − ⟨A⟩ψ‖²`. -/
def varianza {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  ‖centrado A ψ‖ ^ 2

/-- Covarianza `Re ⟨Ãψ, B̃ψ⟩`. -/
def covarianza {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  (inner ℂ (centrado A ψ) (centrado B ψ)).re

/-- `c` con `⟨ψ*,[T_d,P_d]ψ*⟩ = i·c`. -/
def commutatorConstant (d : ℕ) : ℝ := -(2 / ((d : ℝ) - 1))

theorem commutatorConstant_half_sq {d : ℕ} (hd : 2 ≤ d) : (commutatorConstant d / 2) ^ 2 = 1 / ((d :
    ℝ) - 1) ^ 2 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  unfold commutatorConstant
  field_simp

theorem commutatorConstant_half_sq_pos {d : ℕ} (hd : 2 ≤ d) : 0 < (commutatorConstant d / 2) ^ 2 :=
    by
  rw [commutatorConstant_half_sq hd]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  exact one_div_pos.mpr (pow_pos h1 2)

/-! ## 1. Medias, varianzas y covarianza en `ψ*` -/

theorem media_T {d : ℕ} (hd : 2 ≤ d) : media (TdOp d) (psiStar d) = 0 := by
  have h := escalon_media_T hd
  simp [media, h]

theorem media_P {d : ℕ} (hd : 2 ≤ d) : media (PdOp d) (psiStar d) = 0 := by
  have h := escalon_media_P hd
  simp [media, h]

theorem norma_psiStar {d : ℕ} (hd : 2 ≤ d) : ‖psiStar d‖ = 1 :=
  vectorFiedlerExplicito_normalizado d (by omega)

theorem centrado_T {d : ℕ} (hd : 2 ≤ d) :
    centrado (TdOp d) (psiStar d) = TdOp d (psiStar d) := by
  simp [centrado, media_T hd]

theorem centrado_P {d : ℕ} (hd : 2 ≤ d) :
    centrado (PdOp d) (psiStar d) = PdOp d (psiStar d) := by
  simp [centrado, media_P hd]

theorem varianza_T {d : ℕ} (hd : 2 ≤ d) :
    varianza (TdOp d) (psiStar d) = ‖TdOp d (psiStar d)‖ ^ 2 := by
  unfold varianza
  rw [centrado_T hd]

theorem varianza_P {d : ℕ} (hd : 2 ≤ d) :
    varianza (PdOp d) (psiStar d) = ‖PdOp d (psiStar d)‖ ^ 2 := by
  unfold varianza
  rw [centrado_P hd]

theorem covarianza_cero {d : ℕ} (hd : 2 ≤ d) :
    covarianza (TdOp d) (PdOp d) (psiStar d) = 0 := by
  unfold covarianza
  rw [centrado_T hd, centrado_P hd]
  exact escalon_cruzado_re hd

/-! ## 2. Igualdad exacta con `δ_geom` y gap -/

theorem CoherenceConstantSq_eq_sq {d : ℕ} (hd : 2 ≤ d) : CoherenceConstantSq d = (1 + geometricGap
    d) ^ 2 := by
  have h0 : 0 ≤ CoherenceConstantSq d := by
    rw [← escalon_producto hd]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [← CoherenceConstant_eq_one_add_geometricGap, CoherenceConstant, Real.sq_sqrt h0]

/-- **Igualdad exacta.** `Var T_d · Var P_d = (c/2)² · (1 + δ_geom d)²`. -/
theorem producto_varianzas {d : ℕ} (hd : 2 ≤ d) :
    varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d) =
      (commutatorConstant d / 2) ^ 2 * (1 + geometricGap d) ^ 2 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  rw [varianza_T hd, varianza_P hd, commutatorConstant_half_sq hd, ← CoherenceConstantSq_eq_sq hd, ←
      escalon_producto hd]
  field_simp

/-- Gap de Robertson–Schrödinger en función de `δ_geom`. -/
theorem gap_eq_geometricGap {d : ℕ} (hd : 2 ≤ d) :
    varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d) -
      (covarianza (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2) =
      (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) := by
  rw [producto_varianzas hd, covarianza_cero hd]
  ring

/-- La gap es el defect de Gram `(C_Nava(d)² − 1)/(d−1)²`. -/
theorem gap_eq_defectGram {d : ℕ} (hd : 2 ≤ d) :
    varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d) -
      (covarianza (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2) =
      defectGram d := by
  rw [escalon_gram hd, gap_eq_geometricGap hd, commutatorConstant_half_sq hd,
      CoherenceConstantSq_eq_sq hd]
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  field_simp
  ring

/-! ## 3. Saturación en `d = 2, 3`; desigualdad estricta desde `d = 4` -/

theorem geometricGap_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ geometricGap d := by
  unfold geometricGap
  have h1 : 1 ≤ CoherenceConstant d := by
    unfold CoherenceConstant
    rw [Real.one_le_sqrt]
    rcases Nat.lt_or_ge d 4 with h4 | h4
    · rcases (by omega : d = 2 ∨ d = 3) with rfl | rfl
      · rw [CoherenceConstantSq_two]
      · rw [CoherenceConstantSq_three]
    · exact (one_lt_CoherenceConstantSq d h4).le
  linarith

/-- Saturación de Robertson–Schrödinger en `ψ*` exactamente para `d = 2, 3`. -/
theorem saturacion_iff {d : ℕ} (hd : 2 ≤ d) :
    covarianza (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2 =
        varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d) ↔ d = 2 ∨ d = 3 := by
  have hb := gap_eq_geometricGap hd
  have hp := commutatorConstant_half_sq_pos hd
  have hδ : 0 ≤ geometricGap d := geometricGap_nonneg hd
  rw [← CoherenceConstant_eq_one_iff d hd, CoherenceConstant_eq_one_add_geometricGap, add_eq_left]
  constructor
  · intro h
    have h0 : (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) = 0 := by
      rw [← hb]
      linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hp.ne'
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · linarith
  · intro h
    rw [h] at hb
    linarith

/-- **Nava–Robertson–Schrödinger: Elemental Dimensional Uncertainty Inequality.**
Para `d ≥ 4`, en `ψ*`, la desigualdad de Robertson–Schrödinger es estricta:
`cov² + (c/2)² < Var T_d · Var P_d`, con gap `(c/2)² · δ_geom(d) · (2 + δ_geom(d)) > 0`. -/
theorem desigualdad_estricta {d : ℕ} (hd : 4 ≤ d) :
    covarianza (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2 <
      varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d) := by
  have hd2 : 2 ≤ d := by omega
  have hδ := geometricGap_pos_of_four_le d hd
  have hp := commutatorConstant_half_sq_pos hd2
  have h := gap_eq_geometricGap hd2
  have : 0 < (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) :=
    mul_pos hp (mul_pos hδ (by linarith))
  linarith

/-! ## 4. Unicidad del estado de máxima tensión -/

/-- El autovalor superior de `K_d` es simple: su autoespacio lo genera `ψ*`. -/
theorem autovector_superior_multiplo {d : ℕ} (hd : 2 ≤ d) (v : Hd d)
    (hv : KdOp d v = ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • v) :
    ∃ c : ℂ, v = c • psiStar d := by
  classical
  have hd1 : 1 ≤ d := by omega
  let k0 : Fin d := ⟨0, by omega⟩
  have hres : ∀ k : Fin d, k ≠ k0 → (baseModosFaseHd hd).repr v k = 0 := by
    intro k hk
    have h1 := repr_KdOp hd v k
    rw [hv, map_smul, Finsupp.smul_apply, smul_eq_mul, ← autovalorK_fundamental d hd] at h1
    have h2 : (autovalorK d k0 - autovalorK d k) * (baseModosFaseHd hd).repr v k = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (autovalorK_injective hd (sub_eq_zero.mp h)).symm hk
    · exact h
  have hsum : v = (baseModosFaseHd hd).repr v k0 • baseModosFaseHd hd k0 := by
    conv_lhs => rw [← (baseModosFaseHd hd).sum_repr v]
    rw [Finset.sum_eq_single k0]
    · intro k _ hk
      rw [hres k hk, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ k0) h
  rw [baseModosFaseHd_apply, modoFaseHd_fundamental_eq_vectorFiedlerCrudo d hd] at hsum
  have hn : (‖vectorFiedlerCrudo d‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (vectorFiedlerCrudo_ne_zero d hd1))
  refine ⟨(baseModosFaseHd hd).repr v k0 * ‖vectorFiedlerCrudo d‖, hsum.trans ?_⟩
  show _ • vectorFiedlerCrudo d =
    _ • ((‖vectorFiedlerCrudo d‖ : ℂ)⁻¹ • vectorFiedlerCrudo d)
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]

/-- Un estado unitario cuya esperanza de `K_d` alcanza el máximo `2/(d−1)` es una
fase de `ψ*`. -/
theorem estado_maxima_tension_es_fase {d : ℕ} (hd : 2 ≤ d) (v : Hd d) (hv : ‖v‖ = 1)
    (h : (inner ℂ v (KdOp d v)).re = 2 / ((d : ℝ) - 1)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • psiStar d := by
  have hd1 : 1 ≤ d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  let T : Hd d →L[ℂ] Hd d := LinearMap.toContinuousLinearMap (KdOp d)
  have hT : IsSelfAdjoint T :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr (KdOp_simetrico d)
  have hTv : ∀ x, T x = KdOp d x := fun x => rfl
  have hmax : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : Hd d) ‖v‖) v := by
    rw [isMaxOn_iff]
    intro x hx
    have hx' : ‖x‖ = 1 := by simpa [hv] using hx
    have hle := expectativa_le_radio (KdOp d) (KdOp_simetrico d) x hx'
    rw [radioEspectral_KdOp_eq_paso d hd] at hle
    have hre : (inner ℂ (KdOp d x) x).re = (inner ℂ x (KdOp d x)).re := by
      rw [← inner_conj_symm x (KdOp d x), Complex.conj_re]
    have hre_v : (inner ℂ (KdOp d v) v).re = 2 / ((d : ℝ) - 1) := by
      rw [← h, ← inner_conj_symm v (KdOp d v), Complex.conj_re]
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply, hTv, RCLike.re_to_complex]
    rw [hre, hre_v]
    exact (Complex.re_le_norm _).trans hle
  have hK : T v = ((T.rayleighQuotient v : ℝ) : ℂ) • v :=
    hT.eq_smul_self_of_isLocalExtrOn (Or.inr hmax.localize)
  have hray : T.rayleighQuotient v = 2 / ((d : ℝ) - 1) := by
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      hTv, hv, RCLike.re_to_complex]
    rw [← h, ← inner_conj_symm v (KdOp d v), Complex.conj_re]
    simp
  rw [hray, hTv] at hK
  obtain ⟨c, hc⟩ := autovector_superior_multiplo hd v hK
  refine ⟨c, ?_, hc⟩
  have := congrArg norm hc
  rwa [hv, norm_smul, vectorFiedlerExplicito_normalizado d hd1, mul_one, eq_comm] at this

/-! ## 5. Invariancia de fase y desigualdad estricta en todo estado de máxima tensión -/

theorem media_fase {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    media A (c • ψ) = media A ψ := by
  simp only [media, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, Complex.mul_conj', hc]
  simp

theorem centrado_fase {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    centrado A (c • ψ) = c • centrado A ψ := by
  unfold centrado
  rw [media_fase A ψ c hc]
  simp only [map_smul]
  module

theorem varianza_fase {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    varianza A (c • ψ) = varianza A ψ := by
  unfold varianza
  rw [centrado_fase A ψ c hc, norm_smul, hc, one_mul]

theorem covarianza_fase {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    covarianza A B (c • ψ) = covarianza A B ψ := by
  unfold covarianza
  rw [centrado_fase A ψ c hc, centrado_fase B ψ c hc, inner_smul_left, inner_smul_right,
    ← mul_assoc, Complex.conj_mul', hc]
  simp

/-- **Desigualdad elemental en todo estado de máxima tensión.** Para `d ≥ 4`, todo
estado unitario que alcanza la cota más fuerte, `⟨K_d⟩ = 2/(d−1)`, satisface la
desigualdad de Robertson–Schrödinger de forma estricta: no solo `ψ*`. -/
theorem desigualdad_estricta_estado_maximo {d : ℕ} (hd : 4 ≤ d) (v : Hd d) (hv : ‖v‖ = 1)
    (h : (inner ℂ v (KdOp d v)).re = 2 / ((d : ℝ) - 1)) :
    covarianza (TdOp d) (PdOp d) v ^ 2 + (commutatorConstant d / 2) ^ 2 <
      varianza (TdOp d) v * varianza (PdOp d) v := by
  obtain ⟨c, hc, rfl⟩ := estado_maxima_tension_es_fase (by omega) v hv h
  rw [covarianza_fase _ _ _ _ hc, varianza_fase _ _ _ hc, varianza_fase _ _ _ hc]
  exact desigualdad_estricta hd

end NavaRobertsonSchrodingerEDUI

end

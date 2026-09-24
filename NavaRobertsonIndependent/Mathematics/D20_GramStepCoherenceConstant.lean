import NavaRobertsonIndependent.Mathematics.D19_FiedlerPositionVariance
import NavaRobertsonIndependent.Mathematics.D6_Fiedler
import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# Escalón: defect de Gram de `(T_d ψ, P_d ψ)` y `C_Nava(d)²`

Módulo de álgebra pura sobre `H_d = ℂ^d`. Une dos cosas que en el corpus
estaban separadas:

* la fórmula cerrada `CoherenceConstantSq d` (y con ella `δ_geom d = C_Nava d - 1`);
* las matrices concretas `T_d`, `P_d` y el vector explícito
  `ψ = vectorFiedlerExplicito d`.

Resultado central (`escalon_producto`), para `d ≥ 2`:

`(d-1)² · ‖T_d ψ‖² · ‖P_d ψ‖² = CoherenceConstantSq d`.

Con `⟨T_d ψ, P_d ψ⟩` de parte real nula y parte imaginaria `-1/(d-1)`
(`escalon_cruzado_re`, `escalon_cruzado_im`) el defect de Gram del par vale
`(CoherenceConstantSq d - 1)/(d-1)²` (`escalon_gram`). Las medias `⟨ψ, T_d ψ⟩` y
`⟨ψ, P_d ψ⟩` son nulas (`escalon_media_T`, `escalon_media_P`), de modo que ese
defect es el centrado. Por tanto se anula exactamente en `d = 2, 3`
(`escalon_gram_eq_zero_iff`) y es estrictamente positivo desde `d = 4`
(`escalon_gram_pos`).

No se introduce ninguna definición nueva sobre los operadores: todo se
demuestra sobre `TdOp`, `PdOp`, `KdOp` y `vectorFiedlerExplicito` ya
existentes.
-/

noncomputable section

namespace Gnomon

/-- `C_Nava(d) = 1` exactamente en las seeds `d = 2, 3` (dimensiones `≥ 2`). -/
theorem CoherenceConstant_eq_one_iff (d : ℕ) (hd : 2 ≤ d) : CoherenceConstant d = 1 ↔ d = 2 ∨ d = 3 := by
  constructor
  · intro h
    by_contra hne
    have h4 : 4 ≤ d := by omega
    have hpos := geometricGap_pos_of_four_le d h4
    unfold geometricGap at hpos
    linarith
  · rintro (rfl | rfl)
    · unfold CoherenceConstant
      rw [CoherenceConstantSq_two]
      exact Real.sqrt_one
    · unfold CoherenceConstant
      rw [CoherenceConstantSq_three]
      exact Real.sqrt_one

end Gnomon

open Gnomon TransportePosicion RNavaVarianzaFiedler

namespace EscalonGramCoherenceConstant

/-! ## 1. Acción de las matrices sobre coordenadas -/

theorem TdOp_apply (d : ℕ) (x : Hd d) :
    TdOp d x = WithLp.toLp 2 ((Td d).mulVec x.ofLp) :=
  Matrix.toLpLin_apply 2 2 (Td d) x

theorem PdOp_apply (d : ℕ) (x : Hd d) :
    PdOp d x = WithLp.toLp 2 ((Pd d).mulVec x.ofLp) :=
  Matrix.toLpLin_apply 2 2 (Pd d) x

theorem Td_mulVec (d : ℕ) (f : Fin d → ℂ) (i : Fin d) :
    (Td d).mulVec f i = (Ad d).mulVec f i / (rho d : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, Td, div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem Pd_mulVec (d : ℕ) (f : Fin d → ℂ) (i : Fin d) :
    (Pd d).mulVec f i = (posicionCoord d i : ℂ) * f i := by
  simp [Matrix.mulVec, dotProduct, Pd]

/-! ## 2. Coordenadas del modo crudo -/

/-- Coordenadas del vector de Fiedler sin normalizar. -/
def cf (d : ℕ) (j : Fin d) : ℂ :=
  (-Complex.I) ^ j.val * (Real.sin (((j.val : ℝ) + 1) * theta d) : ℂ)

theorem crudo_ofLp (d : ℕ) : (vectorFiedlerCrudo d).ofLp = cf d := by
  funext j
  have h : (vectorFiedlerCrudo d).ofLp j =
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) * anguloFiedler d) : ℂ) := rfl
  rw [h, anguloFiedler_eq_theta]
  rfl

theorem sin_sub_sin_two (θ : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + 2) * θ) - Real.sin ((n : ℝ) * θ) =
      2 * Real.sin θ * Real.cos (((n : ℝ) + 1) * θ) := by
  rw [show ((n : ℝ) + 2) * θ = ((n : ℝ) + 1) * θ + θ by ring,
    show (n : ℝ) * θ = ((n : ℝ) + 1) * θ - θ by ring, Real.sin_add, Real.sin_sub]
  ring

theorem sin_theta_pos {d : ℕ} (hd : 1 ≤ d) : 0 < Real.sin (theta d) := by
  have h1 : 0 < theta d := theta_pos d
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : theta d < Real.pi := by
    unfold theta Nreal
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < d)]
  exact Real.sin_pos_of_pos_of_lt_pi h1 h2

theorem cos_theta_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Real.cos (theta d) := by
  have h1 : 0 < theta d := theta_pos d
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : theta d < Real.pi / 2 := by
    unfold theta Nreal
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩

theorem sin_frontera (d : ℕ) : Real.sin (((d : ℝ) + 1) * theta d) = 0 := by
  have : ((d : ℝ) + 1) * theta d = Real.pi := by
    unfold theta Nreal
    field_simp
  rw [this, Real.sin_pi]

/-- La adyacencia actúa sobre el modo de fase como `(-i)^(j+1) · 2 sin θ cos((j+1)θ)`. -/
theorem Ad_cf_apply (d : ℕ) (i : Fin d) :
    (Ad d).mulVec (cf d) i =
      (-Complex.I) ^ (i.val + 1) *
        ((2 * Real.sin (theta d) * Real.cos (((i.val : ℝ) + 1) * theta d) : ℝ) : ℂ) := by
  rw [Ad_mulVec_apply]
  have hup : (if h : i.val + 1 < d then cf d ⟨i.val + 1, h⟩ else 0) =
      (-Complex.I) ^ (i.val + 1) * (Real.sin (((i.val : ℝ) + 2) * theta d) : ℂ) := by
    by_cases h : i.val + 1 < d
    · simp only [h, dite_true, cf]
      have : ((((i.val + 1 : ℕ) : ℝ)) + 1) = (i.val : ℝ) + 2 := by push_cast; ring
      simp only [this]
    · have hid : i.val + 1 = d := by omega
      have hr : (i.val : ℝ) + 2 = (d : ℝ) + 1 := by
        have := congrArg (Nat.cast (R := ℝ)) hid
        push_cast at this
        linarith
      simp only [h, dite_false]
      rw [hr, sin_frontera]
      simp
  have hdown : (if h : 0 < i.val then cf d ⟨i.val - 1, by omega⟩ else 0) =
      -((-Complex.I) ^ (i.val + 1) * (Real.sin ((i.val : ℝ) * theta d) : ℂ)) := by
    by_cases h : 0 < i.val
    · obtain ⟨m, hm⟩ : ∃ m, i.val = m + 1 := ⟨i.val - 1, by omega⟩
      simp only [h, dite_true, cf]
      have hm' : i.val - 1 = m := by omega
      have hcast : (((i.val - 1 : ℕ) : ℝ)) + 1 = (i.val : ℝ) := by
        rw [hm']
        have := congrArg (Nat.cast (R := ℝ)) hm
        push_cast at this ⊢
        linarith
      simp only [hm']
      rw [hm]
      have hI : (-Complex.I) ^ 2 = -1 := by simp [pow_two]
      rw [pow_succ, pow_succ, mul_assoc ((-Complex.I) ^ m), ← pow_two, hI]
      push_cast
      ring
    · have h0 : i.val = 0 := by omega
      simp [h0]
  rw [hup, hdown]
  have hc := sin_sub_sin_two (theta d) i.val
  have hc' : (Real.sin (((i.val : ℝ) + 2) * theta d) : ℂ) -
      (Real.sin ((i.val : ℝ) * theta d) : ℂ) =
        ((2 * Real.sin (theta d) * Real.cos (((i.val : ℝ) + 1) * theta d) : ℝ) : ℂ) := by
    rw [← hc]
    push_cast
    ring
  linear_combination ((-Complex.I) ^ (i.val + 1)) * hc'

theorem Td_cf_apply {d : ℕ} (hd : 2 ≤ d) (i : Fin d) :
    (Td d).mulVec (cf d) i =
      (-Complex.I) ^ (i.val + 1) *
        ((Real.tan (theta d) * Real.cos (((i.val : ℝ) + 1) * theta d) : ℝ) : ℂ) := by
  rw [Td_mulVec, Ad_cf_apply]
  have hrho : rho d = 2 * Real.cos (theta d) := by
    unfold rho theta Nreal
    rfl
  have hcos : Real.cos (theta d) ≠ 0 := (cos_theta_pos hd).ne'
  rw [hrho, Real.tan_eq_sin_div_cos]
  push_cast
  field_simp

/-! ## 3. Normas -/

theorem norm_ofLp_sq_of_phase (i : ℕ) (r : ℝ) :
    ‖(-Complex.I) ^ i * (r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem sum_sin_sq_fin {d : ℕ} (hd : 1 ≤ d) :
    ∑ i : Fin d, Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2 = ((d : ℝ) + 1) / 2 := by
  have h1 := crudo_normSq_eq_sum d
  rw [sin_sq_sum_eq d hd, EuclideanSpace.norm_sq_eq] at h1
  simp_rw [vectorFiedlerCrudo_norm_sq] at h1
  exact h1.symm ▸ rfl

theorem sum_cos_sq_fin {d : ℕ} (hd : 1 ≤ d) :
    ∑ i : Fin d, Real.cos (((i.val : ℝ) + 1) * theta d) ^ 2 = ((d : ℝ) - 1) / 2 := by
  have h := sum_sin_sq_fin hd
  have hc : ∀ i : Fin d, Real.cos (((i.val : ℝ) + 1) * theta d) ^ 2 =
      1 - Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2 := fun i => Real.cos_sq' _
  simp_rw [hc, Finset.sum_sub_distrib, h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem norm_crudo_sq {d : ℕ} (hd : 1 ≤ d) :
    ‖vectorFiedlerCrudo d‖ ^ 2 = ((d : ℝ) + 1) / 2 := by
  rw [crudo_normSq_eq_sum, sin_sq_sum_eq d hd]

theorem norm_sq_Td_crudo {d : ℕ} (hd : 2 ≤ d) :
    ‖TdOp d (vectorFiedlerCrudo d)‖ ^ 2 = Real.tan (theta d) ^ 2 * (((d : ℝ) - 1) / 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  have hcoord : ∀ i : Fin d, ‖(TdOp d (vectorFiedlerCrudo d)).ofLp i‖ ^ 2 =
      Real.tan (theta d) ^ 2 * Real.cos (((i.val : ℝ) + 1) * theta d) ^ 2 := by
    intro i
    rw [TdOp_apply, WithLp.ofLp_toLp, crudo_ofLp, Td_cf_apply hd i, norm_ofLp_sq_of_phase,
      mul_pow]
  simp_rw [hcoord]
  rw [← Finset.mul_sum, sum_cos_sq_fin (by omega)]

theorem norm_sq_Td_psi {d : ℕ} (hd : 2 ≤ d) :
    ‖TdOp d (vectorFiedlerExplicito d)‖ ^ 2 =
      Real.tan (theta d) ^ 2 * (((d : ℝ) - 1) / ((d : ℝ) + 1)) := by
  have hn := norm_crudo_sq (d := d) (by omega)
  rw [vectorFiedlerExplicito, map_smul, norm_smul, mul_pow, norm_inv, Complex.norm_real,
    norm_norm, inv_pow, hn, norm_sq_Td_crudo hd]
  have : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem norm_sq_Pd_psi {d : ℕ} (hd : 2 ≤ d) :
    ‖PdOp d (vectorFiedlerExplicito d)‖ ^ 2 = RNavaSq d := by
  rw [RNavaSq_eq_varianzaFin d hd, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [PdOp_apply, WithLp.ofLp_toLp, Pd_mulVec, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, mul_comm]

/-- **Escalón.** `(d-1)² · ‖T_d ψ‖² · ‖P_d ψ‖² = C_Nava(d)²`, sobre las matrices
concretas y el vector de Fiedler explícito. -/
theorem escalon_producto {d : ℕ} (hd : 2 ≤ d) :
    ((d : ℝ) - 1) ^ 2 *
        (‖TdOp d (vectorFiedlerExplicito d)‖ ^ 2 * ‖PdOp d (vectorFiedlerExplicito d)‖ ^ 2) =
      CoherenceConstantSq d := by
  rw [norm_sq_Td_psi hd, norm_sq_Pd_psi hd, RNavaSq_eq d hd]
  have hs : Real.sin (theta d) ≠ 0 := (sin_theta_pos (by omega)).ne'
  have hc : Real.cos (theta d) ≠ 0 := (cos_theta_pos hd).ne'
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  have hd2 : (d : ℝ) + 1 ≠ 0 := by positivity
  unfold CoherenceConstantSq Nreal
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## 4. Producto cruzado `⟨T_d ψ, P_d ψ⟩` -/

theorem cruz_term {d : ℕ} (hd : 2 ≤ d) (i : Fin d) :
    inner ℂ ((TdOp d (vectorFiedlerCrudo d)).ofLp i) ((PdOp d (vectorFiedlerCrudo d)).ofLp i) =
      Complex.I *
        ((posicionCoord d i * Real.sin (((i.val : ℝ) + 1) * theta d) *
          (Real.tan (theta d) * Real.cos (((i.val : ℝ) + 1) * theta d)) : ℝ) : ℂ) := by
  simp only [TdOp_apply, PdOp_apply, WithLp.ofLp_toLp, crudo_ofLp]
  rw [Td_cf_apply hd i, Pd_mulVec, RCLike.inner_apply]
  have hII : ((-Complex.I) ^ i.val) * (Complex.I ^ i.val) = 1 := by
    rw [← mul_pow]
    simp
  have hconj : (starRingEnd ℂ) ((-Complex.I) ^ (i.val + 1)) = Complex.I ^ (i.val + 1) := by
    rw [map_pow]
    simp
  rw [map_mul, hconj, Complex.conj_ofReal]
  simp only [cf]
  generalize posicionCoord d i = p
  generalize Real.sin (((i.val : ℝ) + 1) * theta d) = sn
  generalize Real.tan (theta d) = t
  generalize Real.cos (((i.val : ℝ) + 1) * theta d) = c
  push_cast
  rw [pow_succ Complex.I]
  linear_combination (Complex.I * (p : ℂ) * (sn : ℂ) * (t : ℂ) * (c : ℂ)) * hII

theorem cruzado_crudo_re {d : ℕ} (hd : 2 ≤ d) :
    (inner ℂ (TdOp d (vectorFiedlerCrudo d)) (PdOp d (vectorFiedlerCrudo d))).re = 0 := by
  rw [PiLp.inner_apply]
  simp_rw [cruz_term hd]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, Complex.I_mul_re, Complex.ofReal_im, neg_zero]

/-- La parte real del producto cruzado es nula (covarianza nula). -/
theorem escalon_cruzado_re {d : ℕ} (hd : 2 ≤ d) :
    (inner ℂ (TdOp d (vectorFiedlerExplicito d)) (PdOp d (vectorFiedlerExplicito d))).re = 0 := by
  have hcr := cruzado_crudo_re hd
  rw [vectorFiedlerExplicito, map_smul, map_smul, inner_smul_left, inner_smul_right,
    ← mul_assoc]
  set r : ℂ := ((‖vectorFiedlerCrudo d‖ : ℝ) : ℂ)⁻¹ with hr
  have hrr : (starRingEnd ℂ) r * r = ((((‖vectorFiedlerCrudo d‖ : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [hr, map_inv₀, Complex.conj_ofReal]
    push_cast
    ring
  rw [hrr, Complex.re_ofReal_mul, hcr]
  ring

/-! ## 5. Parte imaginaria vía el autovalor de `K = i[T_d,P_d]` -/

theorem escalon_cruzado_im {d : ℕ} (hd : 2 ≤ d) :
    (inner ℂ (TdOp d (vectorFiedlerExplicito d)) (PdOp d (vectorFiedlerExplicito d))).im =
      -(1 / ((d : ℝ) - 1)) := by
  set ψ := vectorFiedlerExplicito d with hψ
  set z := inner ℂ (TdOp d ψ) (PdOp d ψ) with hz
  have hK := KdOp_vectorFiedlerExplicito d hd
  have hn : ‖ψ‖ = 1 := vectorFiedlerExplicito_normalizado d (by omega)
  have h1 : inner ℂ ψ (KdOp d ψ) = ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
    rw [hK, inner_smul_right, inner_self_eq_norm_sq_to_K, hn]
    simp
  have h2 : inner ℂ ψ (KdOp d ψ) = Complex.I * (z - (starRingEnd ℂ) z) := by
    have hT := TdOp_simetrico d ψ (PdOp d ψ)
    have hP := PdOp_simetrico d ψ (TdOp d ψ)
    have hc : inner ℂ (PdOp d ψ) (TdOp d ψ) = (starRingEnd ℂ) z :=
      (inner_conj_symm (PdOp d ψ) (TdOp d ψ)).symm
    simp only [KdOp, ConstructorEspectralTP.observableTension, ConstructorEspectralTP.conmutador,
      LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right,
      inner_sub_right]
    rw [← hT, ← hP, hc]
  rw [h1, Complex.sub_conj] at h2
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re] at h3
  simp at h3
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  field_simp at h3 ⊢
  linarith

/-! ## 6. Defect de Gram del par `(T_d ψ, P_d ψ)` -/

/-- Defect de Gram del par `(T_d ψ, P_d ψ)`. -/
def defectGram (d : ℕ) : ℝ :=
  ‖TdOp d (vectorFiedlerExplicito d)‖ ^ 2 * ‖PdOp d (vectorFiedlerExplicito d)‖ ^ 2 -
    ‖inner ℂ (TdOp d (vectorFiedlerExplicito d)) (PdOp d (vectorFiedlerExplicito d))‖ ^ 2

/-- **Puente.** El defect de Gram es `(C_Nava(d)² - 1)/(d-1)²`. -/
theorem escalon_gram {d : ℕ} (hd : 2 ≤ d) :
    defectGram d = (CoherenceConstantSq d - 1) / ((d : ℝ) - 1) ^ 2 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  have hprod := escalon_producto hd
  have hnorm : ‖inner ℂ (TdOp d (vectorFiedlerExplicito d))
      (PdOp d (vectorFiedlerExplicito d))‖ ^ 2 = 1 / ((d : ℝ) - 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, escalon_cruzado_re hd, escalon_cruzado_im hd]
    field_simp
    ring
  unfold defectGram
  rw [hnorm, ← hprod]
  field_simp

/-- Desde `d = 4` el defect de Gram es estrictamente positivo. -/
theorem escalon_gram_pos {d : ℕ} (hd : 4 ≤ d) : 0 < defectGram d := by
  rw [escalon_gram (by omega)]
  have h1 := one_lt_CoherenceConstantSq d hd
  have hd1 : (0 : ℝ) < ((d : ℝ) - 1) ^ 2 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  exact div_pos (by linarith) hd1

/-- El defect de Gram se anula exactamente en `d = 2, 3`. -/
theorem escalon_gram_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) :
    defectGram d = 0 ↔ d = 2 ∨ d = 3 := by
  have hd1 : (0 : ℝ) < ((d : ℝ) - 1) ^ 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  rw [← CoherenceConstant_eq_one_iff d hd, escalon_gram hd, CoherenceConstant, Real.sqrt_eq_one,
    div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hd1.ne'
  · intro h
    exact Or.inl (by linarith)


/-! ## 7. Las medias son nulas: el defect es el centrado -/

theorem sum_fin_shift (d : ℕ) (g : ℕ → ℝ) (h0 : g 0 = 0) :
    ∑ i : Fin d, g (i.val + 1) = ∑ k ∈ Finset.range (d + 1), g k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1)) d, Finset.sum_range_succ' g d, h0]
  ring

theorem sum_pos_sin_sq {d : ℕ} (hd : 2 ≤ d) :
    ∑ i : Fin d, posicionCoord d i * Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2 = 0 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  have hk := k_sin_sq_sum_eq d (by omega)
  have hs := sin_sq_sum_eq d (by omega)
  have hkf : ∑ i : Fin d, ((i.val : ℝ) + 1) * Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2 =
      ((d : ℝ) + 1) ^ 2 / 4 := by
    have := sum_fin_shift d (fun k => (k : ℝ) * Real.sin ((k : ℝ) * theta d) ^ 2) (by simp)
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [this, hk]
  have hsf := sum_sin_sq_fin (d := d) (by omega)
  have hterm : ∀ i : Fin d, posicionCoord d i * Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2 =
      (2 * (((i.val : ℝ) + 1) * Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2) -
        ((d : ℝ) + 1) * Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2) / ((d : ℝ) - 1) := by
    intro i
    rw [posicionCoord_apply]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hkf, hsf]
  ring

/-- `⟨ψ, P_d ψ⟩ = 0`. -/
theorem escalon_media_P {d : ℕ} (hd : 2 ≤ d) :
    inner ℂ (vectorFiedlerExplicito d) (PdOp d (vectorFiedlerExplicito d)) = 0 := by
  have hn := norm_crudo_sq (d := d) (by omega)
  have hterm : ∀ i : Fin d,
      inner ℂ ((vectorFiedlerExplicito d).ofLp i) ((PdOp d (vectorFiedlerExplicito d)).ofLp i) =
        ((posicionCoord d i * Real.sin (((i.val : ℝ) + 1) * theta d) ^ 2 /
          (((d : ℝ) + 1) / 2) : ℝ) : ℂ) := by
    intro i
    simp only [PdOp_apply, WithLp.ofLp_toLp]
    rw [Pd_mulVec, RCLike.inner_apply]
    have h2 : ((vectorFiedlerExplicito d).ofLp i) *
        (starRingEnd ℂ) ((vectorFiedlerExplicito d).ofLp i) =
          ((‖(vectorFiedlerExplicito d).ofLp i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj', ]
      push_cast
      ring
    have hnorm := vectorFiedlerExplicito_norm_sq d (by omega) i
    rw [vectorFiedlerCrudo_norm_sq, hn] at hnorm
    calc (posicionCoord d i : ℂ) * (vectorFiedlerExplicito d).ofLp i *
          (starRingEnd ℂ) ((vectorFiedlerExplicito d).ofLp i)
        = (posicionCoord d i : ℂ) * ((vectorFiedlerExplicito d).ofLp i *
          (starRingEnd ℂ) ((vectorFiedlerExplicito d).ofLp i)) := by ring
      _ = _ := by
        rw [h2, hnorm]
        push_cast
        ring
  rw [PiLp.inner_apply]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, sum_pos_sin_sq hd]
  simp

/-- `⟨ψ, T_d ψ⟩ = 0`. -/
theorem escalon_media_T {d : ℕ} (hd : 2 ≤ d) :
    inner ℂ (vectorFiedlerExplicito d) (TdOp d (vectorFiedlerExplicito d)) = 0 := by
  have hterm : ∀ i : Fin d,
      inner ℂ ((vectorFiedlerCrudo d).ofLp i) ((TdOp d (vectorFiedlerCrudo d)).ofLp i) =
        -Complex.I *
          ((Real.tan (theta d) * Real.cos (((i.val : ℝ) + 1) * theta d) *
            Real.sin (((i.val : ℝ) + 1) * theta d) : ℝ) : ℂ) := by
    intro i
    simp only [TdOp_apply, WithLp.ofLp_toLp, crudo_ofLp]
    rw [Td_cf_apply hd i, RCLike.inner_apply]
    have hII : ((-Complex.I) ^ i.val) * (Complex.I ^ i.val) = 1 := by
      rw [← mul_pow]
      simp
    have hconj : (starRingEnd ℂ) ((-Complex.I) ^ i.val) = Complex.I ^ i.val := by
      rw [map_pow]
      simp
    simp only [cf]
    rw [map_mul, hconj, Complex.conj_ofReal]
    generalize Real.sin (((i.val : ℝ) + 1) * theta d) = sn
    generalize Real.tan (theta d) = t
    generalize Real.cos (((i.val : ℝ) + 1) * theta d) = c
    push_cast
    rw [pow_succ]
    linear_combination (-Complex.I * (t : ℂ) * (c : ℂ) * (sn : ℂ)) * hII
  have hcr : (inner ℂ (vectorFiedlerCrudo d) (TdOp d (vectorFiedlerCrudo d))).re = 0 := by
    rw [PiLp.inner_apply]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, neg_mul, Complex.neg_re, Complex.I_mul_re,
      Complex.ofReal_im, neg_zero, neg_zero]
  set ψ := vectorFiedlerExplicito d with hψ
  set z := inner ℂ ψ (TdOp d ψ) with hz
  have hre : z.re = 0 := by
    rw [hz, hψ, vectorFiedlerExplicito, map_smul, inner_smul_left, inner_smul_right,
      ← mul_assoc]
    set r : ℂ := ((‖vectorFiedlerCrudo d‖ : ℝ) : ℂ)⁻¹ with hr
    have hrr : (starRingEnd ℂ) r * r = ((((‖vectorFiedlerCrudo d‖ : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [hr, map_inv₀, Complex.conj_ofReal]
      push_cast
      ring
    rw [hrr, Complex.re_ofReal_mul, hcr]
    ring
  have him : z.im = 0 := by
    have hT := TdOp_simetrico d ψ ψ
    have hc : (starRingEnd ℂ) (inner ℂ (TdOp d ψ) ψ) = inner ℂ ψ (TdOp d ψ) :=
      inner_conj_symm ψ (TdOp d ψ)
    rw [hT] at hc
    have := congrArg Complex.im hc
    simp only [Complex.conj_im] at this
    rw [hz]
    linarith
  exact Complex.ext (by simpa using hre) (by simpa using him)



end EscalonGramCoherenceConstant

end

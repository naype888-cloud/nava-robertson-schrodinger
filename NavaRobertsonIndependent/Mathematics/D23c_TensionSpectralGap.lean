import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap

/-!
# D23c — Brecha espectral de `K_d`: la tensión controla la distancia a `ψ*`

El autovalor superior `2/(d−1)` de `K_d = i[T_d, P_d]` es simple (`D21`). Aquí se da la
separación explícita con el resto del espectro:

* `autovalorK_eq`: `λ_k = (2/(d−1)) · cos θ_k / cos θ_0`, con `θ_k = (k+1)π/(d+1)`.
* `segundoAutovalor d = (2/(d−1)) · cos(2π/(d+1)) / cos(π/(d+1))` acota todo autovalor
  distinto del superior (`autovalorK_le_segundo`).
* `brechaK d = 2/(d−1) − segundoAutovalor d > 0` (`brechaK_pos`).
* `tension_ortogonal_le`: si `φ ⊥ ψ*`, entonces `⟨φ, K_d φ⟩ ≤ segundoAutovalor d · ‖φ‖²`.
* `distancia_le_deficit`: para todo estado unitario `ψ`, con `a = ⟨ψ*, ψ⟩`,
  `brechaK d · ‖ψ − a ψ*‖² ≤ 2/(d−1) − ⟨K_d⟩_ψ`.

En palabras: cuanto más cerca está la carga `⟨K_d⟩` del máximo, más cerca está el estado de
`ψ*`, con constante explícita `brechaK d`.
-/

noncomputable section

namespace AnchoFranja

open NavaRobertsonSchrodingerEDUI TransportePosicion SaturacionAutovectores SobranteIntermedio
  ConstructorEspectralTP

/-! ## 1. Expansión espectral de la forma cuadrática -/

section Generico

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem re_inner_eq_suma (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (v : H) :
    (inner ℂ v (K v)).re =
      ∑ i, hK.eigenvalues rfl i * ‖(hK.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
  rw [← (hK.eigenvectorBasis rfl).repr.inner_map_map v (K v), PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hK.eigenvectorBasis_apply_self_apply rfl v i, ← smul_eq_mul, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem norm_sq_eq_suma (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (v : H) :
    ‖v‖ ^ 2 = ∑ i, ‖(hK.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
  rw [← (hK.eigenvectorBasis rfl).repr.norm_map, EuclideanSpace.norm_sq_eq]

end Generico

/-! ## 2. El segundo autovalor y la brecha -/

/-- Cota de todo autovalor de `K_d` distinto del superior. -/
def segundoAutovalor (d : ℕ) : ℝ :=
  (2 / ((d : ℝ) - 1)) * Real.cos (2 * Real.pi / ((d : ℝ) + 1)) /
    Real.cos (Real.pi / ((d : ℝ) + 1))

/-- Brecha espectral de `K_d`: distancia del autovalor superior al resto del espectro. -/
def brechaK (d : ℕ) : ℝ := 2 / ((d : ℝ) - 1) - segundoAutovalor d

theorem cos_fiedler_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Real.cos (Real.pi / ((d : ℝ) + 1)) := by
  have h := rho_pos d hd
  unfold rho at h
  linarith

theorem autovalorK_eq {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    autovalorK d k =
      (((2 / ((d : ℝ) - 1)) * Real.cos (anguloModo d k) /
        Real.cos (Real.pi / ((d : ℝ) + 1)) : ℝ) : ℂ) := by
  have hc := (cos_fiedler_pos hd).ne'
  simp only [autovalorK, autovalorAd, rho]
  push_cast
  field_simp

theorem autovalorK_le_segundo {d : ℕ} (hd : 2 ≤ d) (k : Fin d) (hk : k.val ≠ 0) :
    (autovalorK d k).re ≤ segundoAutovalor d := by
  rw [autovalorK_eq hd, Complex.ofReal_re, segundoAutovalor]
  have hc := cos_fiedler_pos hd
  have hdpos : 0 < 2 / ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_pos (by norm_num) (by linarith)
  apply div_le_div_of_nonneg_right _ hc.le
  apply mul_le_mul_of_nonneg_left _ hdpos.le
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (anguloModo_mem_Icc k).2
  unfold anguloModo
  have hk1 : (2 : ℝ) ≤ (k.val : ℝ) + 1 := by
    have : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
    have : (1 : ℝ) ≤ k.val := by exact_mod_cast this
    linarith
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hk1 (by positivity)

theorem brechaK_pos {d : ℕ} (hd : 2 ≤ d) : 0 < brechaK d := by
  have hc := cos_fiedler_pos hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < 2 / ((d : ℝ) - 1) := div_pos (by norm_num) (by linarith)
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  have hlt : Real.cos (2 * Real.pi / ((d : ℝ) + 1)) < Real.cos (Real.pi / ((d : ℝ) + 1)) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
    · rw [mul_div_assoc]
      have : 0 < Real.pi / ((d : ℝ) + 1) := by positivity
      linarith
  unfold brechaK segundoAutovalor
  rw [mul_div_assoc]
  have hq : Real.cos (2 * Real.pi / ((d : ℝ) + 1)) / Real.cos (Real.pi / ((d : ℝ) + 1)) < 1 :=
    (div_lt_one hc).mpr hlt
  nlinarith

/-! ## 3. Estados ortogonales a `ψ*` -/

/-- Si `φ ⊥ ψ*`, su tensión no pasa de `segundoAutovalor d · ‖φ‖²`. -/
theorem tension_ortogonal_le {d : ℕ} (hd : 2 ≤ d) (φ : Hd d)
    (hφ : inner ℂ (psiStar d) φ = 0) :
    tension d φ ≤ segundoAutovalor d * ‖φ‖ ^ 2 := by
  have hK := KdOp_simetrico d
  unfold tension
  rw [re_inner_eq_suma (KdOp d) hK, norm_sq_eq_suma (KdOp d) hK, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨k, hk⟩ := KdOp_autovalor_agota_espectro hd (hK.hasEigenvalue_eigenvalues rfl i)
  by_cases hk0 : k.val = 0
  · -- autovalor superior: el vector propio es múltiplo de `ψ*`, luego la coordenada es `0`
    have hk' : k = ⟨0, by omega⟩ := Fin.ext hk0
    have hv : KdOp d (hK.eigenvectorBasis rfl i) =
        ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • hK.eigenvectorBasis rfl i := by
      rw [hK.apply_eigenvectorBasis rfl i, hk, hk', autovalorK_fundamental d hd]
    obtain ⟨c, hc⟩ := autovector_superior_multiplo hd _ hv
    have h0 : (hK.eigenvectorBasis rfl).repr φ i = 0 := by
      rw [OrthonormalBasis.repr_apply_apply, hc, inner_smul_left, hφ, mul_zero]
    simp [h0]
  · have hle : hK.eigenvalues rfl i ≤ segundoAutovalor d := by
      have := autovalorK_le_segundo hd k hk0
      rw [← hk] at this
      simpa using this
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

/-! ## 4. La tensión controla la distancia a `ψ*` -/

theorem inner_psiStar_self {d : ℕ} (hd : 2 ≤ d) : inner ℂ (psiStar d) (psiStar d) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norma_psiStar hd]
  simp

/-- La componente de `ψ` ortogonal a `ψ*`. -/
def componenteOrtogonal (d : ℕ) (ψ : Hd d) : Hd d :=
  ψ - inner ℂ (psiStar d) ψ • psiStar d

theorem componenteOrtogonal_perp {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) :
    inner ℂ (psiStar d) (componenteOrtogonal d ψ) = 0 := by
  rw [componenteOrtogonal, inner_sub_right, inner_smul_right, inner_psiStar_self hd, mul_one,
    sub_self]

/-- `‖ψ‖² = |⟨ψ*,ψ⟩|² + ‖φ‖²`. -/
theorem norm_sq_descomp {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) :
    ‖ψ‖ ^ 2 = ‖inner ℂ (psiStar d) ψ‖ ^ 2 + ‖componenteOrtogonal d ψ‖ ^ 2 := by
  set a := inner ℂ (psiStar d) ψ
  set φ := componenteOrtogonal d ψ
  have hψ : ψ = a • psiStar d + φ := by simp [φ, componenteOrtogonal, a]
  have h0 : inner ℂ (a • psiStar d) φ = 0 := by
    rw [inner_smul_left, componenteOrtogonal_perp hd, mul_zero]
  conv_lhs => rw [hψ]
  rw [@norm_add_sq ℂ, h0, norm_smul, norma_psiStar hd]
  simp

/-- `⟨K⟩_ψ = (2/(d−1)) |⟨ψ*,ψ⟩|² + ⟨K⟩_φ`. -/
theorem tension_descomp {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) :
    tension d ψ = 2 / ((d : ℝ) - 1) * ‖inner ℂ (psiStar d) ψ‖ ^ 2 +
      tension d (componenteOrtogonal d ψ) := by
  set a := inner ℂ (psiStar d) ψ
  set φ := componenteOrtogonal d ψ
  have hψ : ψ = a • psiStar d + φ := by simp [φ, componenteOrtogonal, a]
  have hperp : inner ℂ (psiStar d) φ = 0 := componenteOrtogonal_perp hd ψ
  have hperp' : inner ℂ φ (psiStar d) = 0 := by
    rw [← inner_conj_symm, hperp, map_zero]
  have hKφ : inner ℂ (psiStar d) (KdOp d φ) = 0 := by
    rw [← KdOp_simetrico d, KdOp_vectorFiedlerExplicito d hd, inner_smul_left, hperp, mul_zero]
  have hK := KdOp_vectorFiedlerExplicito d hd
  unfold tension
  conv_lhs => rw [hψ]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hK, hKφ, hperp', inner_psiStar_self hd, mul_zero, add_zero, mul_one]
  rw [Complex.add_re]
  congr 1
  rw [mul_comm a, mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  rw [zero_add]

/-- **La tensión controla la distancia a `ψ*`.** Para todo estado unitario,
`brechaK d · ‖ψ − ⟨ψ*,ψ⟩ ψ*‖² ≤ 2/(d−1) − ⟨K_d⟩_ψ`. -/
theorem distancia_le_deficit {d : ℕ} (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    brechaK d * ‖componenteOrtogonal d ψ‖ ^ 2 ≤ 2 / ((d : ℝ) - 1) - tension d ψ := by
  have hn := norm_sq_descomp hd ψ
  have ht := tension_descomp hd ψ
  have hφ := tension_ortogonal_le hd _ (componenteOrtogonal_perp hd ψ)
  rw [hψ, one_pow] at hn
  unfold brechaK
  have e : 2 / ((d : ℝ) - 1) = 2 / ((d : ℝ) - 1) *
      (‖inner ℂ (psiStar d) ψ‖ ^ 2 + ‖componenteOrtogonal d ψ‖ ^ 2) := by
    rw [← hn, mul_one]
  nlinarith

end AnchoFranja

end

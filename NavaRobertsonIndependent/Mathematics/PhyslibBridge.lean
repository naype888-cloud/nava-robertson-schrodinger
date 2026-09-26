/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D21_ElementalNRSInequality
public import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.State.VectorUncertainty

/-!
# Bridge to physlib: `(T_d, P_d)` as an instance of `robertson_schrodinger`

This file certifies that `D21`'s Nava–Robertson–Schrödinger inequality for the concrete
operators `T_d`, `P_d` at the maximal-tension state `ψ*` is not merely analogous to physlib's
abstract `UnitalPositiveLinearMap.robertson_schrodinger` — it *is* that theorem, instantiated.

`T_d`, `P_d` are lifted from `Hd d →ₗ[ℂ] Hd d` (already built in `D5_MaximalTension`) to
self-adjoint elements of the C⋆-algebra `Hd d →L[ℂ] Hd d`
(`PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable`), and `ψ*` to the vector state
`UnitalPositiveLinearMap.ofVec`. Every quantity physlib's `robertson_schrodinger` is stated in
terms of — `variance`, `covariance`, the bracket expectation `ω⟨⁅a,b⁆⟩` — is shown to equal the
corresponding `D21` quantity at `ψ*`, so the two inequalities coincide term by term.

No SI constant, no unit: this stays entirely inside Layer 1.
-/

@[expose] public noncomputable section

open TransportePosicion NavaRobertsonSchrodingerEDUI UnitalPositiveLinearMap ConstructorEspectralTP
open scoped selfAdjoint ComplexOrder InnerProductSpace

namespace PhyslibBridge

/-! ## 1. `T_d`, `P_d` as self-adjoint continuous linear maps -/

/-- `T_d`, realized as a continuous linear endomorphism of `H_d` (automatic in finite dimension).
Same operator as `TdOp d`, just repackaged for the C⋆-algebra `Hd d →L[ℂ] Hd d`. -/
noncomputable def TdCLM (d : ℕ) : Hd d →L[ℂ] Hd d :=
  LinearMap.toContinuousLinearMap (TdOp d)

noncomputable def PdCLM (d : ℕ) : Hd d →L[ℂ] Hd d :=
  LinearMap.toContinuousLinearMap (PdOp d)

theorem TdCLM_apply (d : ℕ) (v : Hd d) : TdCLM d v = TdOp d v := rfl

theorem PdCLM_apply (d : ℕ) (v : Hd d) : PdCLM d v = PdOp d v := rfl

theorem TdCLM_selfAdjoint (d : ℕ) : IsSelfAdjoint (TdCLM d) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (TdOp_simetrico d)

theorem PdCLM_selfAdjoint (d : ℕ) : IsSelfAdjoint (PdCLM d) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (PdOp_simetrico d)

/-- `T_d`, packaged as a physlib `Observable (Hd d →L[ℂ] Hd d)`. -/
noncomputable def TdObs (d : ℕ) : Observable (Hd d →L[ℂ] Hd d) :=
  ⟨TdCLM d, TdCLM_selfAdjoint d⟩

/-- `P_d`, packaged as a physlib `Observable (Hd d →L[ℂ] Hd d)`. -/
noncomputable def PdObs (d : ℕ) : Observable (Hd d →L[ℂ] Hd d) :=
  ⟨PdCLM d, PdCLM_selfAdjoint d⟩

theorem TdObs_coe_apply (d : ℕ) (v : Hd d) : (TdObs d : Hd d →L[ℂ] Hd d) v = TdOp d v := rfl

theorem PdObs_coe_apply (d : ℕ) (v : Hd d) : (PdObs d : Hd d →L[ℂ] Hd d) v = PdOp d v := rfl

/-! ## 2. The vector state at `ψ*` -/

/-- The physlib vector state at the maximal-tension state `ψ*`. -/
noncomputable def omegaStar (d : ℕ) (hd : 2 ≤ d) : 𝓢[ℂ, Hd d →L[ℂ] Hd d] :=
  UnitalPositiveLinearMap.ofVec (norma_psiStar hd)

theorem omegaStar_def (d : ℕ) (hd : 2 ≤ d) :
    omegaStar d hd = UnitalPositiveLinearMap.ofVec (norma_psiStar hd) := rfl

/-! ## 3. Matching `D21`'s statistics term by term -/

/-- The expectation of an observable in `ω*` is `D21`'s `media` at `ψ*`. -/
theorem expectation_omegaStar (d : ℕ) (hd : 2 ≤ d) (a : Observable (Hd d →L[ℂ] Hd d)) :
    (omegaStar d hd)⟨a⟩ = media ((a : Hd d →L[ℂ] Hd d) : Hd d →ₗ[ℂ] Hd d) (psiStar d) := by
  have h := apply_observable_eq_expectation (omegaStar d hd) a
  rw [media, ← Complex.ofReal_re ((omegaStar d hd)⟨a⟩), ← h]
  rfl

/-- The physlib fluctuation vector at `ψ*` is `D21`'s `centrado`. -/
theorem fluctuation_eq_centrado (d : ℕ) (hd : 2 ≤ d) (a : Observable (Hd d →L[ℂ] Hd d)) :
    (a : Hd d →L[ℂ] Hd d) (psiStar d) - (omegaStar d hd)⟨a⟩ • psiStar d =
      centrado ((a : Hd d →L[ℂ] Hd d) : Hd d →ₗ[ℂ] Hd d) (psiStar d) := by
  rw [centrado, ← expectation_omegaStar d hd a, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- physlib's variance of `T_d` at `ω*` is `D21`'s `varianza (TdOp d) (psiStar d)`. -/
theorem variance_TdObs (d : ℕ) (hd : 2 ≤ d) :
    variance (omegaStar d hd) (TdObs d) = varianza (TdOp d) (psiStar d) := by
  rw [omegaStar, variance_ofVec, ← omegaStar_def d hd, fluctuation_eq_centrado d hd]
  rfl

/-- physlib's variance of `P_d` at `ω*` is `D21`'s `varianza (PdOp d) (psiStar d)`. -/
theorem variance_PdObs (d : ℕ) (hd : 2 ≤ d) :
    variance (omegaStar d hd) (PdObs d) = varianza (PdOp d) (psiStar d) := by
  rw [omegaStar, variance_ofVec, ← omegaStar_def d hd, fluctuation_eq_centrado d hd]
  rfl

/-- physlib's covariance of `(T_d, P_d)` at `ω*` is `D21`'s `covarianza`. -/
theorem covariance_TdObs_PdObs (d : ℕ) (hd : 2 ≤ d) :
    covariance (omegaStar d hd) (TdObs d) (PdObs d) = covarianza (TdOp d) (PdOp d) (psiStar d) := by
  rw [covariance_eq_re_apply_centered_mul, omegaStar, apply_centered_mul_centered_ofVec,
    ← omegaStar_def d hd, fluctuation_eq_centrado d hd, fluctuation_eq_centrado d hd]
  rfl

/-! ## 4. The commutator term -/

/-- physlib's bracket `⁅T_d, P_d⁆ = -(i/2)[T_d, P_d]` acts as `-(1/2) K_d`, with
`K_d = i[T_d, P_d]`. -/
theorem bracket_TdObs_PdObs_apply (d : ℕ) (v : Hd d) :
    ((⁅TdObs d, PdObs d⁆ : Observable (Hd d →L[ℂ] Hd d)) : Hd d →L[ℂ] Hd d) v =
      (-(1 / 2 : ℂ)) • KdOp d v := by
  rw [selfAdjoint.coe_bracket]
  simp only [smul_apply, sub_apply,
    mul_apply_eq_comp, TdObs_coe_apply, PdObs_coe_apply, KdOp, observableTension,
    conmutador, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [smul_smul]
  congr 1
  apply Complex.ext <;> simp

/-- The commutator expectation in physlib's convention is `D21`'s `c/2`. -/
theorem expectation_bracket_TdObs_PdObs (d : ℕ) (hd : 2 ≤ d) :
    (omegaStar d hd)⟨⁅TdObs d, PdObs d⁆⟩ = commutatorConstant d / 2 := by
  rw [expectation_omegaStar d hd, media]
  change (inner ℂ (psiStar d)
    (((⁅TdObs d, PdObs d⁆ : Observable (Hd d →L[ℂ] Hd d)) : Hd d →L[ℂ] Hd d) (psiStar d))).re = _
  rw [bracket_TdObs_PdObs_apply, inner_smul_right]
  have ht := SobranteIntermedio.tension_psiStar hd
  unfold SobranteIntermedio.tension at ht
  rw [commutatorConstant]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.one_re, Complex.one_im, ht]
  ring_nf

/-! ## 5. `D21` is physlib's Robertson–Schrödinger inequality -/

/-- physlib's `robertson_schrodinger` at `(ω*, T_d, P_d)` is, term by term, `D21`'s inequality. -/
theorem robertson_schrodinger_eq_D21 (d : ℕ) (hd : 2 ≤ d) :
    (covariance (omegaStar d hd) (TdObs d) (PdObs d) ^ 2 +
        (omegaStar d hd)⟨⁅TdObs d, PdObs d⁆⟩ ^ 2 ≤
      variance (omegaStar d hd) (TdObs d) * variance (omegaStar d hd) (PdObs d)) ↔
    (covarianza (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2 ≤
      varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d)) := by
  rw [covariance_TdObs_PdObs, expectation_bracket_TdObs_PdObs, variance_TdObs, variance_PdObs]

/-- `D21`'s non-strict inequality, obtained directly from physlib's `robertson_schrodinger`. -/
theorem D21_of_physlib (d : ℕ) (hd : 2 ≤ d) :
    covarianza (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2 ≤
      varianza (TdOp d) (psiStar d) * varianza (PdOp d) (psiStar d) :=
  (robertson_schrodinger_eq_D21 d hd).mp
    (robertson_schrodinger (omegaStar d hd) (TdObs d) (PdObs d))

/-- For `d ≥ 4`, physlib's `robertson_schrodinger` at `(ω*, T_d, P_d)` is strict (`D21`). -/
theorem physlib_robertson_schrodinger_strict (d : ℕ) (hd : 4 ≤ d) :
    covariance (omegaStar d (by omega)) (TdObs d) (PdObs d) ^ 2 +
        (omegaStar d (by omega))⟨⁅TdObs d, PdObs d⁆⟩ ^ 2 <
      variance (omegaStar d (by omega)) (TdObs d) * variance (omegaStar d (by omega)) (PdObs d) :=
          by
  rw [covariance_TdObs_PdObs, expectation_bracket_TdObs_PdObs, variance_TdObs, variance_PdObs]
  exact desigualdad_estricta hd

end PhyslibBridge

end

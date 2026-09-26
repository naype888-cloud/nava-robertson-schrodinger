/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
public import NavaRobertsonIndependent.Mathematics.D6_Fiedler
public import NavaRobertsonIndependent.Mathematics.D8_Szego

/-!
# D21 — The Nava–Robertson–Schrödinger inequality

On `T_d`, `P_d` of the path at the maximal-tension state `ψ*`, with `K_d = i[T_d, P_d]` and
`c = −2/(d−1)`:

* the means and `cov(T_d, P_d)` vanish;
* `Var T_d · Var P_d = (c/2)² (1 + δ(d))²` exactly;
* the Robertson–Schrödinger gap `Var T · Var P − (cov² + (c/2)²) = (c/2)² δ(d) (2 + δ(d))` is
  the Gram defect `(C_Nava(d)² − 1)/(d−1)²`, zero exactly at `d = 2, 3`, positive from `d = 4`;
* the top eigenvalue `2/(d−1)` of `K_d` is simple, so the inequality is strict at every
  maximal-tension state.

Mean, variance and covariance are those of centred vectors: `⟨A⟩ = Re ⟪ψ, A ψ⟫`,
`Var A = ‖A ψ − ⟨A⟩ ψ‖²`, `cov(A, B) = Re ⟪Ãψ, B̃ψ⟫`.

## Main results

- `NRSInequality.variance_mul_variance` : `Var T_d · Var P_d = (c/2)² (1 + δ(d))²`.
- `NRSInequality.saturation_iff` : saturation at `ψ*` iff `d = 2, 3`.
- `NRSInequality.strict_inequality` : strict for `d ≥ 4`.
- `NRSInequality.strict_inequality_of_maxTension` : strict at every maximal-tension state.
-/

@[expose] public noncomputable section

namespace Gnomon

theorem CoherenceConstant_eq_one_add_geometricGap (d : ℕ) : CoherenceConstant d = 1 + geometricGap d
    := by
  unfold geometricGap
  ring

end Gnomon

open Gnomon TransportPosition FiedlerPositionVariance GramStep
    SpectralExtremal

namespace NRSInequality

/-- The maximal-tension state `ψ*`, the explicit Fiedler vector. -/
abbrev psiStar (d : ℕ) : Hd d := fiedlerVec d

/-- The mean `Re ⟪ψ, A ψ⟫`. -/
def mean {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  (inner ℂ ψ (A ψ)).re

/-- The fluctuation vector `A ψ − ⟨A⟩ ψ`. -/
def centered {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : Hd d :=
  A ψ - (mean A ψ : ℂ) • ψ

/-- The variance `‖A ψ − ⟨A⟩ ψ‖²`. -/
def variance {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  ‖centered A ψ‖ ^ 2

/-- The covariance `Re ⟪Ãψ, B̃ψ⟫`. -/
def covariance {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) : ℝ :=
  (inner ℂ (centered A ψ) (centered B ψ)).re

/-- The constant `c` with `⟪ψ*, [T_d, P_d] ψ*⟫ = i c`. -/
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

/-! ## 1. Means, variances and covariance at `ψ*` -/

theorem mean_T {d : ℕ} (hd : 2 ≤ d) : mean (TdOp d) (psiStar d) = 0 := by
  have h := gramStep_mean_T hd
  simp [mean, h]

theorem mean_P {d : ℕ} (hd : 2 ≤ d) : mean (PdOp d) (psiStar d) = 0 := by
  have h := gramStep_mean_P hd
  simp [mean, h]

theorem norm_psiStar {d : ℕ} (hd : 2 ≤ d) : ‖psiStar d‖ = 1 :=
  norm_fiedlerVec d (by omega)

theorem centered_T {d : ℕ} (hd : 2 ≤ d) :
    centered (TdOp d) (psiStar d) = TdOp d (psiStar d) := by
  simp [centered, mean_T hd]

theorem centered_P {d : ℕ} (hd : 2 ≤ d) :
    centered (PdOp d) (psiStar d) = PdOp d (psiStar d) := by
  simp [centered, mean_P hd]

theorem variance_T {d : ℕ} (hd : 2 ≤ d) :
    variance (TdOp d) (psiStar d) = ‖TdOp d (psiStar d)‖ ^ 2 := by
  unfold variance
  rw [centered_T hd]

theorem variance_P {d : ℕ} (hd : 2 ≤ d) :
    variance (PdOp d) (psiStar d) = ‖PdOp d (psiStar d)‖ ^ 2 := by
  unfold variance
  rw [centered_P hd]

theorem covariance_eq_zero {d : ℕ} (hd : 2 ≤ d) :
    covariance (TdOp d) (PdOp d) (psiStar d) = 0 := by
  unfold covariance
  rw [centered_T hd, centered_P hd]
  exact gramStep_cross_re hd

/-! ## 2. The exact product and the gap -/

theorem CoherenceConstantSq_eq_sq {d : ℕ} (hd : 2 ≤ d) : CoherenceConstantSq d = (1 + geometricGap
    d) ^ 2 := by
  have h0 : 0 ≤ CoherenceConstantSq d := by
    rw [← gramStep_product hd]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [← CoherenceConstant_eq_one_add_geometricGap, CoherenceConstant, Real.sq_sqrt h0]

/-- `Var T_d · Var P_d = (c/2)² (1 + δ(d))²`. -/
theorem variance_mul_variance {d : ℕ} (hd : 2 ≤ d) :
    variance (TdOp d) (psiStar d) * variance (PdOp d) (psiStar d) =
      (commutatorConstant d / 2) ^ 2 * (1 + geometricGap d) ^ 2 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  rw [variance_T hd, variance_P hd, commutatorConstant_half_sq hd, ← CoherenceConstantSq_eq_sq hd, ←
      gramStep_product hd]
  field_simp

/-- The Robertson–Schrödinger gap in terms of `δ(d)`. -/
theorem gap_eq_geometricGap {d : ℕ} (hd : 2 ≤ d) :
    variance (TdOp d) (psiStar d) * variance (PdOp d) (psiStar d) -
      (covariance (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2) =
      (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) := by
  rw [variance_mul_variance hd, covariance_eq_zero hd]
  ring

/-- The gap is the Gram defect `(C_Nava(d)² − 1)/(d−1)²`. -/
theorem gap_eq_defectGram {d : ℕ} (hd : 2 ≤ d) :
    variance (TdOp d) (psiStar d) * variance (PdOp d) (psiStar d) -
      (covariance (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2) =
      defectGram d := by
  rw [gramStep_gram hd, gap_eq_geometricGap hd, commutatorConstant_half_sq hd,
      CoherenceConstantSq_eq_sq hd]
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  field_simp
  ring

/-! ## 3. Saturation at `d = 2, 3`; strict from `d = 4` -/

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

/-- Robertson–Schrödinger saturates at `ψ*` iff `d = 2, 3`. -/
theorem saturation_iff {d : ℕ} (hd : 2 ≤ d) :
    covariance (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2 =
        variance (TdOp d) (psiStar d) * variance (PdOp d) (psiStar d) ↔ d = 2 ∨ d = 3 := by
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

/-- **Nava–Robertson–Schrödinger inequality.** For `d ≥ 4`, at `ψ*`,
`cov² + (c/2)² < Var T_d · Var P_d`, with gap `(c/2)² δ(d) (2 + δ(d)) > 0`. -/
theorem strict_inequality {d : ℕ} (hd : 4 ≤ d) :
    covariance (TdOp d) (PdOp d) (psiStar d) ^ 2 + (commutatorConstant d / 2) ^ 2 <
      variance (TdOp d) (psiStar d) * variance (PdOp d) (psiStar d) := by
  have hd2 : 2 ≤ d := by omega
  have hδ := geometricGap_pos_of_four_le d hd
  have hp := commutatorConstant_half_sq_pos hd2
  have h := gap_eq_geometricGap hd2
  have : 0 < (commutatorConstant d / 2) ^ 2 * (geometricGap d * (2 + geometricGap d)) :=
    mul_pos hp (mul_pos hδ (by linarith))
  linarith

/-! ## 4. Uniqueness of the maximal-tension state -/

/-- The top eigenvalue of `K_d` is simple: its eigenspace is spanned by `ψ*`. -/
theorem top_eigenvector_smul {d : ℕ} (hd : 2 ≤ d) (v : Hd d)
    (hv : KdOp d v = ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • v) :
    ∃ c : ℂ, v = c • psiStar d := by
  classical
  have hd1 : 1 ≤ d := by omega
  let k0 : Fin d := ⟨0, by omega⟩
  have hres : ∀ k : Fin d, k ≠ k0 → (phaseModeBasisHd hd).repr v k = 0 := by
    intro k hk
    have h1 := repr_KdOp hd v k
    rw [hv, map_smul, Finsupp.smul_apply, smul_eq_mul, ← eigenvalueK_fundamental d hd] at h1
    have h2 : (eigenvalueK d k0 - eigenvalueK d k) * (phaseModeBasisHd hd).repr v k = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (eigenvalueK_injective hd (sub_eq_zero.mp h)).symm hk
    · exact h
  have hsum : v = (phaseModeBasisHd hd).repr v k0 • phaseModeBasisHd hd k0 := by
    conv_lhs => rw [← (phaseModeBasisHd hd).sum_repr v]
    rw [Finset.sum_eq_single k0]
    · intro k _ hk
      rw [hres k hk, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ k0) h
  rw [phaseModeBasisHd_apply, phaseModeHd_fundamental_eq_fiedlerVecRaw d hd] at hsum
  have hn : (‖fiedlerVecRaw d‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (fiedlerVecRaw_ne_zero d hd1))
  refine ⟨(phaseModeBasisHd hd).repr v k0 * ‖fiedlerVecRaw d‖, hsum.trans ?_⟩
  show _ • fiedlerVecRaw d =
    _ • ((‖fiedlerVecRaw d‖ : ℂ)⁻¹ • fiedlerVecRaw d)
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]

/-- A unit state with `⟨K_d⟩ = 2/(d−1)` is a phase times `ψ*`. -/
theorem maxTension_state_eq_phase {d : ℕ} (hd : 2 ≤ d) (v : Hd d) (hv : ‖v‖ = 1)
    (h : (inner ℂ v (KdOp d v)).re = 2 / ((d : ℝ) - 1)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • psiStar d := by
  have hd1 : 1 ≤ d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  let T : Hd d →L[ℂ] Hd d := LinearMap.toContinuousLinearMap (KdOp d)
  have hT : IsSelfAdjoint T :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr (KdOp_isSymmetric d)
  have hTv : ∀ x, T x = KdOp d x := fun x => rfl
  have hmax : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : Hd d) ‖v‖) v := by
    rw [isMaxOn_iff]
    intro x hx
    have hx' : ‖x‖ = 1 := by simpa [hv] using hx
    have hle := expectation_le_specRadius (KdOp d) (KdOp_isSymmetric d) x hx'
    rw [specRadius_KdOp_eq_step d hd] at hle
    have hre : (inner ℂ (KdOp d x) x).re = (inner ℂ x (KdOp d x)).re := by
      rw [← inner_conj_symm x (KdOp d x), Complex.conj_re]
    have hre_v : (inner ℂ (KdOp d v) v).re = 2 / ((d : ℝ) - 1) := by
      rw [← h, ← inner_conj_symm v (KdOp d v), Complex.conj_re]
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply, hTv, RCLike.re_to_complex]
    rw [hre, hre_v]
    exact (Complex.re_le_norm _).trans hle
  have hK : T v = ((T.rayleighQuotient v : ℝ) : ℂ) • v :=
    hT.eq_smul_self_of_isLocalExtrOn (Or.inr hmax.isLocalMaxOn)
  have hray : T.rayleighQuotient v = 2 / ((d : ℝ) - 1) := by
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      hTv, hv, RCLike.re_to_complex]
    rw [← h, ← inner_conj_symm v (KdOp d v), Complex.conj_re]
    simp
  rw [hray, hTv] at hK
  obtain ⟨c, hc⟩ := top_eigenvector_smul hd v hK
  refine ⟨c, ?_, hc⟩
  have := congrArg norm hc
  rwa [hv, norm_smul, norm_fiedlerVec d hd1, mul_one, eq_comm] at this

/-! ## 5. Phase invariance and strictness at every maximal-tension state -/

theorem mean_phase {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    mean A (c • ψ) = mean A ψ := by
  simp only [mean, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, Complex.mul_conj', hc]
  simp

theorem centered_phase {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    centered A (c • ψ) = c • centered A ψ := by
  unfold centered
  rw [mean_phase A ψ c hc]
  simp only [map_smul]
  module

theorem variance_phase {d : ℕ} (A : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    variance A (c • ψ) = variance A ψ := by
  unfold variance
  rw [centered_phase A ψ c hc, norm_smul, hc, one_mul]

theorem covariance_phase {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) (c : ℂ) (hc : ‖c‖ = 1) :
    covariance A B (c • ψ) = covariance A B ψ := by
  unfold covariance
  rw [centered_phase A ψ c hc, centered_phase B ψ c hc, inner_smul_left, inner_smul_right,
    ← mul_assoc, Complex.conj_mul', hc]
  simp

/-- For `d ≥ 4`, every unit state with `⟨K_d⟩ = 2/(d−1)` satisfies Robertson–Schrödinger
strictly. -/
theorem strict_inequality_of_maxTension {d : ℕ} (hd : 4 ≤ d) (v : Hd d) (hv : ‖v‖ = 1)
    (h : (inner ℂ v (KdOp d v)).re = 2 / ((d : ℝ) - 1)) :
    covariance (TdOp d) (PdOp d) v ^ 2 + (commutatorConstant d / 2) ^ 2 <
      variance (TdOp d) v * variance (PdOp d) v := by
  obtain ⟨c, hc, rfl⟩ := maxTension_state_eq_phase (by omega) v hv h
  rw [covariance_phase _ _ _ _ hc, variance_phase _ _ _ hc, variance_phase _ _ _ hc]
  exact strict_inequality hd

end NRSInequality

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation

/-!
# D47 — Platform blindness: position eigenstates cannot witness the defect

All previous waveguide-array experiments on continuous-time quantum walks (Perets 2008,
Peruzzo 2010, Tang 2018) prepare a single-guide excitation, an eigenstate of the position
operator `P_d`. A defect witness of the Nava–Robertson–Schrödinger inequality is a unit
state whose Robertson–Schrödinger gap — the Gram defect of `D23` — is strictly positive.

## Main results

- `PlatformBlindness.IsDefectWitness` : the defect witness, a unit state with strictly
  positive Gram defect.
- `PlatformBlindness.gramDefectAt_eq_zero_of_P_eigenvector` : a unit eigenvector of `P_d`
  with real eigenvalue has zero Gram defect; it saturates trivially (`0 = 0`).
- `PlatformBlindness.not_isDefectWitness_of_P_eigenvector` : such a state is not a defect
  witness; single-guide excitations cannot witness the defect.
- `PlatformBlindness.isDefectWitness_psiStar` : for `d ≥ 4` the maximal-tension state `ψ*`
  is a defect witness, with nonzero tension `⟨K_d⟩ = 2/(d−1)`.
- `PlatformBlindness.variance_pos_of_isDefectWitness` : every defect witness fluctuates in
  both `T_d` and `P_d`.
-/

@[expose] public noncomputable section

namespace PlatformBlindness

open NRSInequality EigenvectorSaturation TransportPosition

/-- A defect witness: a unit state at which the Robertson–Schrödinger gap, the Gram defect
of `D23`, is strictly positive. -/
def IsDefectWitness {d : ℕ} (ψ : Hd d) : Prop :=
  ‖ψ‖ = 1 ∧ 0 < gramDefectAt (TdOp d) (PdOp d) ψ

/-! ## 1. Position eigenstates saturate trivially -/

/-- A unit eigenvector of `B` with real eigenvalue has zero centred fluctuation in `B`, hence
zero variance and zero Gram defect: Robertson–Schrödinger saturates, `0 = 0`. -/
theorem gramDefectAt_eq_zero_of_eigenvector {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) (a : ℝ) (h : B ψ = (a : ℂ) • ψ) : gramDefectAt A B ψ = 0 := by
  have hc := centered_eigenvector hψ a h
  have hv : variance B ψ = 0 := by
    unfold variance
    rw [hc]
    simp
  exact (gramDefectAt_eq_zero_iff A B ψ).mpr (Or.inl hv)

/-- A unit eigenvector of `P_d` with real eigenvalue has zero Gram defect: it saturates
Robertson–Schrödinger, `0 = 0`. -/
theorem gramDefectAt_eq_zero_of_P_eigenvector {d : ℕ} {ψ : Hd d} (hψ : ‖ψ‖ = 1) (a : ℝ)
    (h : PdOp d ψ = (a : ℂ) • ψ) : gramDefectAt (TdOp d) (PdOp d) ψ = 0 :=
  gramDefectAt_eq_zero_of_eigenvector (TdOp d) (PdOp d) hψ a h

/-- On a position eigenstate both the covariance and the imaginary part of the fluctuation
inner product vanish: both sides of Robertson–Schrödinger are `0`. -/
theorem saturates_of_P_eigenvector {d : ℕ} {ψ : Hd d} (hψ : ‖ψ‖ = 1) (a : ℝ)
    (h : PdOp d ψ = (a : ℂ) • ψ) :
    covariance (TdOp d) (PdOp d) ψ = 0 ∧ imPart (TdOp d) (PdOp d) ψ = 0 := by
  have hc : centered (PdOp d) ψ = 0 := centered_eigenvector hψ a h
  refine ⟨?_, ?_⟩
  · unfold covariance
    rw [hc]
    simp
  · unfold imPart
    rw [hc]
    simp

/-- A position eigenstate (a single-guide excitation) cannot witness the defect. -/
theorem not_isDefectWitness_of_P_eigenvector {d : ℕ} {ψ : Hd d} (hψ : ‖ψ‖ = 1) (a : ℝ)
    (h : PdOp d ψ = (a : ℂ) • ψ) : ¬ IsDefectWitness ψ :=
  fun hw => (ne_of_gt hw.2) (gramDefectAt_eq_zero_of_P_eigenvector hψ a h)

/-! ## 2. The defect witnesses `ψ*` for `d ≥ 4` -/

/-- `⟪ψ*, K_d ψ*⟫ = 2/(d−1)`, real. -/
theorem inner_KdOp_psiStar {d : ℕ} (hd : 2 ≤ d) :
    inner ℂ (psiStar d) (KdOp d (psiStar d)) = ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
  have hK := KdOp_fiedlerVec d hd
  have hn := norm_psiStar hd
  rw [show psiStar d = fiedlerVec d from rfl, hK, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hn]
  simp

/-- The witness `ψ*` has nonzero tension `⟨K_d⟩ = 2/(d−1)`. -/
theorem tension_psiStar_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    (inner ℂ (psiStar d) (KdOp d (psiStar d))).re ≠ 0 := by
  rw [inner_KdOp_psiStar hd]
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact ne_of_gt (div_pos (by norm_num) hd1)

/-- At `ψ*` the imaginary part of the fluctuation inner product is `−1/(d−1)`; its square
is `(c/2)²` for `c = commutatorConstant d`. -/
theorem imPart_psiStar_sq {d : ℕ} (hd : 2 ≤ d) :
    imPart (TdOp d) (PdOp d) (psiStar d) ^ 2 = (commutatorConstant d / 2) ^ 2 := by
  have hre : (inner ℂ (psiStar d) (KdOp d (psiStar d))).re = 2 / ((d : ℝ) - 1) := by
    rw [inner_KdOp_psiStar hd, Complex.ofReal_re]
  have h2 := re_inner_KdOp d (psiStar d)
  rw [hre] at h2
  rw [imPart_eq_im_inner (TdOp_isSymmetric d) (PdOp_isSymmetric d)]
  have ht : ((d : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  have key : -2 * (inner ℂ (TdOp d (psiStar d)) (PdOp d (psiStar d))).im * ((d : ℝ) - 1) = 2 := by
    have h2' := congrArg (fun y : ℝ => y * ((d : ℝ) - 1)) h2
    rw [div_mul_cancel₀ _ ht] at h2'
    linarith
  have hxt : (inner ℂ (TdOp d (psiStar d)) (PdOp d (psiStar d))).im * ((d : ℝ) - 1) = -1 := by
    linarith
  have h2sq : (inner ℂ (TdOp d (psiStar d)) (PdOp d (psiStar d))).im ^ 2 =
      1 / ((d : ℝ) - 1) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 ht)]
    nlinarith
  rw [h2sq, commutatorConstant_half_sq hd]

/-- For `d ≥ 4` the maximal-tension state `ψ*` is a defect witness: by `D21` the
inequality is strict there, and its gap is exactly the Gram defect of `D23`. -/
theorem isDefectWitness_psiStar {d : ℕ} (hd : 4 ≤ d) : IsDefectWitness (psiStar d) := by
  have hd2 : 2 ≤ d := by omega
  refine ⟨norm_psiStar hd2, ?_⟩
  rw [gramDefectAt_eq_gap, imPart_psiStar_sq hd2]
  have hs := strict_inequality hd
  linarith

/-- For `d ≥ 4` a defect witness with nonzero tension exists: `ψ*`, with
`⟨K_d⟩ = 2/(d−1)`. -/
theorem exists_isDefectWitness_of_four_le {d : ℕ} (hd : 4 ≤ d) :
    IsDefectWitness (psiStar d) ∧
      (inner ℂ (psiStar d) (KdOp d (psiStar d))).re ≠ 0 :=
  ⟨isDefectWitness_psiStar hd, tension_psiStar_ne_zero (by omega)⟩

/-! ## 3. Every witness fluctuates in both observables -/

/-- The Gram defect is symmetric in the two observables. -/
theorem gramDefectAt_comm {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) (ψ : Hd d) :
    gramDefectAt A B ψ = gramDefectAt B A ψ := by
  unfold gramDefectAt
  rw [mul_comm, norm_inner_symm]

/-- A defect witness fluctuates in both `T_d` and `P_d`: both variances are strictly
positive. -/
theorem variance_pos_of_isDefectWitness {d : ℕ} {ψ : Hd d} (hw : IsDefectWitness ψ) :
    0 < variance (TdOp d) ψ ∧ 0 < variance (PdOp d) ψ := by
  obtain ⟨_, hg⟩ := hw
  have hle : gramDefectAt (TdOp d) (PdOp d) ψ ≤
      variance (TdOp d) ψ * variance (PdOp d) ψ := by
    unfold gramDefectAt
    have hnn := sq_nonneg (‖inner ℂ (centered (TdOp d) ψ) (centered (PdOp d) ψ)‖)
    linarith
  have hpos : 0 < variance (TdOp d) ψ * variance (PdOp d) ψ := lt_of_lt_of_le hg hle
  exact ⟨pos_of_mul_pos_left hpos (sq_nonneg _),
    pos_of_mul_pos_right hpos (sq_nonneg _)⟩

/-- A defect witness is not an eigenstate of `P_d`. -/
theorem not_P_eigenvector_of_isDefectWitness {d : ℕ} {ψ : Hd d} (hw : IsDefectWitness ψ)
    (a : ℝ) : PdOp d ψ ≠ (a : ℂ) • ψ :=
  fun h => (ne_of_gt hw.2) (gramDefectAt_eq_zero_of_P_eigenvector hw.1 a h)

/-- A defect witness is not an eigenstate of `T_d`. -/
theorem not_T_eigenvector_of_isDefectWitness {d : ℕ} {ψ : Hd d} (hw : IsDefectWitness ψ)
    (a : ℝ) : TdOp d ψ ≠ (a : ℂ) • ψ := by
  intro h
  have hz : gramDefectAt (PdOp d) (TdOp d) ψ = 0 :=
    gramDefectAt_eq_zero_of_eigenvector (PdOp d) (TdOp d) hw.1 a h
  rw [gramDefectAt_comm] at hz
  exact (ne_of_gt hw.2) hz

end PlatformBlindness

end

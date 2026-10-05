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

On a position eigenstate Robertson–Schrödinger is empty: `Var P_d = 0`, so both sides are `0`
and the inequality says nothing about the pair. The pair does not vanish there. Fixing the
position sends the whole indeterminacy to transport, `Var T_d > 0` for `d ≥ 2`, and only the
tension `⟨i[T_d, P_d]⟩` is zero. This is not saturation; it is the case the inequality cannot
read.

## Main results

- `PlatformBlindness.IsDefectWitness` : the defect witness, a unit state with strictly
  positive Gram defect.
- `PlatformBlindness.gramDefectAt_eq_zero_of_P_eigenvector` : a unit eigenvector of `P_d`
  with real eigenvalue has zero Gram defect; the inequality is empty there (`0 = 0`).
- `PlatformBlindness.variance_T_pos_of_P_eigenvector` : for `d ≥ 2` it fluctuates in `T_d`,
  `Var T_d > 0`: fixing the position sends the indeterminacy to transport.
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

/-! ## 1. Position eigenstates: the inequality is empty -/

/-- A unit eigenvector of `B` with real eigenvalue has zero centred fluctuation in `B`, hence
zero variance and zero Gram defect: Robertson–Schrödinger reads `0 = 0` and says nothing. -/
theorem gramDefectAt_eq_zero_of_eigenvector {d : ℕ} (A B : Hd d →ₗ[ℂ] Hd d) {ψ : Hd d}
    (hψ : ‖ψ‖ = 1) (a : ℝ) (h : B ψ = (a : ℂ) • ψ) : gramDefectAt A B ψ = 0 := by
  have hc := centered_eigenvector hψ a h
  have hv : variance B ψ = 0 := by
    unfold variance
    rw [hc]
    simp
  exact (gramDefectAt_eq_zero_iff A B ψ).mpr (Or.inl hv)

/-- A unit eigenvector of `P_d` with real eigenvalue has zero Gram defect: Robertson–Schrödinger
is empty there, `0 = 0`. -/
theorem gramDefectAt_eq_zero_of_P_eigenvector {d : ℕ} {ψ : Hd d} (hψ : ‖ψ‖ = 1) (a : ℝ)
    (h : PdOp d ψ = (a : ℂ) • ψ) : gramDefectAt (TdOp d) (PdOp d) ψ = 0 :=
  gramDefectAt_eq_zero_of_eigenvector (TdOp d) (PdOp d) hψ a h

/-- On a position eigenstate both the covariance and the imaginary part of the fluctuation
inner product vanish: both sides of Robertson–Schrödinger are `0`. The inequality is empty, not
saturated by the pair (`variance_T_pos_of_P_eigenvector`). -/
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

/-- `P_d` acts coordinatewise: `(P_d ψ)_i = x_i ψ_i`. -/
theorem PdOp_apply_coord {d : ℕ} (ψ : Hd d) (i : Fin d) :
    PdOp d ψ i = (posCoord d i : ℂ) * ψ i := by
  simp [PdOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Pd]

/-- `T_d` in coordinates: `(T_d ψ)_i = Σ_j (T_d)_{ij} ψ_j`. -/
theorem TdOp_apply_coord {d : ℕ} (ψ : Hd d) (i : Fin d) :
    TdOp d ψ i = ∑ j, Td d i j * ψ j := by
  simp [TdOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- For `d ≥ 2` distinct positions have distinct coordinates. -/
theorem posCoord_injective {d : ℕ} (hd : 2 ≤ d) : Function.Injective (posCoord d) := by
  intro i j h
  have h1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold posCoord at h
  rw [div_left_inj' h1.ne'] at h
  exact Fin.ext (by exact_mod_cast (by linarith : ((i.val : ℝ)) = j.val))

/-- **The indeterminacy goes to transport.** For `d ≥ 2`, a unit eigenvector of `P_d` is
not an eigenvector of `T_d`: transport carries its one occupied position to a neighbour, so
`Var T_d > 0`. -/
theorem variance_T_pos_of_P_eigenvector {d : ℕ} (hd : 2 ≤ d) {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (a : ℝ) (h : PdOp d ψ = (a : ℂ) • ψ) : 0 < variance (TdOp d) ψ := by
  have hP : ∀ i, (posCoord d i : ℂ) * ψ i = a * ψ i := fun i => by
    simpa [PdOp_apply_coord] using congrArg (fun v : Hd d => v i) h
  have hne : ψ ≠ 0 := fun h0 => by simp [h0] at hψ
  obtain ⟨j, hj⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (by ext i; simp [hc i])
  have hzero : ∀ i, i ≠ j → ψ i = 0 := by
    intro i hij
    have hi := hP i
    have hjj := hP j
    have haj : (posCoord d j : ℂ) = a := mul_right_cancel₀ hj hjj
    by_contra hψi
    have hai : (posCoord d i : ℂ) = a := mul_right_cancel₀ hψi hi
    exact hij (posCoord_injective hd (by exact_mod_cast hai.trans haj.symm))
  obtain ⟨k, hkj, hadj⟩ : ∃ k : Fin d, k ≠ j ∧ MinStep k j := by
    by_cases hlt : j.val + 1 < d
    · exact ⟨⟨j.val + 1, hlt⟩, fun h => by simp [Fin.ext_iff] at h, Or.inr rfl⟩
    · have hj0 : 0 < j.val := by omega
      exact ⟨⟨j.val - 1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega,
        Or.inl (by simp; omega)⟩
  have hTk : TdOp d ψ k = ψ j / (rho d : ℂ) := by
    rw [TdOp_apply_coord, Finset.sum_eq_single j]
    · simp [Td, Ad, hadj, div_eq_inv_mul]
    · intro l _ hl
      simp [hzero l hl]
    · simp
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  unfold variance
  apply pow_pos
  rw [norm_pos_iff]
  intro hc
  have hk := congrArg (fun v : Hd d => v k) hc
  simp only [centered, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hzero k hkj, mul_zero,
    sub_zero, hTk] at hk
  exact div_ne_zero hj hρ (by simpa using hk)

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

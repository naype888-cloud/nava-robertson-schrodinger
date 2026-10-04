/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D38_GroupVelocity

/-!
# D45 — Stark packets: minimum uncertainty in motion

In the gauge `ψⱼ = (−i)ʲ φⱼ`, `φ` real, the equation `(T_d − iλ P_d) ψ = μ ψ` with
`λ = (d − 1)/(ρ_d z)` is the recurrence `φⱼ₊₁ = φⱼ₋₁ + (2(c₀ − j)/z) φⱼ`, `φ₋₁ = φ_d = 0`: a
discrete Wannier–Stark packet of centre `c₀`. It is solved from each end and glued at a position
`g`; the only condition is that the Casoratian of the two halves vanishes there. Every glued
packet saturates Robertson–Schrödinger and moves at `v = 4 ⟨(j − c₀)²⟩ / (ρ_d z)`.

## Main results

- `StarkPacket.glue_rec` : a glued packet solves the recurrence on `0, …, d − 1`.
- `StarkPacket.eigen` : `(T_d − iλ P_d) ψ = μ ψ`.
- `StarkPacket.tension_of_eigen` : on such an eigenvector, `⟨K_d⟩ = 2λ Var P_d`.
- `StarkPacket.exists_saturated_velocity` : a unit minimum-uncertainty state with
  `v · ρ_d z · Σ φⱼ² = 4 Σ (j − c₀)² φⱼ²`.
-/

@[expose] public noncomputable section

open Complex TransportPosition NRSInequality EigenvectorSaturation NearMaxTension GroupVelocity

namespace StarkPacket

/-! ## A. One half of the packet -/

/-- The solution from the left end: `A₋₁ = 0`, `A₀ = 1`, `Aᵢ₊₁ = Aᵢ₋₁ + (2(c − i)/z) Aᵢ`. -/
def seq (z c : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * c / z
  | i + 2 => seq z c i + 2 * (c - (i + 1 : ℕ)) / z * seq z c (i + 1)

@[simp] lemma seq_zero (z c : ℝ) : seq z c 0 = 1 := rfl

lemma seq_one (z c : ℝ) : seq z c 1 = 2 * (c - (0 : ℕ)) / z * seq z c 0 := by
  simp [seq]

lemma seq_add_two (z c : ℝ) (i : ℕ) :
    seq z c (i + 2) = seq z c i + 2 * (c - (i + 1 : ℕ)) / z * seq z c (i + 1) := rfl

/-- Up to the centre, each half is positive. -/
lemma seq_pos {z c : ℝ} (hz : 0 < z) {t : ℕ} (hc : (t : ℝ) - 1 < c) :
    ∀ i ≤ t, 0 < seq z c i := by
  have key : ∀ i, i + 1 ≤ t → 0 < seq z c i ∧ 0 < seq z c (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h
      have : (1 : ℝ) ≤ t := by exact_mod_cast h
      exact ⟨one_pos, div_pos (by linarith) hz⟩
    | succ i ih =>
      intro h
      have : ((i + 2 : ℕ) : ℝ) ≤ t := by exact_mod_cast h
      have : 0 < 2 * (c - (i + 1 : ℕ)) / z := div_pos (by push_cast at *; linarith) hz
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact ⟨h2, by rw [seq_add_two]; positivity⟩
  intro i hi
  rcases i with _ | i
  · exact one_pos
  · exact (key i hi).2

lemma continuous_seq (z : ℝ) (i : ℕ) : Continuous fun c => seq z c i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ => exact continuous_const
    | 1, _ => simp only [seq]; fun_prop
    | i + 2, ih =>
      have := ih i (by omega)
      have := ih (i + 1) (by omega)
      simp only [seq_add_two]
      fun_prop

/-! ## B. Gluing the two halves -/

variable (d g : ℕ) (z c₀ : ℝ)

/-- The left half. -/
def left (j : ℕ) : ℝ := seq z c₀ j

/-- The right half, solved from the position `d − 1`, with centre `d − 1 − c₀`. -/
def right (j : ℕ) : ℝ := seq z ((d : ℝ) - 1 - c₀) (d - 1 - j)

/-- The packet: the left half up to `g`, the right half from `g`. -/
def phi (j : ℕ) : ℝ :=
  if j ≤ g then left z c₀ j * right d z c₀ g else right d z c₀ j * left z c₀ g

/-- The Casoratian of the two halves at `g`. -/
def casoratian : ℝ :=
  left z c₀ g * right d z c₀ (g + 1) - left z c₀ (g + 1) * right d z c₀ g

variable {d g z c₀}

lemma left_rec (j : ℕ) :
    left z c₀ (j + 1) - (if 0 < j then left z c₀ (j - 1) else 0) =
      2 * (c₀ - j) / z * left z c₀ j := by
  rcases j with _ | j
  · simp [left, seq]
  · simp only [left, Nat.succ_pos, ite_true, Nat.add_sub_cancel, seq_add_two]
    push_cast
    ring

lemma right_rec {j : ℕ} (hj0 : 0 < j) (hj : j < d) :
    (if j + 1 < d then right d z c₀ (j + 1) else 0) - right d z c₀ (j - 1) =
      2 * (c₀ - j) / z * right d z c₀ j := by
  obtain ⟨i, rfl⟩ : ∃ i, d = j + 1 + i := ⟨d - j - 1, by omega⟩
  rcases i with _ | i
  · simp only [right, add_zero, lt_self_iff_false, ite_false,
      show j + 1 - 1 - (j - 1) = 1 by omega, show j + 1 - 1 - j = 0 by omega, seq_one]
    simp [seq]
    ring
  · simp only [right, show j + 1 < j + 1 + (i + 1) by omega, ite_true,
      show j + 1 + (i + 1) - 1 - (j + 1) = i by omega,
      show j + 1 + (i + 1) - 1 - (j - 1) = i + 2 by omega,
      show j + 1 + (i + 1) - 1 - j = i + 1 by omega, seq_add_two]
    push_cast
    ring

lemma phi_of_le {j : ℕ} (h : j ≤ g) : phi d g z c₀ j = left z c₀ j * right d z c₀ g := by
  simp [phi, h]

lemma phi_of_lt {j : ℕ} (h : g < j) : phi d g z c₀ j = right d z c₀ j * left z c₀ g := by
  simp [phi, show ¬ j ≤ g by omega]

/-- **Gluing.** If the Casoratian vanishes, the packet solves the recurrence at every position. -/
theorem glue_rec (hg : g + 1 < d) (hW : casoratian d g z c₀ = 0) {j : ℕ} (hj : j < d) :
    (if j + 1 < d then phi d g z c₀ (j + 1) else 0) -
        (if 0 < j then phi d g z c₀ (j - 1) else 0) =
      2 * (c₀ - j) / z * phi d g z c₀ j := by
  have hW' : right d z c₀ (g + 1) * left z c₀ g = left z c₀ (g + 1) * right d z c₀ g := by
    unfold casoratian at hW
    linarith
  have hl := left_rec (z := z) (c₀ := c₀) j
  rcases le_or_gt j g with h | h
  · have hp : phi d g z c₀ (j + 1) = left z c₀ (j + 1) * right d z c₀ g := by
      rcases Nat.lt_or_ge j g with h' | h'
      · exact phi_of_le (by omega)
      · rw [le_antisymm h h', phi_of_lt (by omega), hW']
    simp only [show j + 1 < d by omega, ↓reduceIte, hp, phi_of_le h]
    by_cases h0 : 0 < j
    · simp only [h0, ↓reduceIte, phi_of_le (show j - 1 ≤ g by omega)] at hl ⊢
      linear_combination right d z c₀ g * hl
    · simp only [h0, ↓reduceIte] at hl ⊢
      linear_combination right d z c₀ g * hl
  · have hr := right_rec (z := z) (c₀ := c₀) (show 0 < j by omega) hj
    have hm : phi d g z c₀ (j - 1) = right d z c₀ (j - 1) * left z c₀ g := by
      rcases Nat.lt_or_ge g (j - 1) with h' | h'
      · exact phi_of_lt h'
      · rw [phi_of_le h', show j - 1 = g by omega, mul_comm]
    simp only [show 0 < j by omega, ↓reduceIte, hm, phi_of_lt h]
    by_cases h1 : j + 1 < d
    · simp only [h1, ↓reduceIte, phi_of_lt (show g < j + 1 by omega)] at hr ⊢
      linear_combination left z c₀ g * hr
    · simp only [h1, ↓reduceIte] at hr ⊢
      linear_combination left z c₀ g * hr

/-! ## C. The eigenvalue equation -/

lemma TdOp_apply (u : Hd d) (i : Fin d) :
    TdOp d u i =
      ((if h : i.val + 1 < d then u ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then u ⟨i.val - 1, by omega⟩ else 0)) / (rho d : ℂ) := by
  rw [← Ad_mulVec_apply]
  simp only [TdOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Td,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma PdOp_apply (u : Hd d) (i : Fin d) : PdOp d u i = (posCoord d i : ℂ) * u i := by
  simp [PdOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Pd]

variable (d g z c₀) in
/-- The state `ψⱼ = (−i)ʲ φⱼ`. -/
def psi : Hd d := WithLp.toLp 2 fun j => (-I) ^ (j : ℕ) * (phi d g z c₀ j : ℂ)

variable (d z) in
/-- `λ = (d − 1)/(ρ_d z)`. -/
def lam : ℝ := ((d : ℝ) - 1) / (rho d * z)

variable (d z c₀) in
/-- `μ = −i (2c₀ − (d − 1))/(ρ_d z)`. -/
def mu : ℂ := -I * (((2 * c₀ - ((d : ℝ) - 1)) / (rho d * z) : ℝ) : ℂ)

lemma psi_apply (j : Fin d) : psi d g z c₀ j = (-I) ^ (j : ℕ) * (phi d g z c₀ j : ℂ) := rfl

lemma TdOp_psi_apply (i : Fin d) :
    TdOp d (psi d g z c₀) i =
      (-I) ^ (i : ℕ) * (-I) *
        (((if i.val + 1 < d then phi d g z c₀ (i.val + 1) else 0) -
          (if 0 < i.val then phi d g z c₀ (i.val - 1) else 0) : ℝ) : ℂ) / (rho d : ℂ) := by
  rw [TdOp_apply]
  simp only [psi_apply]
  congr 1
  by_cases h1 : i.val + 1 < d <;> by_cases h0 : 0 < i.val <;>
    simp only [h1, h0, dite_true, dite_false, ite_true, ite_false] <;> push_cast
  · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ, pow_succ]
    ring_nf
    rw [I_sq]
    ring
  · rw [pow_succ]
    ring
  · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring_nf
    rw [I_sq]
    ring
  · ring

/-- **The eigenvalue equation** `(T_d − iλ P_d) ψ = μ ψ`. -/
theorem eigen (hd : 2 ≤ d) (hg : g + 1 < d) (hz : z ≠ 0) (hW : casoratian d g z c₀ = 0) :
    TdOp d (psi d g z c₀) - (I * (lam d z : ℂ)) • PdOp d (psi d g z c₀) =
      mu d z c₀ • psi d g z c₀ := by
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact_mod_cast (show (d : ℝ) - 1 ≠ 0 by linarith)
  have hr : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, TdOp_psi_apply, PdOp_apply,
    psi_apply, glue_rec hg hW i.isLt, lam, mu, posCoord]
  push_cast
  field_simp
  ring_nf

/-! ## D. Eigenvectors of `T_d − iλ P_d` in motion -/

/-- On a unit eigenvector of `T_d − iλ P_d`, the tension is `2λ Var P_d`. -/
lemma tension_of_eigen {ψ : Hd d} (hψ : ‖ψ‖ = 1) (l : ℝ) (m : ℂ)
    (h : TdOp d ψ - (I * (l : ℂ)) • PdOp d ψ = m • ψ) :
    tension d ψ = 2 * l * variance (PdOp d) ψ := by
  have hc := annihilated_of_eigenvector (TdOp_isSymmetric d) (PdOp_isSymmetric d) hψ l m h
  rw [tension, re_inner_KdOp, ← imPart_eq_im_inner (TdOp_isSymmetric d) (PdOp_isSymmetric d),
    imPart, hc, inner_smul_left, inner_self_eq_norm_sq_to_K, variance]
  simp [Complex.mul_im, pow_two]
  ring

/-- On a unit eigenvector of `T_d − iλ P_d` with eigenvalue `μ`, `λ ⟨P_d⟩ = −Im μ`. -/
lemma mean_of_eigen {ψ : Hd d} (hψ : ‖ψ‖ = 1) (l : ℝ) (m : ℂ)
    (h : TdOp d ψ - (I * (l : ℂ)) • PdOp d ψ = m • ψ) :
    l * mean (PdOp d) ψ = -m.im := by
  have h1 := congrArg (inner ℂ ψ) h
  rw [inner_sub_right, inner_smul_right, inner_smul_right, inner_self_apply_real
    (TdOp_isSymmetric d), inner_self_apply_real (PdOp_isSymmetric d),
    inner_self_eq_norm_sq_to_K, hψ] at h1
  have := congrArg Complex.im h1
  simp at this
  linarith

/-! ## E. Stark packets are minimum-uncertainty states in motion -/

variable (d g z c₀) in
/-- `N = Σ φⱼ²`. -/
def normSq : ℝ := ∑ j : Fin d, phi d g z c₀ j ^ 2

variable (d g z c₀) in
/-- `X = Σ (j − c₀)² φⱼ²`. -/
def spread : ℝ := ∑ j : Fin d, ((j : ℝ) - c₀) ^ 2 * phi d g z c₀ j ^ 2

lemma norm_psi_sq : ‖psi d g z c₀‖ ^ 2 = normSq d g z c₀ := by
  simp [EuclideanSpace.norm_sq_eq, psi_apply, normSq, norm_pow, sq_abs]

lemma normSq_pos (hg : g < d) (hz : 0 < z) (hc₁ : (g : ℝ) - 1 < c₀) (hc₂ : c₀ < g + 1) :
    0 < normSq d g z c₀ := by
  have hR : ((d - 1 - g : ℕ) : ℝ) - 1 < (d : ℝ) - 1 - c₀ := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    linarith
  have h : 0 < phi d g z c₀ g := by
    rw [phi_of_le le_rfl]
    exact mul_pos (seq_pos hz hc₁ g le_rfl) (seq_pos hz hR _ le_rfl)
  exact (pow_pos h 2).trans_le <| Finset.single_le_sum
    (f := fun j : Fin d => phi d g z c₀ j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ⟨g, hg⟩)

/-- **Stark packets.** A glued packet, normalized, saturates Robertson–Schrödinger and moves at
`v = 4 X/(ρ_d z N)`. -/
theorem exists_saturated_velocity (hd : 2 ≤ d) (hg : g + 1 < d) (hz : 0 < z)
    (hc₁ : (g : ℝ) - 1 < c₀) (hc₂ : c₀ < g + 1) (hW : casoratian d g z c₀ = 0) :
    ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ surplus d ψ = 0 ∧
      velocity d ψ * (rho d * z) * normSq d g z c₀ = 4 * spread d g z c₀ := by
  have hN := normSq_pos (d := d) (show g < d by omega) hz hc₁ hc₂
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hr := rho_pos d hd
  set s : ℝ := (√(normSq d g z c₀))⁻¹
  have hs : s ^ 2 = 1 / normSq d g z c₀ := by simp [s, inv_pow, Real.sq_sqrt hN.le]
  set ψ : Hd d := (s : ℂ) • psi d g z c₀
  have hψ : ‖ψ‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp ?_
    rw [norm_smul, mul_pow, norm_psi_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs]
    field_simp
  have heig : TdOp d ψ - (I * (lam d z : ℂ)) • PdOp d ψ = mu d z c₀ • ψ := by
    simp only [ψ, map_smul, smul_comm _ (s : ℂ), ← smul_sub, eigen hd hg hz.ne' hW]
  have hc := annihilated_of_eigenvector (TdOp_isSymmetric d) (PdOp_isSymmetric d) hψ _ _ heig
  refine ⟨ψ, hψ, (gramDefectAt_eq_zero_iff _ _ _).2 (Or.inr ⟨_, hc⟩), ?_⟩
  have hmean : mean (PdOp d) ψ = (2 * c₀ - ((d : ℝ) - 1)) / ((d : ℝ) - 1) := by
    have h := mean_of_eigen hψ _ _ heig
    simp only [mu, lam, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at h
    field_simp at h ⊢
    linarith
  have hvar : variance (PdOp d) ψ =
      s ^ 2 * (4 / ((d : ℝ) - 1) ^ 2 * spread d g z c₀) := by
    rw [variance, centered, hmean, EuclideanSpace.norm_sq_eq, spread, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (PdOp d ψ - (((2 * c₀ - ((d : ℝ) - 1)) / ((d : ℝ) - 1) : ℝ) : ℂ) • ψ) j =
        ((2 * ((j : ℝ) - c₀) / ((d : ℝ) - 1) * s * phi d g z c₀ j : ℝ) : ℂ) *
          (-I) ^ (j : ℕ) := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PdOp_apply, ψ, psi_apply,
        posCoord]
      push_cast
      field_simp
      ring
    rw [hj, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  rw [velocity, tension_of_eigen hψ _ _ heig, hvar, hs, lam]
  field_simp

end StarkPacket

end

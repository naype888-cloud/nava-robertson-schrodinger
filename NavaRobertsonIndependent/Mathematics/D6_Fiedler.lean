/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D5_MaximalTension

/-!
# D6 — The spectrum of the path

Explicit diagonalization of the adjacency `A_d` (sine modes) and of `K_d = i[T_d, P_d]` (phase
modes) on `pathGraph d`, with the whole spectrum in closed form. The fundamental phase mode is
the Fiedler vector of `D5`, the extremal eigenvector of `K_d`.

## Main results

- `TransportPosition.eigenvalueAd_exhausts_spectrum` : the sine modes give every eigenvalue
  `2 cos(kπ/(d+1))` of `A_d`.
- `TransportPosition.KdOp_eigenvalue_exhausts_spectrum` : the phase modes give every eigenvalue
  of `K_d`.
- `TransportPosition.KdOp_fiedlerVec` : `ψ*` is the top eigenvector of `K_d`, and
  `specRadius_KdOp_eq_step` its eigenvalue `2/(d−1)`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace TransportPosition

theorem sum_cond_succ {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if i.val + 1 = j.val then f j else 0) =
      if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0 := by
  classical
  by_cases h : i.val + 1 < d
  · let s : Fin d := ⟨i.val + 1, h⟩
    have hs (j : Fin d) : i.val + 1 = j.val ↔ s = j := by
      simp only [s]
      exact ⟨fun e => Fin.ext e, fun e => by
        have := congrArg Fin.val e
        simpa [s] using this⟩
    simp_rw [hs]
    simp [h, s]
  · have hs (j : Fin d) : i.val + 1 ≠ j.val := by omega
    simp [h, hs]

theorem sum_cond_pred {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if j.val + 1 = i.val then f j else 0) =
      if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0 := by
  classical
  by_cases h : 0 < i.val
  · let p : Fin d := ⟨i.val - 1, by omega⟩
    have hp (j : Fin d) : j.val + 1 = i.val ↔ p = j := by
      simp only [p]
      constructor
      · intro e
        apply Fin.ext
        change i.val - 1 = j.val
        omega
      · intro e
        have he := congrArg Fin.val e
        change i.val - 1 = j.val at he
        omega
    simp_rw [hp]
    simp [h, p]
  · have hp (j : Fin d) : j.val + 1 ≠ i.val := by omega
    simp [h, hp]

theorem sum_minStep
    {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if MinStep i j then f j else 0) =
      (if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0) +
      (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  rw [show (∑ j : Fin d, if MinStep i j then f j else 0) =
      (∑ j : Fin d, if i.val + 1 = j.val then f j else 0) +
      (∑ j : Fin d, if j.val + 1 = i.val then f j else 0) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold MinStep
    by_cases h₁ : i.val + 1 = j.val
    · have h₂ : j.val + 1 ≠ i.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val + 1 = i.val <;> simp [h₁, h₂]]
  rw [sum_cond_succ, sum_cond_pred]

theorem Ad_mulVec_apply
    {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (Ad d).mulVec f i =
      (if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0) +
      (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Ad]
  simp_rw [ite_mul, one_mul, zero_mul]
  exact sum_minStep i f

noncomputable def modeAngle (d : ℕ) (k : Fin d) : ℝ :=
  ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)

noncomputable def sineMode (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => (Real.sin (((j.val : ℝ) + 1) * modeAngle d k) : ℂ)

theorem sin_recurrence (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + 2) * a) + Real.sin ((n : ℝ) * a) =
      2 * Real.cos a * Real.sin (((n : ℝ) + 1) * a) := by
  rw [show ((n : ℝ) + 2) * a = ((n : ℝ) + 1) * a + a by ring,
    Real.sin_add,
    show (n : ℝ) * a = ((n : ℝ) + 1) * a - a by ring,
    Real.sin_sub]
  ring

theorem sin_upper_boundary
    {d : ℕ} (k : Fin d) :
    Real.sin (((d : ℝ) + 1) * modeAngle d k) = 0 := by
  unfold modeAngle
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [show ((d : ℝ) + 1) *
      (((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)) =
      (k.val + 1 : ℕ) * Real.pi by
        push_cast
        field_simp]
  exact Real.sin_nat_mul_pi (k.val + 1)

theorem Ad_sineMode
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    (Ad d).mulVec (sineMode d k) =
      fun i => (2 * Real.cos (modeAngle d k) : ℂ) * sineMode d k i := by
  funext i
  rw [Ad_mulVec_apply]
  by_cases hs : i.val + 1 < d
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, dite_true, sineMode]
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hsucc : i.val + 1 + 1 = i.val + 2 := by omega
      have hpredR : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hpred
      have hsuccR : ((i.val + 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) + 2 := by
        exact_mod_cast hsucc
      rw [hpredR, hsuccR]
      exact_mod_cast sin_recurrence (modeAngle d k) i.val
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, dite_true, dite_false, add_zero, sineMode]
      simp only [hi0, Nat.cast_zero, zero_add, Nat.cast_one]
      exact_mod_cast (by
        simpa using sin_recurrence (modeAngle d k) 0)
  · have hilast : i.val + 1 = d := by omega
    by_cases hp : 0 < i.val
    · simp only [hs, hp, dite_false, dite_true, zero_add, sineMode]
      have hrec := sin_recurrence (modeAngle d k) i.val
      have hzero :
          Real.sin (((i.val : ℝ) + 2) * modeAngle d k) = 0 := by
        rw [show ((i.val : ℝ) + 2) = (d : ℝ) + 1 by
          exact_mod_cast (show i.val + 2 = d + 1 by omega)]
        exact sin_upper_boundary k
      rw [hzero, zero_add] at hrec
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hpredR : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hpred
      rw [hpredR]
      exact_mod_cast hrec
    · have hd1 : d = 1 := by omega
      subst d
      have hk0 : k = 0 := Subsingleton.elim _ _
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst k
      subst i
      norm_num [sineMode, modeAngle]

noncomputable def eigenvalueAd (d : ℕ) (k : Fin d) : ℂ :=
  (2 * Real.cos (modeAngle d k) : ℝ)

theorem modeAngle_mem_Icc {d : ℕ} (k : Fin d) :
    modeAngle d k ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · unfold modeAngle
    positivity
  · unfold modeAngle
    have hk : (k.val : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      exact_mod_cast (show k.val + 1 ≤ d + 1 by omega)
    have hd : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) ≤
          ((d : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
            gcongr
      _ = Real.pi := by field_simp

theorem eigenvalueAd_injective {d : ℕ} :
    Function.Injective (eigenvalueAd d) := by
  intro k l hkl
  have hcos :
      Real.cos (modeAngle d k) = Real.cos (modeAngle d l) := by
    apply mul_left_cancel₀ (a := (2 : ℝ)) (by norm_num)
    apply Complex.ofReal_injective
    simpa [eigenvalueAd] using hkl
  have hang : modeAngle d k = modeAngle d l :=
    Real.strictAntiOn_cos.injOn
      (modeAngle_mem_Icc k) (modeAngle_mem_Icc l) hcos
  apply Fin.ext
  unfold modeAngle at hang
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  have : (k.val : ℝ) = (l.val : ℝ) := by
    field_simp at hang
    nlinarith
  exact_mod_cast this

theorem sineMode_ne_zero {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    sineMode d k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, hd⟩
  have ha0 : 0 < modeAngle d k := by
    unfold modeAngle
    positivity
  have hapi : modeAngle d k < Real.pi := by
    unfold modeAngle
    have hk : (k.val : ℝ) + 1 < (d : ℝ) + 1 := by
      exact_mod_cast Nat.add_lt_add_right k.isLt 1
    have hdR : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) <
          ((d : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
            gcongr
      _ = Real.pi := by field_simp
  have hs := (Real.sin_pos_of_pos_of_lt_pi ha0 hapi).ne'
  apply Complex.ofReal_ne_zero.mpr hs
  simpa [sineMode] using h0

theorem sineMode_hasEigenvector
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (Matrix.toLin' (Ad d))
      (eigenvalueAd d k) (sineMode d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    simpa [eigenvalueAd] using congrFun (Ad_sineMode hd k) i
  · exact sineMode_ne_zero hd k

theorem sineModes_linearIndependent
    {d : ℕ} (hd : 1 ≤ d) :
    LinearIndependent ℂ (sineMode d) :=
  Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (Ad d))
    (eigenvalueAd d) eigenvalueAd_injective (sineMode d)
    (sineMode_hasEigenvector hd)

noncomputable def sineModeBasis
    {d : ℕ} (hd : 1 ≤ d) : Module.Basis (Fin d) ℂ (Fin d → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (sineModes_linearIndependent hd)

theorem sineModeBasis_apply
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    sineModeBasis hd k = sineMode d k := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (sineModes_linearIndependent hd)) k

theorem Ad_eq_sum_modes
    {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℂ) :
    Matrix.toLin' (Ad d) v =
      ∑ k : Fin d,
        (sineModeBasis hd).repr v k •
          (eigenvalueAd d k • sineMode d k) := by
  calc
    Matrix.toLin' (Ad d) v =
        Matrix.toLin' (Ad d)
          (∑ k, (sineModeBasis hd).repr v k • sineModeBasis hd k) := by
            rw [(sineModeBasis hd).sum_repr v]
    _ = ∑ k, (sineModeBasis hd).repr v k •
          Matrix.toLin' (Ad d) (sineModeBasis hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [sineModeBasis_apply]
      congr 1
      rw [Matrix.toLin'_apply]
      ext i
      simpa [eigenvalueAd] using congrFun (Ad_sineMode hd k) i

theorem repr_Ad
    {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℂ) (k : Fin d) :
    (sineModeBasis hd).repr (Matrix.toLin' (Ad d) v) k =
      eigenvalueAd d k * (sineModeBasis hd).repr v k := by
  rw [Ad_eq_sum_modes hd v, map_sum]
  classical
  simp [← sineModeBasis_apply hd, Finsupp.single_apply, mul_comm]

theorem eigenvalueAd_exhausts_spectrum
    {d : ℕ} (hd : 1 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (Ad d)) μ) :
    ∃ k : Fin d, μ = eigenvalueAd d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (sineModeBasis hd).repr v ≠ 0 := by
    simpa using (sineModeBasis hd).repr.injective.ne hv.2
  have hk : ∃ k : Fin d, (sineModeBasis hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  obtain ⟨k, hk⟩ := hk
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hc := congrArg (fun w => (sineModeBasis hd).repr w k) heig
  rw [repr_Ad] at hc
  simp only [map_smul] at hc
  exact ⟨k, (mul_right_cancel₀ hk hc).symm⟩

theorem fiedlerAngle_le_modeAngle
    {d : ℕ} (k : Fin d) :
    fiedlerAngle d ≤ modeAngle d k := by
  unfold fiedlerAngle modeAngle
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hk : (1 : ℝ) ≤ (k.val : ℝ) + 1 := by
    exact_mod_cast (show 1 ≤ k.val + 1 by omega)
  calc
    Real.pi / ((d : ℝ) + 1) =
        1 * Real.pi / ((d : ℝ) + 1) := by ring
    _ ≤ ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
      gcongr

theorem modeAngle_le_pi_sub_fiedlerAngle
    {d : ℕ} (k : Fin d) :
    modeAngle d k ≤ Real.pi - fiedlerAngle d := by
  unfold fiedlerAngle modeAngle
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hk : (k.val : ℝ) + 1 ≤ d := by
    exact_mod_cast (show k.val + 1 ≤ d by omega)
  calc
    ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) ≤
        (d : ℝ) * Real.pi / ((d : ℝ) + 1) := by
          gcongr
    _ = Real.pi - Real.pi / ((d : ℝ) + 1) := by
      field_simp
      ring

theorem abs_cos_modeAngle_le_cos_fiedlerAngle
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    |Real.cos (modeAngle d k)| ≤ Real.cos (fiedlerAngle d) := by
  apply abs_le.mpr
  constructor
  · rw [← Real.cos_pi_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact (modeAngle_mem_Icc k).1
    · have hθ : 0 ≤ fiedlerAngle d := by
        unfold fiedlerAngle
        positivity
      linarith [Real.pi_pos]
    · exact modeAngle_le_pi_sub_fiedlerAngle k
  · apply Real.cos_le_cos_of_nonneg_of_le_pi
    · unfold fiedlerAngle
      positivity
    · exact (modeAngle_mem_Icc k).2
    · exact fiedlerAngle_le_modeAngle k

theorem abs_eigenvalueAd_le_rho
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    ‖eigenvalueAd d k‖ ≤ rho d := by
  rw [eigenvalueAd, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [rho]
  exact mul_le_mul_of_nonneg_left
    (by simpa [fiedlerAngle] using
      abs_cos_modeAngle_le_cos_fiedlerAngle hd k)
    (by norm_num)

noncomputable def Kmat (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Complex.I • ((Td d * Pd d) - (Pd d * Td d))

noncomputable def phase (j : ℕ) : ℂ := (-Complex.I) ^ j

noncomputable def phaseMode (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => phase j.val * sineMode d k j

theorem Kmat_apply
    (d : ℕ) (i j : Fin d) :
    Kmat d i j =
      Complex.I * Td d i j *
        ((posCoord d j : ℂ) - posCoord d i) := by
  rw [Kmat]
  change Complex.I * (((Td d * Pd d) - (Pd d * Td d)) i j) = _
  rw [Matrix.sub_apply,
    Td_mul_Pd_apply, Pd_mul_Td_apply]
  ring

theorem neighbour_phase_term
    {d : ℕ} (hd : 2 ≤ d) {i j : Fin d}
    (hpaso : MinStep i j) (z : ℂ) :
    Kmat d i j * (phase j.val * z) =
      ((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) *
        (phase i.val * z) := by
  have hrhoR : rho d ≠ 0 := (rho_pos d hd).ne'
  have hrhoC : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrhoR
  have hdsubR : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  rw [Kmat_apply]
  have hTd : Td d i j = 1 / (rho d : ℂ) := by
    simp [Td, Ad, hpaso]
  rw [hTd]
  rcases hpaso with hij | hji
  · have hpos := posCoord_succ_sub d hd i j hij
    have hposC :
        (posCoord d j : ℂ) - posCoord d i =
          ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
      exact_mod_cast hpos
    have hpow : phase j.val = phase i.val * (-Complex.I) := by
      unfold phase
      rw [← hij, pow_succ]
    rw [hpow, hposC]
    push_cast
    field_simp [hrhoR, hdsubR]
    ring_nf
    simp [Complex.I_sq]
  · have hpos := posCoord_succ_sub d hd j i hji
    have hposC :
        (posCoord d j : ℂ) - posCoord d i =
          -((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
      exact_mod_cast (show posCoord d j - posCoord d i =
        -(2 / ((d : ℝ) - 1)) by linarith)
    have hpow : phase i.val = phase j.val * (-Complex.I) := by
      unfold phase
      rw [← hji, pow_succ]
    have hI : phase j.val = phase i.val * Complex.I := by
      calc
        phase j.val = phase j.val * ((-Complex.I) * Complex.I) := by
          rw [show (-Complex.I) * Complex.I = 1 by
            apply Complex.ext <;> norm_num]
          ring
        _ = phase i.val * Complex.I := by rw [hpow]; ring
    rw [hI, hposC]
    push_cast
    field_simp [hrhoR, hdsubR]
    ring_nf
    simp [Complex.I_sq]

theorem Kmat_mulVec_phaseMode
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    (Kmat d).mulVec (phaseMode d k) =
      fun i =>
        (((2 / ((d : ℝ) - 1)) *
          (2 * Real.cos (modeAngle d k) / rho d) : ℝ) : ℂ) *
          phaseMode d k i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [show (∑ j : Fin d, Kmat d i j * phaseMode d k j) =
      ∑ j : Fin d,
        if MinStep i j then
          (((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) *
            (phase i.val * sineMode d k j))
        else 0 by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hp : MinStep i j
      · simp only [hp, ↓reduceIte, phaseMode]
        exact neighbour_phase_term hd hp (sineMode d k j)
      · have hz : Kmat d i j = 0 := by
          rw [Kmat_apply]
          simp [Td, Ad, hp]
        simp [hp, hz]]
  rw [show (∑ x : Fin d,
      if MinStep i x then
        (((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) *
          (phase i.val * sineMode d k x))
      else 0) =
      (((2 / ((d : ℝ) - 1) / rho d : ℝ) : ℂ) * phase i.val) *
        ∑ x : Fin d, if MinStep i x then sineMode d k x else 0 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : MinStep i x <;> simp [hp]
    ring]
  rw [show (∑ j : Fin d, if MinStep i j then sineMode d k j else 0) =
      (Ad d).mulVec (sineMode d k) i by
        simp only [Matrix.mulVec, dotProduct, Ad]
        simp_rw [ite_mul, one_mul, zero_mul]]
  rw [congrFun (Ad_sineMode (by omega) k) i]
  simp only [phaseMode]
  push_cast
  ring

noncomputable def eigenvalueK (d : ℕ) (k : Fin d) : ℂ :=
  ((((2 / ((d : ℝ) - 1)) / rho d : ℝ) : ℂ) * eigenvalueAd d k)

theorem Kmat_phaseMode
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Matrix.toLin' (Kmat d) (phaseMode d k) =
      eigenvalueK d k • phaseMode d k := by
  rw [Matrix.toLin'_apply]
  ext i
  change (Kmat d).mulVec (phaseMode d k) i =
    eigenvalueK d k * phaseMode d k i
  rw [congrFun (Kmat_mulVec_phaseMode hd k) i]
  simp only [eigenvalueK, eigenvalueAd]
  push_cast
  ring

theorem phaseMode_ne_zero
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    phaseMode d k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  have hs := sineMode_ne_zero (by omega : 1 ≤ d) k
  apply hs
  funext j
  have hf : phase j.val ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  have hj := congrFun h j
  simp only [phaseMode] at hj
  exact (mul_eq_zero.mp hj).resolve_left hf

theorem eigenvalueK_injective
    {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (eigenvalueK d) := by
  intro k l hkl
  apply eigenvalueAd_injective
  unfold eigenvalueK at hkl
  have hcR : (2 / ((d : ℝ) - 1)) / rho d ≠ 0 := by
    have hdR : (d : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    exact div_ne_zero (div_ne_zero (by norm_num) hdR) (rho_pos d hd).ne'
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hcR) hkl

theorem phaseMode_hasEigenvector
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (Matrix.toLin' (Kmat d))
      (eigenvalueK d k) (phaseMode d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact Kmat_phaseMode hd k
  · exact phaseMode_ne_zero hd k

theorem phaseModes_linearIndependent
    {d : ℕ} (hd : 2 ≤ d) :
    LinearIndependent ℂ (phaseMode d) :=
  Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (Kmat d))
    (eigenvalueK d) (eigenvalueK_injective hd) (phaseMode d)
    (phaseMode_hasEigenvector hd)

noncomputable def phaseModeBasis
    {d : ℕ} (hd : 2 ≤ d) : Module.Basis (Fin d) ℂ (Fin d → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (phaseModes_linearIndependent hd)

theorem phaseModeBasis_apply
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    phaseModeBasis hd k = phaseMode d k := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (phaseModes_linearIndependent hd)) k

theorem Kmat_eq_sum_modes
    {d : ℕ} (hd : 2 ≤ d) (v : Fin d → ℂ) :
    Matrix.toLin' (Kmat d) v =
      ∑ k : Fin d,
        (phaseModeBasis hd).repr v k •
          (eigenvalueK d k • phaseMode d k) := by
  calc
    Matrix.toLin' (Kmat d) v =
        Matrix.toLin' (Kmat d)
          (∑ k, (phaseModeBasis hd).repr v k • phaseModeBasis hd k) := by
            rw [(phaseModeBasis hd).sum_repr v]
    _ = ∑ k, (phaseModeBasis hd).repr v k •
          Matrix.toLin' (Kmat d) (phaseModeBasis hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [phaseModeBasis_apply]
      congr 1
      exact Kmat_phaseMode hd k

theorem repr_Kmat
    {d : ℕ} (hd : 2 ≤ d) (v : Fin d → ℂ) (k : Fin d) :
    (phaseModeBasis hd).repr (Matrix.toLin' (Kmat d) v) k =
      eigenvalueK d k * (phaseModeBasis hd).repr v k := by
  rw [Kmat_eq_sum_modes hd v, map_sum]
  classical
  simp [← phaseModeBasis_apply hd, Finsupp.single_apply, mul_comm]

theorem Kmat_eigenvalue_exhausts_spectrum
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (Kmat d)) μ) :
    ∃ k : Fin d, μ = eigenvalueK d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (phaseModeBasis hd).repr v ≠ 0 := by
    simpa using (phaseModeBasis hd).repr.injective.ne hv.2
  obtain ⟨k, hk⟩ :
      ∃ k : Fin d, (phaseModeBasis hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoord := congrArg (fun w => (phaseModeBasis hd).repr w k) heig
  rw [repr_Kmat] at hcoord
  simp only [map_smul] at hcoord
  exact ⟨k, (mul_right_cancel₀ hk hcoord).symm⟩

theorem abs_eigenvalueK_le_step
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    ‖eigenvalueK d k‖ ≤ 2 / ((d : ℝ) - 1) := by
  have hδ : 0 ≤ 2 / ((d : ℝ) - 1) := by
    have hdsub : 0 < (d : ℝ) - 1 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    exact div_nonneg (by norm_num) hdsub.le
  have hρ := rho_pos d hd
  rw [eigenvalueK, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hδ hρ.le)]
  calc
    (2 / ((d : ℝ) - 1) / rho d) * ‖eigenvalueAd d k‖ ≤
        (2 / ((d : ℝ) - 1) / rho d) * rho d := by
          gcongr
          exact abs_eigenvalueAd_le_rho hd k
    _ = 2 / ((d : ℝ) - 1) := by
      field_simp [(rho_pos d hd).ne']

theorem KdOp_eq_Kmat (d : ℕ) :
    KdOp d = Matrix.toEuclideanLin (Kmat d) := by
  unfold KdOp SpectralExtremal.observableTension Kmat
  rw [commutator_TdOp_PdOp_eq_matrix]
  exact (Matrix.toEuclideanLin :
    Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] (Hd d →ₗ[ℂ] Hd d)).map_smul
      Complex.I ((Td d * Pd d) - (Pd d * Td d)) |>.symm

noncomputable def phaseModeHd (d : ℕ) (k : Fin d) : Hd d :=
  WithLp.toLp 2 (phaseMode d k)

theorem KdOp_phaseModeHd
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    KdOp d (phaseModeHd d k) =
      eigenvalueK d k • phaseModeHd d k := by
  rw [KdOp_eq_Kmat]
  change WithLp.toLp 2 ((Kmat d).mulVec (phaseMode d k)) =
    WithLp.toLp 2 (fun i => eigenvalueK d k * phaseMode d k i)
  congr 1
  funext i
  simpa [smul_eq_mul] using congrFun (Kmat_phaseMode hd k) i

theorem phaseModeHd_ne_zero
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    phaseModeHd d k ≠ 0 := by
  exact (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.injective.ne
    (phaseMode_ne_zero hd k)

theorem phaseModeHd_hasEigenvector
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (KdOp d)
      (eigenvalueK d k) (phaseModeHd d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact KdOp_phaseModeHd hd k
  · exact phaseModeHd_ne_zero hd k

theorem phaseModesHd_linearIndependent
    {d : ℕ} (hd : 2 ≤ d) :
    LinearIndependent ℂ (phaseModeHd d) :=
  Module.End.eigenvectors_linearIndependent' (KdOp d)
    (eigenvalueK d) (eigenvalueK_injective hd) (phaseModeHd d)
    (phaseModeHd_hasEigenvector hd)

noncomputable def phaseModeBasisHd
    {d : ℕ} (hd : 2 ≤ d) : Module.Basis (Fin d) ℂ (Hd d) :=
  (phaseModeBasis hd).map (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm

theorem phaseModeBasisHd_apply
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    phaseModeBasisHd hd k = phaseModeHd d k := by
  simp [phaseModeBasisHd, phaseModeHd, phaseModeBasis_apply]

theorem KdOp_eq_sum_modes
    {d : ℕ} (hd : 2 ≤ d) (v : Hd d) :
    KdOp d v =
      ∑ k : Fin d,
        (phaseModeBasisHd hd).repr v k •
          (eigenvalueK d k • phaseModeHd d k) := by
  calc
    KdOp d v =
        KdOp d
          (∑ k, (phaseModeBasisHd hd).repr v k •
            phaseModeBasisHd hd k) := by
              rw [(phaseModeBasisHd hd).sum_repr v]
    _ = ∑ k, (phaseModeBasisHd hd).repr v k •
          KdOp d (phaseModeBasisHd hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [phaseModeBasisHd_apply]
      congr 1
      exact KdOp_phaseModeHd hd k

theorem repr_KdOp
    {d : ℕ} (hd : 2 ≤ d) (v : Hd d) (k : Fin d) :
    (phaseModeBasisHd hd).repr (KdOp d v) k =
      eigenvalueK d k * (phaseModeBasisHd hd).repr v k := by
  rw [KdOp_eq_sum_modes hd v, map_sum]
  classical
  simp [← phaseModeBasisHd_apply hd, Finsupp.single_apply, mul_comm]

theorem KdOp_eigenvalue_exhausts_spectrum
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (KdOp d) μ) :
    ∃ k : Fin d, μ = eigenvalueK d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (phaseModeBasisHd hd).repr v ≠ 0 := by
    simpa using (phaseModeBasisHd hd).repr.injective.ne hv.2
  obtain ⟨k, hk⟩ :
      ∃ k : Fin d, (phaseModeBasisHd hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoord := congrArg (fun w => (phaseModeBasisHd hd).repr w k) heig
  rw [repr_KdOp] at hcoord
  simp only [map_smul] at hcoord
  exact ⟨k, (mul_right_cancel₀ hk hcoord).symm⟩

theorem abs_eigenvalue_KdOp_le
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (KdOp d) μ) :
    ‖μ‖ ≤ 2 / ((d : ℝ) - 1) := by
  obtain ⟨k, rfl⟩ := KdOp_eigenvalue_exhausts_spectrum hd hμ
  exact abs_eigenvalueK_le_step hd k

theorem eigenvalueK_fundamental
    (d : ℕ) (hd : 2 ≤ d) :
    eigenvalueK d ⟨0, by omega⟩ =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
  have hρ : rho d ≠ 0 := (rho_pos d hd).ne'
  have hdsub : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  simp only [eigenvalueK, eigenvalueAd, modeAngle,
    Nat.cast_zero, zero_add]
  rw [show (1 : ℝ) * Real.pi / ((d : ℝ) + 1) =
    Real.pi / ((d : ℝ) + 1) by ring]
  rw [show (2 * Real.cos (Real.pi / ((d : ℝ) + 1)) : ℝ) = rho d by
    rfl]
  push_cast
  field_simp [hρ, hdsub]

theorem phaseModeHd_fundamental_eq_fiedlerVecRaw
    (d : ℕ) (hd : 2 ≤ d) :
    phaseModeHd d ⟨0, by omega⟩ = fiedlerVecRaw d := by
  change WithLp.toLp 2 (fun j : Fin d =>
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) *
          ((((⟨0, by omega⟩ : Fin d).val : ℝ) + 1) * Real.pi /
            ((d : ℝ) + 1))) : ℂ)) =
    WithLp.toLp 2 (fun j : Fin d =>
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) *
          (Real.pi / ((d : ℝ) + 1))) : ℂ))
  congr 1
  funext j
  congr 3
  norm_num

theorem KdOp_fiedlerVecRaw
    (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (fiedlerVecRaw d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • fiedlerVecRaw d := by
  rw [← phaseModeHd_fundamental_eq_fiedlerVecRaw d hd,
    KdOp_phaseModeHd hd, eigenvalueK_fundamental d hd]

theorem KdOp_fiedlerVec
    (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (fiedlerVec d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • fiedlerVec d := by
  rw [fiedlerVec, map_smul, KdOp_fiedlerVecRaw d hd]
  module

theorem specRadius_KdOp_eq_step
    (d : ℕ) (hd : 2 ≤ d) :
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    letI : Nontrivial (Hd d) := inferInstance
    SpectralExtremal.specRadius (KdOp d) (KdOp_isSymmetric d) =
      2 / ((d : ℝ) - 1) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (Hd d) := inferInstance
  have hdsub : 0 < (d : ℝ) - 1 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hδ : 0 ≤ 2 / ((d : ℝ) - 1) := by
    exact div_nonneg (by norm_num) hdsub.le
  apply le_antisymm
  · have heig :=
      (KdOp_isSymmetric d).hasEigenvalue_eigenvalues rfl
        (SpectralExtremal.extremalIndex (KdOp d) (KdOp_isSymmetric d))
    have hb := abs_eigenvalue_KdOp_le hd heig
    simpa [SpectralExtremal.specRadius,
      SpectralExtremal.extremalEigenvalue,
      Complex.norm_real, Real.norm_eq_abs] using hb
  · have hb :=
      SpectralExtremal.norm_apply_le_specRadius_mul_norm
        (KdOp d) (KdOp_isSymmetric d) (fiedlerVec d)
    rw [KdOp_fiedlerVec d hd, norm_smul,
      norm_fiedlerVec d (by omega)] at hb
    have hb' :
        2 / ‖(((d : ℝ) : ℂ) - 1)‖ ≤
          SpectralExtremal.specRadius (KdOp d) (KdOp_isSymmetric d) := by
      simpa [Complex.norm_real, abs_of_nonneg hδ] using hb
    rw [show (((d : ℝ) : ℂ) - 1) = (((d : ℝ) - 1 : ℝ) : ℂ) by
      push_cast
      ring, Complex.norm_real, Real.norm_of_nonneg hdsub.le] at hb'
    exact hb'

end TransportPosition

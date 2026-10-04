/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D5_MaximalTension

/-!
# D49i — The commutators of `T_d` and `P_d` close only at `d = 2, 3`

Let `C = [T_d, P_d]`. The bracket with `P_d` always closes,

  `[P_d, C] = −h² T_d`,  `h = 2/(d − 1)`,

because neighbouring positions differ by `h`. The bracket with `T_d` is `D = [T_d, C]`, a
diagonal matrix: on an interior position the two neighbours cancel, at the two ends they do not. So
`D` lies in `span {T_d, P_d, C}` exactly when `D` is proportional to `P_d`, that is, when `P_d`
vanishes on every interior position: `d = 2` (`P = diag(−1, 1)`) or `d = 3` (`P = diag(−1, 0, 1)`).

At `d = 2, 3` the three operators `T_d`, `P_d`, `[T_d, P_d]` close like a spin, a Lie algebra of
dimension three, as `x`, `p`, `iħ` close in the continuum. From `d = 4` on the bracket of
transport with the commutator leaves the span: the commutators never close. This is the
rupture at `d = 4` of `D7` (Niven) and `D13` (the first interior edge), seen in the algebra.

## Main results

- `LieClosure.commutator_P_C` : `[P_d, [T_d, P_d]] = −h² T_d` for every `d`.
- `LieClosure.D_zero_zero` : `[T_d, [T_d, P_d]]` at the first position is `−2h/ρ_d² ≠ 0`.
- `LieClosure.D_one_one` : `[T_d, [T_d, P_d]]` vanishes on the first interior position.
- `LieClosure.closure_iff` : `[T_d, [T_d, P_d]] ∈ span {T_d, P_d, [T_d, P_d]}` iff `d ∈ {2, 3}`.
-/

@[expose] public noncomputable section

open Matrix

namespace TransportPosition

namespace LieClosure

variable {d : ℕ}

/-- The commutator `C = [T_d, P_d]`. -/
def C (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Td d * Pd d - Pd d * Td d

/-- The double commutator `D = [T_d, [T_d, P_d]]`. -/
def D (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Td d * C d - C d * Td d

theorem mul_Pd_apply (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * Pd d) i j = A i j * posCoord d j := by
  simp [mul_apply, Pd]

theorem Pd_mul_apply (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (Pd d * A) i j = posCoord d i * A i j := by
  simp [mul_apply, Pd]

theorem C_apply (i j : Fin d) :
    C d i j = Td d i j * ((posCoord d j : ℂ) - posCoord d i) := by
  simp only [C, Matrix.sub_apply, mul_Pd_apply, Pd_mul_apply]
  ring

theorem Td_apply (i j : Fin d) : Td d i j = if MinStep i j then 1 / (rho d : ℂ) else 0 := by
  by_cases h : MinStep i j <;> simp [Td, Ad, h]

theorem Td_self (i : Fin d) : Td d i i = 0 := by
  simp [Td_apply, MinStep]

theorem posCoord_sub (i j : Fin d) :
    posCoord d j - posCoord d i = 2 * ((j.val : ℝ) - i.val) / ((d : ℝ) - 1) := by
  simp only [posCoord]
  ring

/-- Neighbours differ in position by `±h`. -/
theorem posCoord_sub_sq_of_minStep {i j : Fin d} (h : MinStep i j) :
    (posCoord d j - posCoord d i) ^ 2 = (2 / ((d : ℝ) - 1)) ^ 2 := by
  rw [posCoord_sub]
  have : ((j.val : ℝ) - i.val) ^ 2 = 1 := by
    rcases h with h | h
    · rw [← h]; push_cast; ring
    · rw [← h]; push_cast; ring
  rw [div_pow, mul_pow, this, mul_one, div_pow]

/-- **`[P_d, [T_d, P_d]] = −h² T_d`**: the bracket with position always closes. -/
theorem commutator_P_C :
    Pd d * C d - C d * Pd d = -(((2 / ((d : ℝ) - 1)) ^ 2 : ℝ) : ℂ) • Td d := by
  ext i j
  simp only [Matrix.sub_apply, Pd_mul_apply, mul_Pd_apply, C_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : MinStep i j
  · have hs := posCoord_sub_sq_of_minStep h
    have hs' : ((posCoord d j : ℂ) - posCoord d i) ^ 2 = (((2 / ((d : ℝ) - 1)) ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast hs
    linear_combination (-(Td d i j)) * hs'
  · simp [Td_apply, h]

/-- The diagonal of `[T_d, [T_d, P_d]]`. -/
theorem D_diag (i : Fin d) :
    D d i i = ∑ k, 2 * Td d i k * Td d k i * ((posCoord d i : ℂ) - posCoord d k) := by
  simp only [D, Matrix.sub_apply, mul_apply, C_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- At the first position `[T_d, [T_d, P_d]]` is `−2h/ρ_d²`, not zero. -/
theorem D_zero_zero (hd : 2 ≤ d) :
    D d ⟨0, by omega⟩ ⟨0, by omega⟩ = -(2 * (2 / ((d : ℝ) - 1)) / rho d ^ 2 : ℝ) := by
  rw [D_diag, Finset.sum_eq_single (⟨1, by omega⟩ : Fin d)]
  · have h01 : MinStep (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ := Or.inl rfl
    have h10 : MinStep (⟨1, by omega⟩ : Fin d) ⟨0, by omega⟩ := Or.inr rfl
    have hp := posCoord_sub (d := d) ⟨1, by omega⟩ ⟨0, by omega⟩
    simp only [Nat.cast_zero, Nat.cast_one] at hp
    have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
    simp only [Td_apply, h01, h10, ↓reduceIte]
    have hp' : (posCoord d ⟨0, by omega⟩ : ℂ) - posCoord d ⟨1, by omega⟩ =
        ((2 * (0 - 1) / ((d : ℝ) - 1) : ℝ) : ℂ) := by exact_mod_cast hp
    rw [hp']
    push_cast
    field_simp
    ring
  · intro k _ hk
    have : ¬MinStep (⟨0, by omega⟩ : Fin d) k := by
      rintro (h | h)
      · exact hk (Fin.ext (by simp only at h ⊢; omega))
      · simp only at h; omega
    simp [Td_apply, this]
  · simp

/-- On the first interior position the two neighbours cancel: `[T_d, [T_d, P_d]]` vanishes there. -/
theorem D_one_one (hd : 3 ≤ d) : D d ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 := by
  rw [D_diag, Finset.sum_eq_add (⟨0, by omega⟩ : Fin d) (⟨2, by omega⟩ : Fin d)
    (by simp [Fin.ext_iff])]
  · have h10 : MinStep (⟨1, by omega⟩ : Fin d) ⟨0, by omega⟩ := Or.inr rfl
    have h01 : MinStep (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ := Or.inl rfl
    have h12 : MinStep (⟨1, by omega⟩ : Fin d) ⟨2, by omega⟩ := Or.inl rfl
    have h21 : MinStep (⟨2, by omega⟩ : Fin d) ⟨1, by omega⟩ := Or.inr rfl
    simp only [Td_apply, h10, h01, h12, h21, ↓reduceIte, posCoord]
    push_cast
    ring
  · intro k _ hk
    have : ¬MinStep (⟨1, by omega⟩ : Fin d) k := by
      rintro (h | h)
      · exact hk.2 (Fin.ext (by simp only at h ⊢; omega))
      · exact hk.1 (Fin.ext (by simp only at h ⊢; omega))
    simp [Td_apply, this]
  · simp
  · simp

/-- **The commutators close only at `d = 2, 3`.** `[T_d, [T_d, P_d]]` lies in the span of
`T_d`, `P_d` and `[T_d, P_d]` exactly when `d = 2` or `d = 3`. -/
theorem closure_iff (hd : 2 ≤ d) :
    (∃ a b c : ℂ, D d = a • Td d + b • Pd d + c • C d) ↔ d = 2 ∨ d = 3 := by
  constructor
  · rintro ⟨a, b, c, h⟩
    by_contra hne
    have h4 : 4 ≤ d := by omega
    have hdiag (i : Fin d) : D d i i = b * posCoord d i := by
      rw [h]
      simp [Td_self, C_apply, Pd]
    have h1 := hdiag ⟨1, by omega⟩
    rw [D_one_one (by omega)] at h1
    have hp1 : (posCoord d ⟨1, by omega⟩ : ℂ) ≠ 0 := by
      have hd1 : (d : ℝ) - 1 ≠ 0 := by
        have : (4 : ℝ) ≤ d := by exact_mod_cast h4
        linarith
      have : posCoord d ⟨1, by omega⟩ ≠ 0 := by
        simp only [posCoord, Nat.cast_one]
        rw [div_ne_zero_iff]
        refine ⟨?_, hd1⟩
        have : (4 : ℝ) ≤ d := by exact_mod_cast h4
        intro h0
        linarith
      exact_mod_cast this
    have hb : b = 0 := by
      rcases mul_eq_zero.mp h1.symm with hb | hp
      · exact hb
      · exact absurd hp hp1
    have h0 := hdiag ⟨0, by omega⟩
    rw [hb, zero_mul, D_zero_zero hd] at h0
    have hρ := rho_pos d hd
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have : (2 * (2 / ((d : ℝ) - 1)) / rho d ^ 2 : ℝ) ≠ 0 := by positivity
    exact this (by exact_mod_cast neg_eq_zero.mp h0)
  · rintro (rfl | rfl)
    · refine ⟨0, (2 * (2 / ((2 : ℝ) - 1)) / rho 2 ^ 2 : ℝ), 0, ?_⟩
      have hρ : (rho 2 : ℂ) ≠ 0 := by exact_mod_cast (rho_pos 2 le_rfl).ne'
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [D, C, mul_apply, Fin.sum_univ_succ, Td, Ad, Pd, posCoord, MinStep] <;>
        field_simp <;> ring
    · refine ⟨0, (2 * (2 / ((3 : ℝ) - 1)) / rho 3 ^ 2 : ℝ), 0, ?_⟩
      have hρ : (rho 3 : ℂ) ≠ 0 := by exact_mod_cast (rho_pos 3 (by norm_num)).ne'
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [D, C, mul_apply, Fin.sum_univ_succ, Td, Ad, Pd, posCoord, MinStep] <;>
        field_simp <;> ring

end LieClosure

end TransportPosition

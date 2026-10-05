/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49q_TransportRelation

/-!
# D49r — `[T_d, [T_d, P_d]]` lives on the two ends

`D = [T_d, [T_d, P_d]]` is diagonal (`D_offdiag`), vanishes at every interior position
(`D_interior`), and is `∓2h/ρ_d²` at the first and last positions (`D49i`, `D_last`):

  `D = (2h/ρ_d²) · diag(−1, 0, …, 0, +1)`.

On an interior position the two neighbours pull in opposite directions and cancel; at an end
only one neighbour is left. Two positions at distance two meet at their midpoint with opposite
offsets, so `D` has no entries off the diagonal.

## Main results

- `EdgeOperator.D_offdiag` : `D i j = 0` for `i ≠ j`.
- `EdgeOperator.D_interior` : `D i i = 0` for `0 < i < d − 1`.
- `EdgeOperator.D_last` : `D (d − 1) (d − 1) = 2h/ρ_d²`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition LieClosure

namespace EdgeOperator

variable {d : ℕ}

theorem minStep_val {i k : Fin d} : MinStep i k ↔ i.val + 1 = k.val ∨ k.val + 1 = i.val :=
  Iff.rfl

/-- **`D` is diagonal.** -/
theorem D_offdiag {i j : Fin d} (hij : i ≠ j) : D d i j = 0 := by
  simp only [D, Matrix.sub_apply, mul_apply, C_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : MinStep i k
  · by_cases hkj : MinStep k j
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hN : i.val + j.val = 2 * k.val := by
        rcases hik with h1 | h1 <;> rcases hkj with h2 | h2 <;> omega
      have hmid : (i.val : ℝ) + j.val = 2 * k.val := by exact_mod_cast hN
      have hx : (posCoord d j : ℂ) - posCoord d k - ((posCoord d k : ℂ) - posCoord d i) = 0 := by
        have h1 := posCoord_sub (d := d) k j
        have h2 := posCoord_sub (d := d) i k
        have : (posCoord d j - posCoord d k) - (posCoord d k - posCoord d i) = 0 := by
          have hz : 2 * ((j.val : ℝ) - k.val) - 2 * ((k.val : ℝ) - i.val) = 0 := by linarith
          rw [h1, h2, div_sub_div_same, hz, zero_div]
        exact_mod_cast this
      linear_combination (Td d i k * Td d k j) * hx
    · simp [Td_apply, hkj]
  · simp [Td_apply, hik]

/-- **`D` vanishes at every interior position.** -/
theorem D_interior {i : Fin d} (h0 : 0 < i.val) (h1 : i.val + 1 < d) : D d i i = 0 := by
  rw [D_diag, Finset.sum_eq_add (⟨i.val - 1, by omega⟩ : Fin d) (⟨i.val + 1, h1⟩ : Fin d)
    (by simp only [ne_eq, Fin.ext_iff]; omega)]
  · have a1 : MinStep i ⟨i.val - 1, by omega⟩ := Or.inr (by simp; omega)
    have a2 : MinStep (⟨i.val - 1, by omega⟩ : Fin d) i := Or.inl (by simp; omega)
    have a3 : MinStep i ⟨i.val + 1, h1⟩ := Or.inl rfl
    have a4 : MinStep (⟨i.val + 1, h1⟩ : Fin d) i := Or.inr rfl
    simp only [Td_apply, a1, a2, a3, a4, ↓reduceIte, posCoord]
    have : ((i.val - 1 : ℕ) : ℝ) = i.val - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    push_cast [this]
    ring
  · intro k _ hk
    have : ¬MinStep i k := by
      rintro (h | h)
      · exact hk.2 (Fin.ext (by simp; omega))
      · exact hk.1 (Fin.ext (by simp; omega))
    simp [Td_apply, this]
  · simp
  · simp

/-- **At the last position `D` is `+2h/ρ_d²`.** -/
theorem D_last (hd : 2 ≤ d) :
    D d ⟨d - 1, by omega⟩ ⟨d - 1, by omega⟩ = (2 * (2 / ((d : ℝ) - 1)) / rho d ^ 2 : ℝ) := by
  rw [D_diag, Finset.sum_eq_single (⟨d - 2, by omega⟩ : Fin d)]
  · have a1 : MinStep (⟨d - 1, by omega⟩ : Fin d) ⟨d - 2, by omega⟩ := Or.inr (by simp; omega)
    have a2 : MinStep (⟨d - 2, by omega⟩ : Fin d) ⟨d - 1, by omega⟩ := Or.inl (by simp; omega)
    have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
    simp only [Td_apply, a1, a2, ↓reduceIte, posCoord]
    have e1 : ((d - 1 : ℕ) : ℝ) = d - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have e2 : ((d - 2 : ℕ) : ℝ) = d - 2 := by rw [Nat.cast_sub (by omega)]; simp
    push_cast [e1, e2]
    have hd1 : ((d : ℂ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      exact_mod_cast (show (d : ℝ) - 1 ≠ 0 by linarith)
    field_simp
    ring
  · intro k _ hk
    have : ¬MinStep (⟨d - 1, by omega⟩ : Fin d) k := by
      rintro (h | h)
      · simp at h; omega
      · exact hk (Fin.ext (by simp at h ⊢; omega))
    simp [Td_apply, this]
  · simp

end EdgeOperator

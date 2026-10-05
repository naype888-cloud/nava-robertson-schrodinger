/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D49i_TransportPositionLieClosure

/-!
# D49m — The mirror state: equality in det|NRS³ with nothing moving

The mirror `J` sends position `j` to `d − 1 − j` with sign `(−1)^j`. It anticommutes with
transport and with position, `J T_d = −T_d J` and `J P_d = −P_d J`, and it is unitary.

Read as a state of two axes, `Φ(j, k) = J_{jk}/√d` places `x` at position `j` and `y` at the
mirror position `d − 1 − j`. Since `T_d`, `P_d` are real symmetric, `(A ⊗ 1 + 1 ⊗ A) vec J =
vec (A J + J A)`, so the anticommutation says `(T_x + T_y) Φ = 0` and `(P_x + P_y) Φ = 0`: total
transport and total position of the pair are fixed, while each axis alone is completely
undetermined (its reduced state is `J Jᴴ / d = 1/d`). Its tension is `tr [T_d, P_d] / d = 0`.

So the mirror state gives equality in Robertson 1934, but as `0 = 0`: the six fluctuation
vectors are dependent and every tension vanishes. It moves at speed `0`, as far from the band
`Ϙ(d)` near the cone as a state can be. It is the trivial case of the open step of `D49h`, kept
here so that it is on record; what matters lies on the other side, in the band.

## Main results

- `MirrorState.J_mul_Td` : `J T_d = −T_d J`.
- `MirrorState.J_mul_Pd` : `J P_d = −P_d J`.
- `MirrorState.J_mul_conjTranspose` : `J Jᴴ = 1`.
- `MirrorState.trace_mirror_commutator` : `tr (Jᴴ [T_d, P_d] J) = 0`, the tension of an axis.
-/

@[expose] public noncomputable section

open Matrix TransportPosition

namespace MirrorState


variable {d : ℕ}

/-- The mirror `J`: position `j` goes to `d − 1 − j`, with sign `(−1)^j`. -/
def J (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val + j.val + 1 = d then (-1) ^ i.val else 0

/-- Mirror positions have opposite coordinates. -/
theorem posCoord_mirror (i j : Fin d) (h : i.val + j.val + 1 = d) :
    posCoord d j = -posCoord d i := by
  unfold posCoord
  have : (j.val : ℝ) = d - 1 - i.val := by
    have : (i.val : ℝ) + j.val + 1 = d := by exact_mod_cast h
    linarith
  rw [this]; ring

/-- `J` anticommutes with position. -/
theorem J_mul_Pd : J d * Pd d = -(Pd d * J d) := by
  ext i k
  rw [Matrix.neg_apply, mul_apply, mul_apply, Finset.sum_eq_single k, Finset.sum_eq_single i]
  · by_cases h : i.val + k.val + 1 = d
    · simp [J, Pd, h, posCoord_mirror i k h]; ring
    · simp [J, Pd, h]
  · intro b _ hb; simp [Pd, Ne.symm hb]
  · simp
  · intro b _ hb; simp [Pd, hb]
  · simp

/-- The mirror of a position. -/
def mir (i : Fin d) : Fin d := ⟨d - 1 - i.val, by omega⟩

/-- Neighbouring exponents give opposite signs. -/
theorem neg_one_pow_of_adj {a b : ℕ} (h : a + 1 = b ∨ b + 1 = a) :
    (-1 : ℂ) ^ a = -(-1) ^ b := by
  rcases h with h | h <;> subst h <;> rw [pow_succ] <;> ring

/-- `J` anticommutes with transport. -/
theorem J_mul_Td : J d * Td d = -(Td d * J d) := by
  ext i k
  have hiL := i.isLt
  have hkL := k.isLt
  rw [Matrix.neg_apply, mul_apply, mul_apply, Finset.sum_eq_single (mir i),
    Finset.sum_eq_single (mir k)]
  · have hi : i.val + (d - 1 - i.val) + 1 = d := by omega
    have hk : d - 1 - k.val + k.val + 1 = d := by omega
    have hiff : MinStep (mir i) k ↔ MinStep i (mir k) := by
      simp only [MinStep, mir]; omega
    by_cases h1 : MinStep (mir i) k
    · have h2 := hiff.mp h1
      have hs : (-1 : ℂ) ^ i.val = -(-1) ^ (d - 1 - k.val) :=
        neg_one_pow_of_adj (by simp only [MinStep, mir] at h1; omega)
      simp only [Td, Ad, h1, h2, ite_true]
      simp only [J, mir, hi, hk, ite_true, hs]
      ring
    · have h2 : ¬ MinStep i (mir k) := fun h => h1 (hiff.mpr h)
      simp [Td, Ad, h1, h2]
  · intro b _ hb
    have : ¬ (b.val + k.val + 1 = d) := fun h => hb (Fin.ext (by simp [mir]; omega))
    simp [J, this]
  · simp
  · intro b _ hb
    have : ¬ (i.val + b.val + 1 = d) := fun h => hb (Fin.ext (by simp [mir]; omega))
    simp [J, this]
  · simp

/-- `J` is unitary: `J Jᴴ = 1`. -/
theorem J_mul_conjTranspose : J d * (J d)ᴴ = 1 := by
  ext i k
  have hiL := i.isLt
  rw [mul_apply, Finset.sum_eq_single (mir i)]
  · by_cases hik : i = k
    · subst hik
      have hi : i.val + (d - 1 - i.val) + 1 = d := by omega
      simp [J, mir, hi, ← mul_pow]
    · have : ¬ (k.val + (d - 1 - i.val) + 1 = d) := fun h => hik (Fin.ext (by omega))
      simp [J, mir, this, hik]
  · intro b _ hb
    have : ¬ (i.val + b.val + 1 = d) := fun h => hb (Fin.ext (by simp [mir]; omega))
    simp [J, this]
  · simp

/-- **The mirror state carries no tension.** For `Φ = vec J` on two axes, the tension of one axis
is `tr (Jᴴ [T_d, P_d] J) / d = tr [T_d, P_d] / d = 0`. -/
theorem trace_mirror_commutator :
    (Matrix.trace ((J d)ᴴ * (Td d * Pd d - Pd d * Td d) * J d)) = 0 := by
  rw [Matrix.trace_mul_cycle, J_mul_conjTranspose, one_mul, Matrix.trace_sub,
    Matrix.trace_mul_comm, sub_self]

end MirrorState

end

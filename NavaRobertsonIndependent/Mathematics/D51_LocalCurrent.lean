/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module
public import NavaRobertsonIndependent.Mathematics.D5_MaximalTension
/-!
# D51 — The local currents of `T_d`, and the tension as their sum

`T_d` moves one step along the axis (`D3`), and `P_d` is the diagonal position. The current through
the link between the positions `m` and `n` is
`K_{mn} = i (T_{mn} |m⟩⟨n| - T_{nm} |n⟩⟨m|)`, Hermitian and antisymmetric in `(m, n)`.

The evolution of the occupation of the position `n` is the sum of the currents that leave it
(`continuity`): `i [T, |n⟩⟨n|] = ∑_m K_{mn}`. Reading position as a weight, the tension
`i [T_d, P_d]` of `D5` is the sum of the local currents weighted by the position they leave
(`tension_eq_sum_bondCurrent`), and, by the antisymmetry, by the displacement of each link
(`tension_eq_half_sum_displacement`). The advection is the transport.

## Main results

- `bondCurrent_antisymm`, `bondCurrent_isHermitian` : the local current.
- `continuity` : `i [T, |n⟩⟨n|] = ∑_m K_{mn}` for every matrix `T`.
- `tension_eq_sum_bondCurrent` : `i [T_d, P_d] = ∑_n P_n ∑_m K_{mn}`.
- `tension_eq_half_sum_displacement` : `2 i [T_d, P_d] = ∑ (P_n - P_m) K_{mn}`.
-/
@[expose] public noncomputable section
open Matrix
namespace TransportPosition

variable {d : ℕ}

/-- The current through the link between the positions `m` and `n`. -/
def bondCurrent (T : Matrix (Fin d) (Fin d) ℂ) (m n : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Complex.I • (T m n • Matrix.single m n (1 : ℂ) - T n m • Matrix.single n m (1 : ℂ))

lemma bondCurrent_antisymm (T : Matrix (Fin d) (Fin d) ℂ) (m n : Fin d) :
    bondCurrent T n m = - bondCurrent T m n := by
  unfold bondCurrent
  rw [← smul_neg, neg_sub]

lemma bondCurrent_isHermitian {T : Matrix (Fin d) (Fin d) ℂ} (hT : T.IsHermitian) (m n : Fin d) :
    (bondCurrent T m n).IsHermitian := by
  have h1 : star (T n m) = T m n := by
    simpa using congrFun (congrFun hT.eq m) n
  have h2 : star (T m n) = T n m := by
    simpa using congrFun (congrFun hT.eq n) m
  unfold Matrix.IsHermitian bondCurrent
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
    star_one, h1, h2, Complex.star_def, Complex.conj_I]
  rw [neg_smul, ← smul_neg, neg_sub]

/-- **Continuity**: the evolution of the occupation of the position `n` is the sum of the currents
that leave it, `i [T, |n⟩⟨n|] = ∑_m K_{mn}`. -/
theorem continuity (T : Matrix (Fin d) (Fin d) ℂ) (n : Fin d) :
    Complex.I • (T * Matrix.single n n (1 : ℂ) - Matrix.single n n (1 : ℂ) * T) =
      ∑ m, bondCurrent T m n := by
  ext i j
  simp only [bondCurrent, Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.single_apply, smul_eq_mul]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  by_cases hnj : n = j <;> by_cases hni : n = i <;>
    simp [hnj, hni, ite_and, Finset.sum_ite_eq, eq_comm]

/-- The position `P_d` is the sum of the occupations weighted by the coordinate. -/
lemma Pd_eq_sum (d : ℕ) :
    Pd d = ∑ n : Fin d, (posCoord d n : ℂ) • Matrix.single n n (1 : ℂ) := by
  ext i j
  simp only [Pd, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, ite_and, Finset.sum_ite_eq, eq_comm]

/-- **The tension is the sum of the local currents weighted by position**:
`i [T_d, P_d] = ∑_n P_n ∑_m K_{mn}`. -/
theorem tension_eq_sum_bondCurrent (d : ℕ) :
    Complex.I • (Td d * Pd d - Pd d * Td d) =
      ∑ n : Fin d, (posCoord d n : ℂ) • ∑ m : Fin d, bondCurrent (Td d) m n := by
  rw [Pd_eq_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← continuity, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_comm]

/-- **The tension, link by link**: `2 i [T_d, P_d] = ∑ (P_n - P_m) K_{mn}`: each link contributes
its current times the displacement it covers. -/
theorem tension_eq_half_sum_displacement (d : ℕ) :
    (2 : ℂ) • (Complex.I • (Td d * Pd d - Pd d * Td d)) =
      ∑ n : Fin d, ∑ m : Fin d,
        ((posCoord d n : ℂ) - posCoord d m) • bondCurrent (Td d) m n := by
  have h1 := tension_eq_sum_bondCurrent d
  have h2 : ∑ n : Fin d, (posCoord d n : ℂ) • ∑ m : Fin d, bondCurrent (Td d) m n =
      - ∑ n : Fin d, ∑ m : Fin d, (posCoord d m : ℂ) • bondCurrent (Td d) m n := by
    rw [Finset.sum_comm (f := fun n m => (posCoord d m : ℂ) • bondCurrent (Td d) m n)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [bondCurrent_antisymm, smul_neg]
  have h3 : ∑ n : Fin d, ∑ m : Fin d,
        ((posCoord d n : ℂ) - posCoord d m) • bondCurrent (Td d) m n =
      ∑ n : Fin d, (posCoord d n : ℂ) • ∑ m : Fin d, bondCurrent (Td d) m n -
        ∑ n : Fin d, ∑ m : Fin d, (posCoord d m : ℂ) • bondCurrent (Td d) m n := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sub_smul]
  rw [two_smul, h1, h3, h2]
  abel

end TransportPosition

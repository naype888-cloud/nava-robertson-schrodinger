/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50h_CanonicalSentence

/-!
# D50i — The ratio `det Σ / |det Ω|` of a diagonal: one factor per step

A diagonal is a set `S` of axes: a face diagonal has two, a body diagonal three. Take the
`2|S|` operators `(T_i, P_i)`, `i ∈ S`. On canonical axes (`D49k`) both `Σ` and `Ω` are block
diagonal, one `2 × 2` block per axis of `S`, so

  `det Σ / |det Ω| = Π_{i ∈ S} (1 + g_i / ω_i²)`,

with `g_i = τ_i²` the time of the axis (`D50c`). The diagonal of two steps has two factors, the
diagonal of three steps has three; the full cube is the body diagonal (`D49k`).

## Main results

- `DiagonalRatio.det_ratio_diagonal` : the product over any set `S` of axes.
- `DiagonalRatio.det_ratio_face` : two steps, two factors.
- `DiagonalRatio.det_ratio_body` : three steps, three factors.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS CauchyGram RobertsonDeterminant RobertsonDeterminant3D
  AxisDefectEntangled DeterminantEqualityRelation CanonicalAxes

namespace DiagonalRatio

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- The pairs `(T_i, P_i)` of the axes of a diagonal `S`. -/
def famDiag (dx dy dz : ℕ) (S : Finset (Fin 3)) : Fin 2 × S → H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  fun p => pairs dx dy dz (p.1, p.2.1)

variable (horth : ∀ s t (i j : Fin 3), i ≠ j → inner ℂ (fluct Φ (s, i)) (fluct Φ (t, j)) = 0)
include horth

theorem covMatrix_diag (S : Finset (Fin 3)) :
    covMatrix (famDiag dx dy dz S) Φ =
      blockDiagonal fun i : S => covMatrix (famAxis dx dy dz i.1) Φ := by
  ext ⟨s, i⟩ ⟨t, j⟩
  rw [blockDiagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · have h0 := horth s t i.1 j.1 (fun e => h (Subtype.ext e))
    simp only [fluct] at h0
    simp [covMatrix, covarianceG, famDiag, h0]

theorem imMatrix_diag (S : Finset (Fin 3)) :
    imMatrix (famDiag dx dy dz S) Φ =
      blockDiagonal fun i : S => !![0, omega Φ i.1; -omega Φ i.1, 0] := by
  ext ⟨s, i⟩ ⟨t, j⟩
  rw [blockDiagonal_apply]
  split_ifs with h
  · subst h
    fin_cases s <;> fin_cases t
    · simp [imMatrix, famDiag, ← Complex.ofReal_pow]
    · rfl
    · simpa [imMatrix, famDiag, omega] using inner_im_swap _ _
    · simp [imMatrix, famDiag, ← Complex.ofReal_pow]
  · have h0 := horth s t i.1 j.1 (fun e => h (Subtype.ext e))
    simp only [fluct] at h0
    simp [imMatrix, famDiag, h0]

/-- **The ratio of a diagonal: one factor `1 + g_i/ω_i²` per step.** -/
theorem det_ratio_diagonal (S : Finset (Fin 3)) (hω : ∀ i ∈ S, omega Φ i ≠ 0) :
    (covMatrix (famDiag dx dy dz S) Φ).det / |(imMatrix (famDiag dx dy dz S) Φ).det| =
      ∏ i ∈ S, (1 + defect Φ i / omega Φ i ^ 2) := by
  rw [covMatrix_diag horth, imMatrix_diag horth, det_blockDiagonal, det_blockDiagonal]
  simp only [det_block, det_fin_two_of]
  have e : ∀ i : S, (0 * 0 - omega Φ i.1 * -omega Φ i.1) = omega Φ i.1 ^ 2 := fun i => by ring
  simp only [e]
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => sq_nonneg _), ← Finset.prod_div_distrib,
    ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := hω i.1 i.2
  field_simp
  ring

/-- **A face diagonal, two steps: two factors.** -/
theorem det_ratio_face (i j : Fin 3) (hij : i ≠ j) (hi : omega Φ i ≠ 0) (hj : omega Φ j ≠ 0) :
    (covMatrix (famDiag dx dy dz {i, j}) Φ).det /
        |(imMatrix (famDiag dx dy dz {i, j}) Φ).det| =
      (1 + defect Φ i / omega Φ i ^ 2) * (1 + defect Φ j / omega Φ j ^ 2) := by
  have hS : ∀ k ∈ ({i, j} : Finset (Fin 3)), omega Φ k ≠ 0 := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · rw [Finset.mem_singleton.mp hk]; exact hj
  rw [det_ratio_diagonal horth {i, j} hS, Finset.prod_pair hij]

/-- **A body diagonal, three steps: three factors.** -/
theorem det_ratio_body (h0 : omega Φ 0 ≠ 0) (h1 : omega Φ 1 ≠ 0) (h2 : omega Φ 2 ≠ 0) :
    (covMatrix (famDiag dx dy dz Finset.univ) Φ).det /
        |(imMatrix (famDiag dx dy dz Finset.univ) Φ).det| =
      (1 + defect Φ 0 / omega Φ 0 ^ 2) * (1 + defect Φ 1 / omega Φ 1 ^ 2) *
        (1 + defect Φ 2 / omega Φ 2 ^ 2) := by
  rw [det_ratio_diagonal horth Finset.univ (by intro k _; fin_cases k <;> assumption),
    Fin.prod_univ_three]

end DiagonalRatio

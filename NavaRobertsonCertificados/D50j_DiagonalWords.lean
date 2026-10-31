/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50i_DiagonalRatio

/-!
# D50j — The ratio of a diagonal is the ratio of each of its `k!` words

A diagonal of `k` steps is reached by `k!` words, its `k` axes in every order (Physlib #1987:
`2` words for a face diagonal, `3! = 6` for a body diagonal), because steps on different axes
commute. Here the same fact for the ratio `det Σ / |det Ω|` of `D50i`: reading the word letter by
letter, one factor `1 + g_i/ω_i²` per step, gives the ratio of the diagonal, whatever the order.
So the `k!` words of a diagonal are one and the same ratio.

## Main results

- `DiagonalWords.det_ratio_word` : the ratio of the diagonal `w.toFinset` is the product, letter by
  letter, along the word `w`.
- `DiagonalWords.wordRatio_perm` : every order of the word gives the same ratio.
- `DiagonalWords.sum_permutations` : summed over the `k!` words of a diagonal, the ratio is
  `k! · det Σ / |det Ω|`.
- `DiagonalWords.face_two_words`, `DiagonalWords.body_six_words` : `2` and `3! = 6` words.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS CauchyGram RobertsonDeterminant RobertsonDeterminant3D
  AxisDefectEntangled DeterminantEqualityRelation CanonicalAxes DiagonalRatio

namespace DiagonalWords

variable {dx dy dz : ℕ}

/-- The factor of one step: `1 + g_i/ω_i²`. -/
def factor (Φ : H3D dx dy dz) (i : Fin 3) : ℝ := 1 + defect Φ i / omega Φ i ^ 2

/-- The ratio of a word, read letter by letter. -/
def wordRatio (Φ : H3D dx dy dz) (w : List (Fin 3)) : ℝ := (w.map (factor Φ)).prod

theorem wordRatio_perm (Φ : H3D dx dy dz) {w v : List (Fin 3)} (h : w.Perm v) :
    wordRatio Φ w = wordRatio Φ v := (h.map (factor Φ)).prod_eq

variable {Φ : H3D dx dy dz}
  (horth : ∀ s t (i j : Fin 3), i ≠ j → inner ℂ (fluct Φ (s, i)) (fluct Φ (t, j)) = 0)
include horth

/-- **The ratio of a diagonal is the product along any of its words.** -/
theorem det_ratio_word {w : List (Fin 3)} (hw : w.Nodup) (hω : ∀ i ∈ w, omega Φ i ≠ 0) :
    (covMatrix (famDiag dx dy dz w.toFinset) Φ).det /
        |(imMatrix (famDiag dx dy dz w.toFinset) Φ).det| = wordRatio Φ w := by
  rw [det_ratio_diagonal horth w.toFinset (fun i hi => hω i (List.mem_toFinset.mp hi)),
    wordRatio, List.prod_toFinset _ hw]
  rfl

/-- **Every word of the same diagonal has the same ratio**, which is that of the diagonal. -/
theorem det_ratio_of_perm {w v : List (Fin 3)} (hw : w.Nodup) (h : w.Perm v)
    (hω : ∀ i ∈ w, omega Φ i ≠ 0) :
    (covMatrix (famDiag dx dy dz w.toFinset) Φ).det /
        |(imMatrix (famDiag dx dy dz w.toFinset) Φ).det| = wordRatio Φ v := by
  rw [det_ratio_word horth hw hω, wordRatio_perm Φ h]

/-- **Summed over the `k!` words of a diagonal, the ratio is `k!` times that of the diagonal.** -/
theorem sum_permutations {w : List (Fin 3)} (hw : w.Nodup) (hω : ∀ i ∈ w, omega Φ i ≠ 0) :
    (w.permutations.map (wordRatio Φ)).sum =
      (w.length).factorial *
        ((covMatrix (famDiag dx dy dz w.toFinset) Φ).det /
          |(imMatrix (famDiag dx dy dz w.toFinset) Φ).det|) := by
  rw [det_ratio_word horth hw hω, List.sum_eq_length_nsmul _ (wordRatio Φ w), List.length_map,
    List.length_permutations, nsmul_eq_mul]
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  exact wordRatio_perm Φ ((List.mem_permutations.mp hv))

omit horth in
/-- **A face diagonal: two words, one ratio.** -/
theorem face_two_words (i j : Fin 3) :
    wordRatio Φ [i, j] = wordRatio Φ [j, i] := wordRatio_perm Φ (List.Perm.swap j i [])

omit horth in
/-- **A body diagonal: `3! = 6` words.** -/
theorem body_six_words : ([0, 1, 2] : List (Fin 3)).permutations.length = 6 := by
  rw [List.length_permutations]; rfl

end DiagonalWords

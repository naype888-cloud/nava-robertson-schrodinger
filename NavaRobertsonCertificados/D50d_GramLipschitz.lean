/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D50c_ProperTimeAxis

/-!
# D50d — The Gram defect is Lipschitz on any finite position set

The statements of `D23d` (`§2`–`§3`) on `ℂ^ι` instead of `ℂ^d`: the proofs are the same, with
`meanG`, `centeredG` of `D37` in place of `mean`, `centered`.

## Main results

- `GramLipschitz.gram_lipschitz` : `|gap(Ψ) − gap(Ψ')| ≤ 32 ‖Ψ − Ψ'‖` for contractions `A`, `B`.
-/

@[expose] public noncomputable section

open PathGraph3DNRS CauchyGram BandWidth

namespace GramLipschitz

variable {ι : Type*} [Fintype ι]
  {A B : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}

theorem abs_meanG_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    |meanG A ψ| ≤ 1 := by
  unfold meanG
  calc |(inner ℂ ψ (A ψ)).re| ≤ ‖inner ℂ ψ (A ψ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ψ‖ * ‖A ψ‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by rw [hψ, one_mul, ← hψ]; exact hc ψ

theorem abs_meanG_sub_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ ψ' : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1)
    (hψ' : ‖ψ'‖ = 1) : |meanG A ψ - meanG A ψ'| ≤ 2 * ‖ψ - ψ'‖ := by
  have e : inner ℂ ψ (A ψ) - inner ℂ ψ' (A ψ') =
      inner ℂ (ψ - ψ') (A ψ) + inner ℂ ψ' (A (ψ - ψ')) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  unfold meanG
  rw [← Complex.sub_re, e]
  calc |(inner ℂ (ψ - ψ') (A ψ) + inner ℂ ψ' (A (ψ - ψ'))).re|
      ≤ ‖inner ℂ (ψ - ψ') (A ψ) + inner ℂ ψ' (A (ψ - ψ'))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (ψ - ψ') (A ψ)‖ + ‖inner ℂ ψ' (A (ψ - ψ'))‖ := norm_add_le _ _
    _ ≤ ‖ψ - ψ'‖ * ‖A ψ‖ + ‖ψ'‖ * ‖A (ψ - ψ')‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖ψ - ψ'‖ * 1 + 1 * ‖ψ - ψ'‖ := by
        rw [hψ']
        gcongr
        · exact (hc ψ).trans hψ.le
        · exact hc _
    _ = 2 * ‖ψ - ψ'‖ := by ring

theorem norm_centeredG_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) : ‖centeredG A ψ‖ ≤ 1 := by
  have hre : (inner ℂ (A ψ) ψ).re = meanG A ψ := by
    rw [← inner_conj_symm, Complex.conj_re]
    rfl
  have hsq : ‖centeredG A ψ‖ ^ 2 = ‖A ψ‖ ^ 2 - meanG A ψ ^ 2 := by
    unfold centeredG
    rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul, hψ, Complex.norm_real, Real.norm_eq_abs,
      mul_one, sq_abs, RCLike.re_to_complex, Complex.re_ofReal_mul, hre]
    ring
  have h1 : ‖A ψ‖ ≤ 1 := (hc ψ).trans hψ.le
  have h2 : ‖centeredG A ψ‖ ^ 2 ≤ 1 := by
    rw [hsq]
    nlinarith [norm_nonneg (A ψ), sq_nonneg (meanG A ψ)]
  nlinarith [norm_nonneg (centeredG A ψ)]

theorem norm_centeredG_sub_le (hc : ∀ x, ‖A x‖ ≤ ‖x‖) {ψ ψ' : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) (hψ' : ‖ψ'‖ = 1) : ‖centeredG A ψ - centeredG A ψ'‖ ≤ 4 * ‖ψ - ψ'‖ := by
  have e : centeredG A ψ - centeredG A ψ' =
      A (ψ - ψ') - (((meanG A ψ - meanG A ψ' : ℝ) : ℂ) • ψ + (meanG A ψ' : ℂ) • (ψ - ψ')) := by
    unfold centeredG
    rw [map_sub]
    push_cast
    rw [sub_smul, smul_sub]
    abel
  have hm := abs_meanG_sub_le hc hψ hψ'
  have hm' := abs_meanG_le hc hψ'
  rw [e]
  calc ‖A (ψ - ψ') - (((meanG A ψ - meanG A ψ' : ℝ) : ℂ) • ψ + (meanG A ψ' : ℂ) • (ψ - ψ'))‖
      ≤ ‖A (ψ - ψ')‖ + (‖((meanG A ψ - meanG A ψ' : ℝ) : ℂ) • ψ‖ +
          ‖(meanG A ψ' : ℂ) • (ψ - ψ')‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ = ‖A (ψ - ψ')‖ + (|meanG A ψ - meanG A ψ'| + |meanG A ψ'| * ‖ψ - ψ'‖) := by
        rw [norm_smul, norm_smul, hψ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_one]
    _ ≤ ‖ψ - ψ'‖ + (2 * ‖ψ - ψ'‖ + 1 * ‖ψ - ψ'‖) := by
        gcongr
        · exact hc _
    _ = 4 * ‖ψ - ψ'‖ := by ring

/-- **The Gram defect of the fluctuations is Lipschitz** (`D23d`, on `ℂ^ι`). -/
theorem gram_lipschitz (hA : ∀ x, ‖A x‖ ≤ ‖x‖) (hB : ∀ x, ‖B x‖ ≤ ‖x‖)
    {ψ ψ' : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (hψ' : ‖ψ'‖ = 1) :
    |gramDefectC (centeredG A ψ) (centeredG B ψ) -
        gramDefectC (centeredG A ψ') (centeredG B ψ')| ≤ 32 * ‖ψ - ψ'‖ := by
  set a := centeredG A ψ
  set a' := centeredG A ψ'
  set b := centeredG B ψ
  set b' := centeredG B ψ'
  have ha := norm_centeredG_le hA hψ
  have ha' := norm_centeredG_le hA hψ'
  have hb := norm_centeredG_le hB hψ
  have hb' := norm_centeredG_le hB hψ'
  have hda := norm_centeredG_sub_le hA hψ hψ'
  have hdb := norm_centeredG_sub_le hB hψ hψ'
  have hi : ‖inner ℂ a b‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg a, norm_nonneg b])
  have hi' : ‖inner ℂ a' b'‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg a', norm_nonneg b'])
  have hdi : |‖inner ℂ a b‖ - ‖inner ℂ a' b'‖| ≤ ‖a - a'‖ + ‖b - b'‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have e : inner ℂ a b - inner ℂ a' b' = inner ℂ (a - a') b + inner ℂ a' (b - b') := by
      rw [inner_sub_left, inner_sub_right]
      ring
    rw [e]
    calc ‖inner ℂ (a - a') b + inner ℂ a' (b - b')‖
        ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ ‖a - a'‖ * 1 + 1 * ‖b - b'‖ := by gcongr
      _ = ‖a - a'‖ + ‖b - b'‖ := by ring
  have key := gram_lipschitz_real (norm_nonneg a) ha (norm_nonneg a') ha' (norm_nonneg b) hb
    (norm_nonneg b') hb' (norm_nonneg _) hi (norm_nonneg _) hi' (abs_norm_sub_norm_le a a')
    (abs_norm_sub_norm_le b b') hdi
  have hs : ∀ x y : EuclideanSpace ℂ ι, gramDefectC x y =
      ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖inner ℂ x y‖ ^ 2 := fun x y => rfl
  rw [hs, hs]
  calc _ ≤ 4 * (‖a - a'‖ + ‖b - b'‖) := key
    _ ≤ 4 * (4 * ‖ψ - ψ'‖ + 4 * ‖ψ - ψ'‖) := by gcongr
    _ = 32 * ‖ψ - ψ'‖ := by ring

end GramLipschitz

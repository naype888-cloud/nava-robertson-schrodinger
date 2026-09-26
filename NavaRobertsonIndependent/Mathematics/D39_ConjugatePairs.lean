/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum

/-!
# D39 — Every conjugate pair realized on `T_d : P_d`

A pair realized on `T_d : P_d` is `A = a T_d + b`, `B = c P_d + e` with real `a, c ≠ 0`: the
units and origins of the pair (position–momentum, number–phase, charge–flux, …). The
fluctuation vectors of `(A, B)` are those of `(T_d, P_d)` scaled by `a` and `c`, so neither the
angle nor the Robertson–Schrödinger ratio `R = σ_A σ_B / |⟪Ãψ, B̃ψ⟫|` changes. A pair only sets
its floor `|a c| / (d − 1)`. The catalogue of named pairs is in `docs/PAIRS.md`.

## Main results

- `ConjugatePairs.angleG_affineOp`, `ConjugatePairs.ratioG_affineOp` : units do not change the
  angle or the ratio, at every unit state.
- `ConjugatePairs.ratio_pair` : at `ψ*`, `R = C_Nava(d)` for every pair.
- `ConjugatePairs.saturated_pair_iff` : every pair saturates iff `d = 2, 3`.
- `ConjugatePairs.angle_pair_lt_of_lt`, `ConjugatePairs.angle_pair_lt_limit` : the angle grows
  strictly with `d`, whatever the units, below `arccos (1 / C_∞)`.
- `ConjugatePairs.volQuantum_pairs_certificate` : three pairs on the cube, each in its own
  units, give `𝒱(dx, dy, dz)`: zero iff some axis has `2` or `3` sites, positive from
  `4 × 4 × 4`, below `δ_∞³`.
-/

@[expose] public noncomputable section

open Real TransportPosition NRSInequality SpectralExtremal Gnomon
open PathGraph3DNRS EigenvectorSaturation NRSAngle DimensionalQuantum VolumetricQuantum

namespace ConjugatePairs

/-! ## 1. Affine invariance on any finite site set -/

section General

variable {ι : Type*} [Fintype ι]

/-- The observable `a L + b`: `L` in units `a` with origin `b`. -/
def affineOp (a b : ℝ) (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  (a : ℂ) • L + (b : ℂ) • LinearMap.id

/-- The Robertson–Schrödinger ratio `‖x‖ ‖y‖ / |⟨x, y⟩|` of the fluctuation vectors
`x = (L − ⟨L⟩)Ψ`, `y = (M − ⟨M⟩)Ψ`: `1` exactly when the inequality saturates. -/
def ratioG (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  ‖centeredG L Ψ‖ * ‖centeredG M Ψ‖ / ‖inner ℂ (centeredG L Ψ) (centeredG M Ψ)‖

variable {Ψ : EuclideanSpace ℂ ι}

theorem meanG_affineOp (a b : ℝ) (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hΨ : ‖Ψ‖ = 1) : meanG (affineOp a b L) Ψ = a * meanG L Ψ + b := by
  have h1 : inner ℂ Ψ Ψ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
  simp only [meanG, affineOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_add_right, inner_smul_right, h1, mul_one, Complex.add_re, Complex.re_ofReal_mul,
    Complex.ofReal_re]

/-- The fluctuation vector of `a L + b` is `a` times that of `L`. -/
theorem centeredG_affineOp (a b : ℝ) (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hΨ : ‖Ψ‖ = 1) : centeredG (affineOp a b L) Ψ = (a : ℂ) • centeredG L Ψ := by
  rw [centeredG, centeredG, meanG_affineOp a b L hΨ]
  simp only [affineOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  push_cast
  module

/-- Units do not reach the angle between the fluctuation vectors. -/
theorem angleG_affineOp {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (b e : ℝ)
    (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (hΨ : ‖Ψ‖ = 1) :
    angleG (affineOp a b L) (affineOp c e M) Ψ = angleG L M Ψ := by
  have hac : ‖(a : ℂ)‖ * ‖(c : ℂ)‖ ≠ 0 := by simp [ha, hc]
  rw [angleG, angleG, centeredG_affineOp a b L hΨ, centeredG_affineOp c e M hΨ, inner_smul_left,
    inner_smul_right, norm_mul, norm_mul, Complex.norm_conj, norm_smul, norm_smul]
  congr 1
  rw [show ‖(a : ℂ)‖ * (‖(c : ℂ)‖ * ‖inner ℂ (centeredG L Ψ) (centeredG M Ψ)‖) /
      (‖(a : ℂ)‖ * ‖centeredG L Ψ‖ * (‖(c : ℂ)‖ * ‖centeredG M Ψ‖)) =
      (‖(a : ℂ)‖ * ‖(c : ℂ)‖) * ‖inner ℂ (centeredG L Ψ) (centeredG M Ψ)‖ /
      ((‖(a : ℂ)‖ * ‖(c : ℂ)‖) * (‖centeredG L Ψ‖ * ‖centeredG M Ψ‖)) by ring]
  exact mul_div_mul_left _ _ hac

/-- Units do not reach the Robertson–Schrödinger ratio. -/
theorem ratioG_affineOp {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (b e : ℝ)
    (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (hΨ : ‖Ψ‖ = 1) :
    ratioG (affineOp a b L) (affineOp c e M) Ψ = ratioG L M Ψ := by
  have hac : ‖(a : ℂ)‖ * ‖(c : ℂ)‖ ≠ 0 := by simp [ha, hc]
  rw [ratioG, ratioG, centeredG_affineOp a b L hΨ, centeredG_affineOp c e M hΨ, inner_smul_left,
    inner_smul_right, norm_mul, norm_mul, Complex.norm_conj, norm_smul, norm_smul]
  rw [show ‖(a : ℂ)‖ * ‖centeredG L Ψ‖ * (‖(c : ℂ)‖ * ‖centeredG M Ψ‖) /
      (‖(a : ℂ)‖ * (‖(c : ℂ)‖ * ‖inner ℂ (centeredG L Ψ) (centeredG M Ψ)‖)) =
      (‖(a : ℂ)‖ * ‖(c : ℂ)‖) * (‖centeredG L Ψ‖ * ‖centeredG M Ψ‖) /
      ((‖(a : ℂ)‖ * ‖(c : ℂ)‖) * ‖inner ℂ (centeredG L Ψ) (centeredG M Ψ)‖) by ring]
  exact mul_div_mul_left _ _ hac

end General

/-! ## 2. One pair on `T_d : P_d` -/

section Recta

variable {a b c e : ℝ} {d : ℕ}

theorem ratioG_TdPd (hd : 2 ≤ d) :
    ratioG (TdOp d) (PdOp d) (psiStar d) = CoherenceConstant d := by
  have h := cos_angleNRS hd
  rw [ratioG, ← one_div_div]
  exact (congrArg (1 / ·) h).trans (one_div_one_div _)

/-- **The ratio of every pair is `C_Nava(d)`** at the maximal-tension state. -/
theorem ratio_pair (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    ratioG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) = CoherenceConstant d := by
  rw [ratioG_affineOp ha hc b e _ _ (norm_psiStar hd), ratioG_TdPd hd]

theorem angle_pair (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    angleG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) = angleNRS d :=
  angleG_affineOp ha hc b e _ _ (norm_psiStar hd)

/-- **Every pair saturates exactly at `d = 2, 3`.** -/
theorem saturated_pair_iff (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    angleG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) = 0 ↔ d = 2 ∨ d = 3 := by
  rw [angle_pair ha hc hd]
  exact angleNRS_eq_zero_iff hd

theorem angle_pair_pos (ha : a ≠ 0) (hc : c ≠ 0) (hd : 4 ≤ d) :
    0 < angleG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) := by
  rw [angle_pair ha hc (by omega)]
  exact angleNRS_pos hd

/-- **The opening grows with `d`**, even if the two rows carry different units. -/
theorem angle_pair_lt_of_lt {a' b' c' e' : ℝ} {d' : ℕ} (ha : a ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hc' : c' ≠ 0) (hd : 4 ≤ d) (h : d < d') :
    angleG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) <
      angleG (affineOp a' b' (TdOp d')) (affineOp c' e' (PdOp d')) (psiStar d') := by
  rw [angle_pair ha hc (by omega), angle_pair ha' hc' (by omega)]
  exact angleNRS_strictMonoOn (show 4 ≤ d from hd) (show 4 ≤ d' by omega) h

theorem angle_pair_lt_limit (ha : a ≠ 0) (hc : c ≠ 0) (hd : 4 ≤ d) :
    angleG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) <
      arccos (1 / CoherenceConstantInf) := by
  rw [angle_pair ha hc (by omega)]
  exact angleNRS_lt_limit hd

/-- The excess of every pair over the floor is the dimensional quantum `δ(d)` of `D25`. -/
theorem dimQuantum_pair (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    ratioG (affineOp a b (TdOp d)) (affineOp c e (PdOp d)) (psiStar d) - 1 = dimQuantum d := by
  rw [ratio_pair ha hc hd, dimQuantum, geometricGap]

end Recta

/-! ## 3. Three pairs on the cube -/

section Cubo

variable {ια ιβ ιγ : Type*} [Fintype ιγ] [Fintype ια] [Fintype ιβ]
  [DecidableEq ιγ] [DecidableEq ια] [DecidableEq ιβ]

theorem ratioG_lift (eq : ιγ ≃ ια × ιβ) {φ : EuclideanSpace ℂ ιβ} (hφ : ‖φ‖ = 1)
    (A B : Matrix ια ια ℂ) (ψ : EuclideanSpace ℂ ια) :
    ratioG (Matrix.toEuclideanLin (liftAlong eq A)) (Matrix.toEuclideanLin (liftAlong eq B))
        (prodAlong eq ψ φ) =
      ratioG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  have hn : ∀ v : EuclideanSpace ℂ ια, ‖prodAlong eq v φ‖ = ‖v‖ := fun v =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (norm_sq_prodAlong eq v φ hφ)
  rw [ratioG, ratioG, centeredG_lift eq hφ, centeredG_lift eq hφ, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one, hn, hn]

variable {dx dy dz : ℕ} {ax bx cx ex ay b_y cy ey az bz cz ez : ℝ}

theorem norm_PsiStar3D (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    ‖PsiStar3D dx dy dz‖ = 1 := by
  rw [PsiStar3D_eq_eX]
  exact norm_prodAlong_eq_one _ (norm_psiStar hx) (norm_rest hy hz)

theorem ratio_pair_axis_x (hax : ax ≠ 0) (hcx : cx ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy)
    (hz : 2 ≤ dz) :
    ratioG (affineOp ax bx (TX dx dy dz)) (affineOp cx ex (PX dx dy dz)) (PsiStar3D dx dy dz) =
      CoherenceConstant dx := by
  rw [ratioG_affineOp hax hcx _ _ _ _ (norm_PsiStar3D hx hy hz), PsiStar3D_eq_eX, TX, PX,
    ratioG_lift _ (norm_rest hy hz)]
  exact ratioG_TdPd hx

theorem ratio_pair_axis_y (hay : ay ≠ 0) (hcy : cy ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy)
    (hz : 2 ≤ dz) :
    ratioG (affineOp ay b_y (TY dx dy dz)) (affineOp cy ey (PY dx dy dz)) (PsiStar3D dx dy dz) =
      CoherenceConstant dy := by
  rw [ratioG_affineOp hay hcy _ _ _ _ (norm_PsiStar3D hx hy hz), PsiStar3D_eq_eY, TY, PY,
    ratioG_lift _ (norm_rest hx hz)]
  exact ratioG_TdPd hy

theorem ratio_pair_axis_z (haz : az ≠ 0) (hcz : cz ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy)
    (hz : 2 ≤ dz) :
    ratioG (affineOp az bz (TZ dx dy dz)) (affineOp cz ez (PZ dx dy dz)) (PsiStar3D dx dy dz) =
      CoherenceConstant dz := by
  rw [ratioG_affineOp haz hcz _ _ _ _ (norm_PsiStar3D hx hy hz), PsiStar3D_eq_eZ, TZ, PZ,
    ratioG_lift _ (norm_rest hx hy)]
  exact ratioG_TdPd hz

/-- **The volumetric quantum of three pairs**, each in its own units, is `𝒱(dx, dy, dz)`. -/
theorem volQuantum_pairs (hax : ax ≠ 0) (hcx : cx ≠ 0) (hay : ay ≠ 0) (hcy : cy ≠ 0)
    (haz : az ≠ 0) (hcz : cz ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    (ratioG (affineOp ax bx (TX dx dy dz)) (affineOp cx ex (PX dx dy dz))
          (PsiStar3D dx dy dz) - 1) *
        (ratioG (affineOp ay b_y (TY dx dy dz)) (affineOp cy ey (PY dx dy dz))
          (PsiStar3D dx dy dz) - 1) *
        (ratioG (affineOp az bz (TZ dx dy dz)) (affineOp cz ez (PZ dx dy dz))
          (PsiStar3D dx dy dz) - 1) =
      volQuantum dx dy dz := by
  rw [ratio_pair_axis_x hax hcx hx hy hz, ratio_pair_axis_y hay hcy hx hy hz,
    ratio_pair_axis_z haz hcz hx hy hz, volQuantum, dimQuantum, dimQuantum, dimQuantum,
    geometricGap, geometricGap, geometricGap]

/-- **Certificate for three pairs.** Whatever the units of each pair, the product of their
excesses is zero exactly at a seed axis, strictly positive from `4 × 4 × 4` on, and strictly
below `δ_∞³`, which no cube reaches. -/
theorem volQuantum_pairs_certificate (hax : ax ≠ 0) (hcx : cx ≠ 0) (hay : ay ≠ 0) (hcy : cy ≠ 0)
    (haz : az ≠ 0) (hcz : cz ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    let 𝒱 :=
      (ratioG (affineOp ax bx (TX dx dy dz)) (affineOp cx ex (PX dx dy dz))
          (PsiStar3D dx dy dz) - 1) *
        (ratioG (affineOp ay b_y (TY dx dy dz)) (affineOp cy ey (PY dx dy dz))
          (PsiStar3D dx dy dz) - 1) *
        (ratioG (affineOp az bz (TZ dx dy dz)) (affineOp cz ez (PZ dx dy dz))
          (PsiStar3D dx dy dz) - 1)
    (𝒱 = 0 ↔ (dx = 2 ∨ dx = 3) ∨ (dy = 2 ∨ dy = 3) ∨ (dz = 2 ∨ dz = 3)) ∧
      (4 ≤ dx → 4 ≤ dy → 4 ≤ dz → 0 < 𝒱 ∧ 𝒱 < deltaInf ^ 3) := by
  intro 𝒱
  have h : 𝒱 = volQuantum dx dy dz :=
    volQuantum_pairs hax hcx hay hcy haz hcz hx hy hz
  rw [h]
  exact ⟨volQuantum_eq_zero_iff hx hy hz, fun hx4 hy4 hz4 =>
    ⟨volQuantum_pos hx4 hy4 hz4, volQuantum_lt_ceiling hx4 hy4 hz4⟩⟩

end Cubo

end ConjugatePairs

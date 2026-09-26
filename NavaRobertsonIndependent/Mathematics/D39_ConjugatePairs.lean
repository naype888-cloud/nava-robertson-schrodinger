/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum

/-!
# D39 — Every conjugate pair realized on `T_d : P_d`

A pair of observables `(A, B)` realized on `T_d : P_d` is `A = a T_d + b`, `B = c P_d + e`
with real `a, c ≠ 0`: the scales `a, c` and the offsets `b, e` are the units and origins of the
pair (position–momentum, number–phase, charge–flux, …). None of them reaches the statements
of NRS and NRS³:

* the fluctuation vectors of `(A, B)` at a unit state are those of `(T_d, P_d)` times `a` and
  `c` (`centradoG_afin`), so their angle and the Robertson–Schrödinger ratio
  `R = σ_A σ_B / |⟨Ã ψ, B̃ ψ⟩|` do not change (`anguloG_afin`, `razonG_afin`);
* at the maximal-tension state, `R = C_Nava(d)` for every such pair (`razon_par`): it
  saturates exactly at `d = 2, 3` (`satura_par_iff`), strictly from `d = 4` on
  (`angulo_par_pos`), the opening grows strictly with `d` whatever the units of each pair
  (`angulo_par_lt_of_lt`) and stays below `arccos (1 / C_∞)`, which no `d` attains
  (`angulo_par_lt_limite`);
* on the cube `dx × dy × dz` of `D37`, with one pair per axis in its own units, each axis
  carries `C_Nava(d_axis)` (`razon_par_eje_x/y/z`), and the product of the three excesses is
  the volumetric quantum `𝒱(dx, dy, dz)` of `D37e` (`cuantoVolumetrico_pares`): zero exactly
  when some axis has `2` or `3` sites, strictly positive from `4 × 4 × 4` on, strictly below
  `δ_∞³` (`cuanto_volumetrico_pares`).

The only thing a pair changes is its floor `|a c| · ½ |⟨[T_d, P_d]⟩| = |a c| / (d − 1)`, in
its own units. The catalogue of named pairs is in `docs/PAIRS.md`.
-/

@[expose] public noncomputable section

open Real TransportePosicion NavaRobertsonSchrodingerEDUI ConstructorEspectralTP Gnomon
open PathGraph3DNRS SaturacionAutovectores AnguloNRS CuantoDimensional CuantoVolumetrico

namespace ParesConjugados

/-! ## 1. Affine invariance on any finite site set -/

section General

variable {ι : Type*} [Fintype ι]

/-- The observable `a L + b`: `L` in units `a` with origin `b`. -/
def afin (a b : ℝ) (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  (a : ℂ) • L + (b : ℂ) • LinearMap.id

/-- The Robertson–Schrödinger ratio `‖x‖ ‖y‖ / |⟨x, y⟩|` of the fluctuation vectors
`x = (L − ⟨L⟩)Ψ`, `y = (M − ⟨M⟩)Ψ`: `1` exactly when the inequality saturates. -/
def razonG (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  ‖centradoG L Ψ‖ * ‖centradoG M Ψ‖ / ‖inner ℂ (centradoG L Ψ) (centradoG M Ψ)‖

variable {Ψ : EuclideanSpace ℂ ι}

theorem mediaG_afin (a b : ℝ) (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hΨ : ‖Ψ‖ = 1) : mediaG (afin a b L) Ψ = a * mediaG L Ψ + b := by
  have h1 : inner ℂ Ψ Ψ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
  simp only [mediaG, afin, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_add_right, inner_smul_right, h1, mul_one, Complex.add_re, Complex.re_ofReal_mul,
    Complex.ofReal_re]

/-- The fluctuation vector of `a L + b` is `a` times that of `L`. -/
theorem centradoG_afin (a b : ℝ) (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hΨ : ‖Ψ‖ = 1) : centradoG (afin a b L) Ψ = (a : ℂ) • centradoG L Ψ := by
  rw [centradoG, centradoG, mediaG_afin a b L hΨ]
  simp only [afin, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  push_cast
  module

/-- Units do not reach the angle between the fluctuation vectors. -/
theorem anguloG_afin {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (b e : ℝ)
    (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (hΨ : ‖Ψ‖ = 1) :
    anguloG (afin a b L) (afin c e M) Ψ = anguloG L M Ψ := by
  have hac : ‖(a : ℂ)‖ * ‖(c : ℂ)‖ ≠ 0 := by simp [ha, hc]
  rw [anguloG, anguloG, centradoG_afin a b L hΨ, centradoG_afin c e M hΨ, inner_smul_left,
    inner_smul_right, norm_mul, norm_mul, Complex.norm_conj, norm_smul, norm_smul]
  congr 1
  rw [show ‖(a : ℂ)‖ * (‖(c : ℂ)‖ * ‖inner ℂ (centradoG L Ψ) (centradoG M Ψ)‖) /
      (‖(a : ℂ)‖ * ‖centradoG L Ψ‖ * (‖(c : ℂ)‖ * ‖centradoG M Ψ‖)) =
      (‖(a : ℂ)‖ * ‖(c : ℂ)‖) * ‖inner ℂ (centradoG L Ψ) (centradoG M Ψ)‖ /
      ((‖(a : ℂ)‖ * ‖(c : ℂ)‖) * (‖centradoG L Ψ‖ * ‖centradoG M Ψ‖)) by ring]
  exact mul_div_mul_left _ _ hac

/-- Units do not reach the Robertson–Schrödinger ratio. -/
theorem razonG_afin {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (b e : ℝ)
    (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (hΨ : ‖Ψ‖ = 1) :
    razonG (afin a b L) (afin c e M) Ψ = razonG L M Ψ := by
  have hac : ‖(a : ℂ)‖ * ‖(c : ℂ)‖ ≠ 0 := by simp [ha, hc]
  rw [razonG, razonG, centradoG_afin a b L hΨ, centradoG_afin c e M hΨ, inner_smul_left,
    inner_smul_right, norm_mul, norm_mul, Complex.norm_conj, norm_smul, norm_smul]
  rw [show ‖(a : ℂ)‖ * ‖centradoG L Ψ‖ * (‖(c : ℂ)‖ * ‖centradoG M Ψ‖) /
      (‖(a : ℂ)‖ * (‖(c : ℂ)‖ * ‖inner ℂ (centradoG L Ψ) (centradoG M Ψ)‖)) =
      (‖(a : ℂ)‖ * ‖(c : ℂ)‖) * (‖centradoG L Ψ‖ * ‖centradoG M Ψ‖) /
      ((‖(a : ℂ)‖ * ‖(c : ℂ)‖) * ‖inner ℂ (centradoG L Ψ) (centradoG M Ψ)‖) by ring]
  exact mul_div_mul_left _ _ hac

end General

/-! ## 2. One pair on `T_d : P_d` -/

section Recta

variable {a b c e : ℝ} {d : ℕ}

theorem razonG_TdPd (hd : 2 ≤ d) :
    razonG (TdOp d) (PdOp d) (psiStar d) = CoherenceConstant d := by
  have h := cos_anguloNRS hd
  rw [razonG, ← one_div_div]
  exact (congrArg (1 / ·) h).trans (one_div_one_div _)

/-- **The ratio of every pair is `C_Nava(d)`** at the maximal-tension state. -/
theorem razon_par (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    razonG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) = CoherenceConstant d := by
  rw [razonG_afin ha hc b e _ _ (norma_psiStar hd), razonG_TdPd hd]

theorem angulo_par (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    anguloG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) = anguloNRS d :=
  anguloG_afin ha hc b e _ _ (norma_psiStar hd)

/-- **Every pair saturates exactly at `d = 2, 3`.** -/
theorem satura_par_iff (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    anguloG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) = 0 ↔ d = 2 ∨ d = 3 := by
  rw [angulo_par ha hc hd]
  exact anguloNRS_eq_zero_iff hd

theorem angulo_par_pos (ha : a ≠ 0) (hc : c ≠ 0) (hd : 4 ≤ d) :
    0 < anguloG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) := by
  rw [angulo_par ha hc (by omega)]
  exact anguloNRS_pos hd

/-- **The opening grows with `d`**, even if the two rows carry different units. -/
theorem angulo_par_lt_of_lt {a' b' c' e' : ℝ} {d' : ℕ} (ha : a ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hc' : c' ≠ 0) (hd : 4 ≤ d) (h : d < d') :
    anguloG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) <
      anguloG (afin a' b' (TdOp d')) (afin c' e' (PdOp d')) (psiStar d') := by
  rw [angulo_par ha hc (by omega), angulo_par ha' hc' (by omega)]
  exact anguloNRS_strictMonoOn (show 4 ≤ d from hd) (show 4 ≤ d' by omega) h

theorem angulo_par_lt_limite (ha : a ≠ 0) (hc : c ≠ 0) (hd : 4 ≤ d) :
    anguloG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) <
      arccos (1 / CoherenceConstantInf) := by
  rw [angulo_par ha hc (by omega)]
  exact anguloNRS_lt_limite hd

/-- The excess of every pair over the floor is the dimensional quantum `δ(d)` of `D25`. -/
theorem cuanto_par (ha : a ≠ 0) (hc : c ≠ 0) (hd : 2 ≤ d) :
    razonG (afin a b (TdOp d)) (afin c e (PdOp d)) (psiStar d) - 1 = cuantoDim d := by
  rw [razon_par ha hc hd, cuantoDim, geometricGap]

end Recta

/-! ## 3. Three pairs on the cube -/

section Cubo

variable {ια ιβ ιγ : Type*} [Fintype ιγ] [Fintype ια] [Fintype ιβ]
  [DecidableEq ιγ] [DecidableEq ια] [DecidableEq ιβ]

theorem razonG_lift (eq : ιγ ≃ ια × ιβ) {φ : EuclideanSpace ℂ ιβ} (hφ : ‖φ‖ = 1)
    (A B : Matrix ια ια ℂ) (ψ : EuclideanSpace ℂ ια) :
    razonG (Matrix.toEuclideanLin (liftAlong eq A)) (Matrix.toEuclideanLin (liftAlong eq B))
        (prodAlong eq ψ φ) =
      razonG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  have hn : ∀ v : EuclideanSpace ℂ ια, ‖prodAlong eq v φ‖ = ‖v‖ := fun v =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (norm_sq_prodAlong eq v φ hφ)
  rw [razonG, razonG, centradoG_lift eq hφ, centradoG_lift eq hφ, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one, hn, hn]

variable {dx dy dz : ℕ} {ax bx cx ex ay b_y cy ey az bz cz ez : ℝ}

theorem norm_PsiStar3D (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    ‖PsiStar3D dx dy dz‖ = 1 := by
  rw [PsiStar3D_eq_eX]
  exact norm_prodAlong_eq_one _ (norma_psiStar hx) (norm_resto hy hz)

theorem razon_par_eje_x (hax : ax ≠ 0) (hcx : cx ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy)
    (hz : 2 ≤ dz) :
    razonG (afin ax bx (TX dx dy dz)) (afin cx ex (PX dx dy dz)) (PsiStar3D dx dy dz) =
      CoherenceConstant dx := by
  rw [razonG_afin hax hcx _ _ _ _ (norm_PsiStar3D hx hy hz), PsiStar3D_eq_eX, TX, PX,
    razonG_lift _ (norm_resto hy hz)]
  exact razonG_TdPd hx

theorem razon_par_eje_y (hay : ay ≠ 0) (hcy : cy ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy)
    (hz : 2 ≤ dz) :
    razonG (afin ay b_y (TY dx dy dz)) (afin cy ey (PY dx dy dz)) (PsiStar3D dx dy dz) =
      CoherenceConstant dy := by
  rw [razonG_afin hay hcy _ _ _ _ (norm_PsiStar3D hx hy hz), PsiStar3D_eq_eY, TY, PY,
    razonG_lift _ (norm_resto hx hz)]
  exact razonG_TdPd hy

theorem razon_par_eje_z (haz : az ≠ 0) (hcz : cz ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy)
    (hz : 2 ≤ dz) :
    razonG (afin az bz (TZ dx dy dz)) (afin cz ez (PZ dx dy dz)) (PsiStar3D dx dy dz) =
      CoherenceConstant dz := by
  rw [razonG_afin haz hcz _ _ _ _ (norm_PsiStar3D hx hy hz), PsiStar3D_eq_eZ, TZ, PZ,
    razonG_lift _ (norm_resto hx hy)]
  exact razonG_TdPd hz

/-- **The volumetric quantum of three pairs**, each in its own units, is `𝒱(dx, dy, dz)`. -/
theorem cuantoVolumetrico_pares (hax : ax ≠ 0) (hcx : cx ≠ 0) (hay : ay ≠ 0) (hcy : cy ≠ 0)
    (haz : az ≠ 0) (hcz : cz ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    (razonG (afin ax bx (TX dx dy dz)) (afin cx ex (PX dx dy dz)) (PsiStar3D dx dy dz) - 1) *
        (razonG (afin ay b_y (TY dx dy dz)) (afin cy ey (PY dx dy dz))
          (PsiStar3D dx dy dz) - 1) *
        (razonG (afin az bz (TZ dx dy dz)) (afin cz ez (PZ dx dy dz))
          (PsiStar3D dx dy dz) - 1) =
      cuantoVolumetrico dx dy dz := by
  rw [razon_par_eje_x hax hcx hx hy hz, razon_par_eje_y hay hcy hx hy hz,
    razon_par_eje_z haz hcz hx hy hz, cuantoVolumetrico, cuantoDim, cuantoDim, cuantoDim,
    geometricGap, geometricGap, geometricGap]

/-- **Certificate for three pairs.** Whatever the units of each pair, the product of their
excesses is zero exactly at a seed axis, strictly positive from `4 × 4 × 4` on, and strictly
below `δ_∞³`, which no cube reaches. -/
theorem cuanto_volumetrico_pares (hax : ax ≠ 0) (hcx : cx ≠ 0) (hay : ay ≠ 0) (hcy : cy ≠ 0)
    (haz : az ≠ 0) (hcz : cz ≠ 0) (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    let 𝒱 :=
      (razonG (afin ax bx (TX dx dy dz)) (afin cx ex (PX dx dy dz)) (PsiStar3D dx dy dz) - 1) *
        (razonG (afin ay b_y (TY dx dy dz)) (afin cy ey (PY dx dy dz))
          (PsiStar3D dx dy dz) - 1) *
        (razonG (afin az bz (TZ dx dy dz)) (afin cz ez (PZ dx dy dz))
          (PsiStar3D dx dy dz) - 1)
    (𝒱 = 0 ↔ (dx = 2 ∨ dx = 3) ∨ (dy = 2 ∨ dy = 3) ∨ (dz = 2 ∨ dz = 3)) ∧
      (4 ≤ dx → 4 ≤ dy → 4 ≤ dz → 0 < 𝒱 ∧ 𝒱 < deltaInf ^ 3) := by
  intro 𝒱
  have h : 𝒱 = cuantoVolumetrico dx dy dz :=
    cuantoVolumetrico_pares hax hcx hay hcy haz hcz hx hy hz
  rw [h]
  exact ⟨cuantoVolumetrico_eq_cero_iff hx hy hz, fun hx4 hy4 hz4 =>
    ⟨cuantoVolumetrico_pos hx4 hy4 hz4, cuantoVolumetrico_techo hx4 hy4 hz4⟩⟩

end Cubo

end ParesConjugados

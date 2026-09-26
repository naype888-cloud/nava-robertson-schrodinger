/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D3_PathGraph

/-!
# D28 — Bakry–Émery curvature of the path: `CD(0, 2)`, sharp

With the combinatorial Laplacian `Δf(x) = f(x−1) + f(x+1) − 2f(x)` and the Bakry–Émery forms
`Γ(f) = ½[Δ(f²) − 2f Δf]`, `Γ₂(f) = ½[Δ(Γf) − 2Γ(f, Δf)]`, the discrete Bochner identity

`Γ₂(f)(x) = ½(Δf(x))² + ¼(f(x−2) − 2f(x−1) + f(x))² + ¼(f(x) − 2f(x+1) + f(x+2))²`

holds exactly. So the interior of the path satisfies `CD(0, 2)`, and both constants are sharp:
some `f` has `Γ₂ = 0` with `Γ > 0` (no `κ > 0`), some has `Δf ≠ 0` with `Γ₂ = ½(Δf)²` (no
`n < 2`). The path, the only local complete graph (`D3`), is flat; `D28b` reaches the same
conclusion through Ollivier–Ricci.

## Main results

- `BakryEmery.gamma2_eq_bochner` : the discrete Bochner identity.
- `BakryEmery.path_CD02` : the interior of `graphTP d` satisfies `CD(0, 2)`.
- `BakryEmery.kappa_zero_sharp`, `BakryEmery.dim_two_sharp` : both constants are sharp.
-/

@[expose] public noncomputable section

namespace BakryEmery

open TransportPosition

/-! ## Five consecutive values -/

/-- The Laplacian at three consecutive values: `Δf(x) = f(x−1) + f(x+1) − 2f(x)`. -/
def laplacian3 (xl xc xr : ℝ) : ℝ := xl + xr - 2 * xc

/-- The carré du champ `Γ(f)(x)` from three consecutive values. -/
def gamma3 (xl xc xr : ℝ) : ℝ := ((xl - xc) ^ 2 + (xr - xc) ^ 2) / 2

/-- `Γ₂(f)(x)` from `(f(x−2), f(x−1), f(x), f(x+1), f(x+2))`: the expansion of
`½[Δ(Γf)(x) − 2Γ(f, Δf)(x)]`. -/
def gamma2Five (a b c0 c e : ℝ) : ℝ :=
  a ^ 2 / 4 - a * b + a * c0 / 2 + 3 * b ^ 2 / 2 + b * c - 3 * b * c0
    + 3 * c ^ 2 / 2 - 3 * c * c0 - c * e + 5 * c0 ^ 2 / 2 + c0 * e / 2 + e ^ 2 / 4

/-- **Discrete Bochner identity.** `Γ₂ = (Δf)²/2` plus two squares measuring the failure of
affine continuation of `f` at each end. -/
theorem gamma2_eq_bochner (a b c0 c e : ℝ) :
    gamma2Five a b c0 c e
      = (laplacian3 b c0 c) ^ 2 / 2 + (a - 2 * b + c0) ^ 2 / 4 + (e - 2 * c + c0) ^ 2 / 4 := by
  unfold gamma2Five laplacian3
  ring

/-- **`CD(0, 2)`.** `Γ₂ ≥ ½(Δf)²` at every interior point. -/
theorem cd_zero_two (a b c0 c e : ℝ) :
    (laplacian3 b c0 c) ^ 2 / 2 ≤ gamma2Five a b c0 c e := by
  rw [gamma2_eq_bochner]
  nlinarith [sq_nonneg (a - 2 * b + c0), sq_nonneg (e - 2 * c + c0)]

/-- `Γ₂ ≥ 0` in the interior. -/
theorem gamma2_nonneg (a b c0 c e : ℝ) : 0 ≤ gamma2Five a b c0 c e := by
  have h := cd_zero_two a b c0 c e
  nlinarith [sq_nonneg (laplacian3 b c0 c)]

/-- If `f` continues affinely beyond the neighbours, `Γ₂ = ½(Δf)²`. -/
theorem gamma2_eq_of_affine_extension (b c0 c : ℝ) :
    gamma2Five (2 * b - c0) b c0 c (2 * c - c0) = (laplacian3 b c0 c) ^ 2 / 2 := by
  have h := gamma2_eq_bochner (2 * b - c0) b c0 c (2 * c - c0)
  have e1 : (2 * b - c0) - 2 * b + c0 = 0 := by ring
  have e2 : (2 * c - c0) - 2 * c + c0 = 0 := by ring
  rw [e1, e2] at h
  simpa using h

/-- **`n = 2` is sharp.** Some `f` has `Δf(x) ≠ 0` and `Γ₂ = ½(Δf)²`. -/
theorem dim_two_sharp :
    ∃ a b c0 c e : ℝ, laplacian3 b c0 c ≠ 0 ∧
      gamma2Five a b c0 c e = (laplacian3 b c0 c) ^ 2 / 2 := by
  refine ⟨2, 1, 0, 0, 0, ?_, ?_⟩
  · unfold laplacian3; norm_num
  · simpa using gamma2_eq_of_affine_extension 1 0 0

/-- **`κ = 0` is sharp.** Some `f` has `Δf(x) = 0`, `Γ(f)(x) > 0` and `Γ₂(f)(x) = 0`. -/
theorem kappa_zero_sharp :
    ∃ a b c0 c e : ℝ,
      laplacian3 b c0 c = 0 ∧ 0 < gamma3 b c0 c ∧ gamma2Five a b c0 c e = 0 := by
  refine ⟨2, 1, 0, -1, -2, ?_, ?_, ?_⟩
  · unfold laplacian3; norm_num
  · unfold gamma3; norm_num
  · unfold gamma2Five; norm_num

/-! ## The interior of `graphTP d` -/

/-- The neighbour two steps to the left of `i`. -/
def im2 {d : ℕ} (i : Fin d) (h : 2 ≤ i.val) : Fin d :=
  ⟨i.val - 2, by have := i.isLt; omega⟩

/-- The neighbour to the left of `i`. -/
def im1 {d : ℕ} (i : Fin d) (h : 1 ≤ i.val) : Fin d :=
  ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The neighbour to the right of `i`. -/
def ip1 {d : ℕ} (i : Fin d) (h : i.val + 1 < d) : Fin d :=
  ⟨i.val + 1, h⟩

/-- The neighbour two steps to the right of `i`. -/
def ip2 {d : ℕ} (i : Fin d) (h : i.val + 2 < d) : Fin d :=
  ⟨i.val + 2, h⟩

/-- `im1 i` and `ip1 i` are neighbours of `i` in `graphTP d`. -/
theorem adj_im1 {d : ℕ} (i : Fin d) (h : 1 ≤ i.val) :
    (graphTP d).Adj i (im1 i h) := by
  rw [graphTP_adj]
  right
  show (im1 i h).val + 1 = i.val
  simp only [im1]
  omega

theorem adj_ip1 {d : ℕ} (i : Fin d) (h : i.val + 1 < d) :
    (graphTP d).Adj i (ip1 i h) := by
  rw [graphTP_adj]
  left
  show i.val + 1 = (ip1 i h).val
  simp [ip1]

/-- An index with two sites on each side: `i−2, …, i+2` all exist in `Fin d`. -/
def IsDeepInterior (d : ℕ) (i : Fin d) : Prop := 2 ≤ i.val ∧ i.val + 2 < d

/-- The Laplacian of `f : Fin d → ℝ` at an interior vertex of `graphTP d`. -/
def pathLaplacian {d : ℕ} (f : Fin d → ℝ) (i : Fin d) (h : IsDeepInterior d i) : ℝ :=
  have h1 : 2 ≤ i.val := h.1
  have h2 : i.val + 2 < d := h.2
  laplacian3 (f (im1 i (by omega))) (f i) (f (ip1 i (by omega)))

/-- `Γ(f)` on `graphTP d` at an interior vertex. -/
def pathGamma {d : ℕ} (f : Fin d → ℝ) (i : Fin d) (h : IsDeepInterior d i) : ℝ :=
  have h1 : 2 ≤ i.val := h.1
  have h2 : i.val + 2 < d := h.2
  gamma3 (f (im1 i (by omega))) (f i) (f (ip1 i (by omega)))

/-- `Γ₂(f)` on `graphTP d` at an interior vertex. -/
def pathGamma2 {d : ℕ} (f : Fin d → ℝ) (i : Fin d) (h : IsDeepInterior d i) : ℝ :=
  have h1 : 2 ≤ i.val := h.1
  have h2 : i.val + 2 < d := h.2
  gamma2Five (f (im2 i (by omega))) (f (im1 i (by omega))) (f i)
    (f (ip1 i (by omega))) (f (ip2 i (by omega)))

/-- **The path is flat.** The interior of `graphTP d` satisfies `CD(0, 2)` for every `d`. -/
theorem path_CD02 {d : ℕ} (f : Fin d → ℝ) (i : Fin d)
    (h : IsDeepInterior d i) :
    (pathLaplacian f i h) ^ 2 / 2 ≤ pathGamma2 f i h := by
  unfold pathLaplacian pathGamma2
  exact cd_zero_two _ _ _ _ _

/-- `Γ₂ ≥ 0` at every interior vertex of `graphTP d`. -/
theorem pathGamma2_nonneg {d : ℕ} (f : Fin d → ℝ) (i : Fin d)
    (h : IsDeepInterior d i) : 0 ≤ pathGamma2 f i h := by
  unfold pathGamma2
  exact gamma2_nonneg _ _ _ _ _

/-!
`path_CD02` is the bound `κ ≥ 0`; `kappa_zero_sharp` attains it with `Γ₂ = 0`, `Γ > 0`, so the
Bakry–Émery curvature of the path is `κ = 0`, as Ollivier–Ricci (`D28b`).
-/

end BakryEmery

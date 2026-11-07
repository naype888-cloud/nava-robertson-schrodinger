/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.RCLike.Basic
/-!
# D54 — The covariance bound for a nonlinear map

For a linear map `A`, the distance of `B x` to its component along `x` bounds the covariance:
`|f(ABx) - f(Ax) f(Bx)| ≤ K ‖Bx - f(Bx) x‖` (Heisenberg–Robertson–Schrödinger). For a nonlinear
`A`, the covariance does not appear: the Lipschitz estimate bounds
`|f(A(Bx)) - f(A(f(Bx) x))|`, the difference of `A` between `Bx` and its component along `x`.
The two agree when `A (c x) = c A x`. The literal statement with `f(Ax) f(Bx)` fails for
`A(u) = u²` (`not_covariance_bound_sq`).

## Main results

- `nonlinear_bound` : `|f(A(Bx)) - f(A(f(Bx) x))| ≤ K ‖Bx - f(Bx) x‖`.
- `covariance_bound_of_homogeneous` : the covariance bound when `A (c x) = c A x`.
- `not_covariance_bound_sq` : for `A(u) = u²` the covariance bound fails.
-/
@[expose] public section
namespace NonlinearCovariance

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The bound for a nonlinear map**: if `u ↦ f(Au) - f(Ax) f(u)` is `K`-Lipschitz, then
`|f(A(Bx)) - f(A(f(Bx) x))| ≤ K ‖Bx - f(Bx) x‖`. -/
theorem nonlinear_bound (f : E →L[𝕜] 𝕜) (A B : E → E) (x : E) (hfx : f x = 1) {K : ℝ}
    (hK : ∀ u w, ‖(f (A u) - f (A x) * f u) - (f (A w) - f (A x) * f w)‖ ≤ K * ‖u - w‖) :
    ‖f (A (B x)) - f (A (f (B x) • x))‖ ≤ K * ‖B x - f (B x) • x‖ := by
  have h := hK (B x) (f (B x) • x)
  have e : (f (A (B x)) - f (A x) * f (B x)) - (f (A (f (B x) • x)) - f (A x) * f (f (B x) • x))
      = f (A (B x)) - f (A (f (B x) • x)) := by
    rw [map_smul, hfx, smul_eq_mul, mul_one]
    ring
  rwa [e] at h

/-- **The covariance bound for a homogeneous `A`**: if `A (c x) = c A x`, the covariance is bounded
as in the linear case. -/
theorem covariance_bound_of_homogeneous (f : E →L[𝕜] 𝕜) (A B : E → E) (x : E) (hfx : f x = 1)
    {K : ℝ} (hK : ∀ u w, ‖(f (A u) - f (A x) * f u) - (f (A w) - f (A x) * f w)‖ ≤ K * ‖u - w‖)
    (hA : A (f (B x) • x) = f (B x) • A x) :
    ‖f (A (B x)) - f (A x) * f (B x)‖ ≤ K * ‖B x - f (B x) • x‖ := by
  have h := nonlinear_bound f A B x hfx hK
  rwa [hA, map_smul, smul_eq_mul, mul_comm] at h

/-- **The covariance bound fails for `A(u) = u²`**: with `x = 1`, `B u = 2u`, the distance of `Bx` to
its component along `x` is zero, and the covariance is `2`. -/
theorem not_covariance_bound_sq :
    ¬ ∃ K : ℝ, |(2 : ℝ) ^ 2 - 1 ^ 2 * 2| ≤ K * ‖(2 : ℝ) - 2 * 1‖ := by
  rintro ⟨K, h⟩
  norm_num at h

end NonlinearCovariance

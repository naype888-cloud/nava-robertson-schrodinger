/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module
public import NavaRobertsonIndependent.Mathematics.D52_LatticeViscosity
public import NavaRobertsonIndependent.Mathematics.D54_NonlinearCovariance
/-!
# D53 — Nonlinear Euler on the lattice: the quadratic transport conserves the kinetic energy

The gradient of the positions is the bracket of the transport with the position,
`G_d = [T_d, P_d]`: its entries are `T_{ij} (P_j - P_i)`, real and antisymmetric. The nonlinear
transport of a velocity `v` by itself, in the skew form, is
`N(v) = ⅓ (G (v ∘ v) + v ∘ G v)`. It is quadratic (`N(c v) = c² N(v)`, `N(0) = 0`), and it
conserves the kinetic energy: `⟨v, N(v)⟩ = 0`, because `G` is antisymmetric.

## Main results

- `gradR_antisymm` : `G_d` is antisymmetric.
- `eulerAdv_zero`, `eulerAdv_smul` : `N` is quadratic.
- `energy_conserved` : `⟨v, N(v)⟩ = 0`.
- `euler_covariance_bound` : the covariance bound of `D54` for `N`, where `N (c x) = c² N x`.
-/
@[expose] public noncomputable section
open Matrix
namespace TransportPosition

variable {d : ℕ}

/-- The real gradient of the positions: `G_{ij} = T_{ij} (P_j - P_i)`, the entries of
`[T_d, P_d]`. -/
def gradR (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (if MinStep i j then 1 / rho d else 0) * (posCoord d j - posCoord d i)

lemma gradR_antisymm (d : ℕ) : (gradR d)ᵀ = -gradR d := by
  ext i j
  simp only [gradR, Matrix.transpose_apply, Matrix.neg_apply]
  by_cases h : MinStep i j
  · simp [h, minStep_symm.mp h]
    ring
  · have h' : ¬ MinStep j i := fun h' => h (minStep_symm.mp h')
    simp [h, h']

/-- The gradient is the bracket `[T_d, P_d]`. -/
lemma gradR_map (d : ℕ) :
    (gradR d).map (algebraMap ℝ ℂ) = Td d * Pd d - Pd d * Td d := by
  ext i j
  simp only [gradR, Td, Ad, Pd, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply]
  by_cases h : MinStep i j
  · simp [h]
    ring
  · simp [h]

/-- The nonlinear transport of a velocity by itself, in the skew form. -/
def eulerAdv (d : ℕ) (v : Fin d → ℝ) : Fin d → ℝ :=
  (1 / 3 : ℝ) • (gradR d *ᵥ (v * v) + v * (gradR d *ᵥ v))

lemma eulerAdv_zero (d : ℕ) : eulerAdv d 0 = 0 := by
  simp [eulerAdv]

/-- **The transport is quadratic**: `N(c v) = c² N(v)`. -/
lemma eulerAdv_smul (d : ℕ) (c : ℝ) (v : Fin d → ℝ) :
    eulerAdv d (c • v) = c ^ 2 • eulerAdv d v := by
  ext i
  simp only [eulerAdv, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul, Matrix.mulVec_smul]
  have : (c • v) * (c • v) = c ^ 2 • (v * v) := by
    ext k; simp [Pi.mul_apply]; ring
  rw [this, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The kinetic energy is conserved**: `⟨v, N(v)⟩ = 0`. -/
theorem energy_conserved (d : ℕ) (v : Fin d → ℝ) : v ⬝ᵥ eulerAdv d v = 0 := by
  have h1 : v ⬝ᵥ (gradR d *ᵥ (v * v)) = -((gradR d *ᵥ v) ⬝ᵥ (v * v)) := by
    rw [Matrix.dotProduct_mulVec]
    have : v ᵥ* gradR d = -(gradR d *ᵥ v) := by
      rw [← Matrix.vecMul_transpose, gradR_antisymm, Matrix.vecMul_neg, neg_neg]
    rw [this, neg_dotProduct]
  have h2 : v ⬝ᵥ (v * (gradR d *ᵥ v)) = (gradR d *ᵥ v) ⬝ᵥ (v * v) := by
    simp only [dotProduct, Pi.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [eulerAdv, dotProduct_smul, dotProduct_add, h1, h2, smul_eq_mul]
  ring

/-- **The covariance bound for the quadratic transport** (`D54`): since `N (c x) = c² N x`, for a
functional `f` with `f x = 1` the covariance of `N` and any `B` is bounded by the distance of `B x`
to its component along `x`, with `f (B x)²` in place of `f (B x)`:
`|f(N(Bx)) - f(Bx)² f(Nx)| ≤ K ‖Bx - f(Bx) x‖`. -/
theorem euler_covariance_bound (f : (Fin d → ℝ) →L[ℝ] ℝ) (B : (Fin d → ℝ) → (Fin d → ℝ))
    (x : Fin d → ℝ) (hfx : f x = 1) {K : ℝ}
    (hK : ∀ u w, ‖(f (eulerAdv d u) - f (eulerAdv d x) * f u) -
        (f (eulerAdv d w) - f (eulerAdv d x) * f w)‖ ≤ K * ‖u - w‖) :
    ‖f (eulerAdv d (B x)) - f (B x) ^ 2 * f (eulerAdv d x)‖ ≤ K * ‖B x - f (B x) • x‖ := by
  have h := NonlinearCovariance.nonlinear_bound f (eulerAdv d) B x hfx hK
  rwa [eulerAdv_smul, map_smul, smul_eq_mul] at h

end TransportPosition

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37g_LiebRobinson
public import NavaRobertsonIndependent.Mathematics.D37c_CubeSpectrum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# D38 — Dispersion and group velocity of transport

The sine modes of `D6` have energy `ε(θ) = 2 cos θ / ρ_d`, with group velocity
`v(θ) = −ε'(θ) = 2 sin θ / ρ_d`, largest at the band centre `θ = π/2`. Under
`U(t) = exp(−i t T_d)` position obeys `d/dt (U† P_d U) = U† K_d U`: the tension is velocity.
In sites, the velocity of a state is `((d−1)/2) ⟨K_d⟩`; it never exceeds one site per unit of
time, and `ψ*` moves at exactly that speed, the slope of the cone of `D37f`. On the cube
`Ψ*` reaches the bound on the three axes at once: velocity `(1, 1, 1)`, length `√3`.

## Main results

- `GroupVelocity.hasDerivAt_dispersion` : `ε' = −v`.
- `GroupVelocity.heisenberg` : `d/dt (U† P_d U) = U† K_d U`.
- `GroupVelocity.abs_velocity_le`, `GroupVelocity.velocity_psiStar` : `|v| ≤ 1`, attained by
  `ψ*`.
- `GroupVelocity.velocities_PsiStar3D` : `Ψ*` moves at `(1, 1, 1)`.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality SpectralExtremal NearMaxTension
open LiebRobinson PathGraph3DNRS CubeSpectrum
open scoped Matrix

namespace GroupVelocity

variable {d : ℕ}

/-! ## 1. Dispersion relation and group velocity -/

/-- Dispersion relation of transport: energy of the plane wave of angle `θ`. -/
def dispersion (d : ℕ) (θ : ℝ) : ℝ := 2 * Real.cos θ / rho d

/-- Group velocity `v(θ) = −ε'(θ)`, in sites per unit of time. -/
def groupVelocity (d : ℕ) (θ : ℝ) : ℝ := 2 * Real.sin θ / rho d

theorem hasDerivAt_dispersion (θ : ℝ) :
    HasDerivAt (dispersion d) (-groupVelocity d θ) θ := by
  unfold dispersion groupVelocity
  convert ((Real.hasDerivAt_cos θ).const_mul 2).div_const (rho d) using 1
  ring

/-- The sine modes of `D6` are eigenvectors of `T_d`, with energy `ε(θ_k)`. -/
theorem Td_mulVec_sineMode (hd : 1 ≤ d) (k : Fin d) :
    (Td d).mulVec (sineMode d k) =
      fun i => (dispersion d (modeAngle d k) : ℂ) * sineMode d k i := by
  have hA := Ad_sineMode hd k
  funext i
  have hi := congrFun hA i
  simp only [Matrix.mulVec, dotProduct, Td] at hi ⊢
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, hi, dispersion]
  push_cast
  ring

theorem dispersion_centre : dispersion d (Real.pi / 2) = 0 := by
  simp [dispersion]

theorem groupVelocity_le (hd : 2 ≤ d) (θ : ℝ) : groupVelocity d θ ≤ 2 / rho d := by
  have hρ := rho_pos d hd
  unfold groupVelocity
  gcongr
  linarith [Real.sin_le_one θ]

theorem groupVelocity_eq_max_iff (hd : 2 ≤ d) (θ : ℝ) :
    groupVelocity d θ = 2 / rho d ↔ Real.sin θ = 1 := by
  have hρ := (rho_pos d hd).ne'
  unfold groupVelocity
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h, mul_one]

theorem groupVelocity_centre : groupVelocity d (Real.pi / 2) = 2 / rho d := by
  simp [groupVelocity]

/-! ## 2. The Heisenberg equation for position -/

/-- The adjoint evolution `exp(i t T_d)`. -/
def W (d : ℕ) (t : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  NormedSpace.exp ((Complex.I * t) • Td d)

theorem U_conjTranspose (t : ℝ) : (U d t)ᴴ = W d t := by
  rw [U, W, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, (Td_isHermitian d).eq]
  congr 2
  simp [Complex.conj_ofReal]

/-- **Heisenberg equation.** `d/dt (U(t)† P_d U(t)) = U(t)† K_d U(t)`, with
`K_d = i[T_d, P_d]`: the tension is the rate of change of position. -/
theorem heisenberg (t : ℝ) :
    HasDerivAt (fun s : ℝ => (U d s)ᴴ * Pd d * U d s) ((U d t)ᴴ * Kmat d * U d t) t := by
  let _ : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  set B : Matrix (Fin d) (Fin d) ℂ := Complex.I • Td d
  set A : Matrix (Fin d) (Fin d) ℂ := (-Complex.I) • Td d
  have hW : ∀ s : ℝ, W d s = NormedSpace.exp ((s : ℂ) • B) := fun s => by
    rw [W, smul_smul, mul_comm]
  have hU : ∀ s : ℝ, U d s = NormedSpace.exp ((s : ℂ) • A) := fun s => by
    rw [U, smul_smul]
    congr 2
    ring
  have dW : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • B))
      (NormedSpace.exp ((t : ℂ) • B) * B) t := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) B t
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
    exact h
  have dU : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A))
      (A * NormedSpace.exp ((t : ℂ) • A)) t := by
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
    exact h
  have h := (dW.mul (hasDerivAt_const t (Pd d))).mul dU
  have hf : (fun s : ℝ => (U d s)ᴴ * Pd d * U d s) =
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • B)) * (fun _ : ℝ => Pd d) *
        (fun s : ℝ => NormedSpace.exp ((s : ℂ) • A)) := by
    funext s
    rw [Pi.mul_apply, Pi.mul_apply, U_conjTranspose, hW, hU]
  rw [hf]
  refine h.congr_deriv ?_
  rw [U_conjTranspose, hW, hU, Kmat]
  simp only [Pi.mul_apply, mul_zero, add_zero, B, A, Matrix.mul_assoc, smul_mul_assoc,
    mul_smul_comm, neg_smul, neg_mul, mul_neg, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

/-! ## 3. Velocity: one site per unit of time, reached at `ψ*` -/

/-- Velocity of a state, in sites per unit of time: `((d−1)/2)·⟨K_d⟩`. -/
def velocity (d : ℕ) (ψ : Hd d) : ℝ := ((d : ℝ) - 1) / 2 * tension d ψ

theorem abs_tension_le (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) :
    |tension d ψ| ≤ 2 / ((d : ℝ) - 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Hd d) := inferInstance
  have hle := expectation_le_specRadius (KdOp d) (KdOp_isSymmetric d) ψ hψ
  rw [specRadius_KdOp_eq_step d hd] at hle
  exact (Complex.abs_re_le_norm _).trans hle

/-- **Speed limit.** No unit state moves faster than one site per unit of time. -/
theorem abs_velocity_le (hd : 2 ≤ d) (ψ : Hd d) (hψ : ‖ψ‖ = 1) : |velocity d ψ| ≤ 1 := by
  have h1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [velocity, abs_mul, abs_of_pos (by positivity)]
  calc ((d : ℝ) - 1) / 2 * |tension d ψ| ≤ ((d : ℝ) - 1) / 2 * (2 / ((d : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (abs_tension_le hd ψ hψ) (by positivity)
    _ = 1 := by field_simp

/-- **`ψ*` moves at the speed limit**, the slope of the light cone of `D37f`. -/
theorem velocity_psiStar (hd : 2 ≤ d) : velocity d (psiStar d) = 1 := by
  have h1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [velocity, tension_psiStar hd]
  field_simp

/-- **Velocity of the phase modes.** The velocity operator `((d−1)/2)·K_d` acts on the phase
mode `k` of `D6` as the group velocity at `π/2 − θ_k`: the carrier `(−i)^j` shifts the
angle by `π/2`. For `k = 0` (`ψ*`) this is `v(π/2 − π/(d+1)) = 1`. -/
theorem velocity_phaseMode (hd : 2 ≤ d) (k : Fin d) :
    ((((d : ℝ) - 1) / 2 : ℝ) : ℂ) • (Kmat d).mulVec (phaseMode d k) =
      fun i => (groupVelocity d (Real.pi / 2 - modeAngle d k) : ℂ) * phaseMode d k i := by
  have h1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1' : ((d : ℂ) - 1) ≠ 0 := by exact_mod_cast h1
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  rw [Kmat_mulVec_phaseMode hd k]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, groupVelocity, Real.sin_pi_div_two_sub]
  push_cast
  field_simp

/-! ## 4. The cube: one speed limit per axis -/

section Cubo

variable {dx dy dz : ℕ}

/-- Velocity along `x`, in sites per unit of time. -/
def velocityX (Φ : H3D dx dy dz) : ℝ :=
  ((dx : ℝ) - 1) / 2 * tensionG (TX dx dy dz) (PX dx dy dz) Φ
/-- Velocity along `y`. -/
def velocityY (Φ : H3D dx dy dz) : ℝ :=
  ((dy : ℝ) - 1) / 2 * tensionG (TY dx dy dz) (PY dx dy dz) Φ
/-- Velocity along `z`. -/
def velocityZ (Φ : H3D dx dy dz) : ℝ :=
  ((dz : ℝ) - 1) / 2 * tensionG (TZ dx dy dz) (PZ dx dy dz) Φ

theorem mul_tension_le {a : ℕ} (ha : 2 ≤ a) {x n : ℝ} (hx : x ≤ 2 / ((a : ℝ) - 1) * n) :
    ((a : ℝ) - 1) / 2 * x ≤ n := by
  have h1 : (0 : ℝ) < (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  calc ((a : ℝ) - 1) / 2 * x ≤ ((a : ℝ) - 1) / 2 * (2 / ((a : ℝ) - 1) * n) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = n := by field_simp

/-- **One speed limit per axis.** Along each axis, no state moves faster than one site per
unit of time (`‖Φ‖ = 1`). -/
theorem velocities_le (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (Φ : H3D dx dy dz)
    (hΦ : ‖Φ‖ = 1) : velocityX Φ ≤ 1 ∧ velocityY Φ ≤ 1 ∧ velocityZ Φ ≤ 1 := by
  have bx := tension_lift_le hx (eX dx dy dz) Φ
  have by' := tension_lift_le hy (eY dx dy dz) Φ
  have bz := tension_lift_le hz (eZ dx dy dz) Φ
  rw [hΦ, one_pow, mul_one] at bx by' bz
  refine ⟨?_, ?_, ?_⟩
  · unfold velocityX
    exact mul_tension_le hx (n := 1) (by simpa [tensionG, TX, PX] using bx)
  · unfold velocityY
    exact mul_tension_le hy (n := 1) (by simpa [tensionG, TY, PY] using by')
  · unfold velocityZ
    exact mul_tension_le hz (n := 1) (by simpa [tensionG, TZ, PZ] using bz)

theorem mul_tension_eq {a : ℕ} (ha : 2 ≤ a) : ((a : ℝ) - 1) / 2 * (2 / ((a : ℝ) - 1)) = 1 := by
  have h1 : (a : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  field_simp

/-- **`Ψ*` reaches the limit on the three axes at once**: its velocity is `(1, 1, 1)`. -/
theorem velocities_PsiStar3D (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    velocityX (PsiStar3D dx dy dz) = 1 ∧ velocityY (PsiStar3D dx dy dz) = 1 ∧
      velocityZ (PsiStar3D dx dy dz) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [velocityX, PsiStar3D_eq_eX, TX, PX,
      (stats_axis (norm_rest hy hz) hx (eX dx dy dz)).2.2.2, mul_tension_eq hx]
  · rw [velocityY, PsiStar3D_eq_eY, TY, PY,
      (stats_axis (norm_rest hx hz) hy (eY dx dy dz)).2.2.2, mul_tension_eq hy]
  · rw [velocityZ, PsiStar3D_eq_eZ, TZ, PZ,
      (stats_axis (norm_rest hx hy) hz (eZ dx dy dz)).2.2.2, mul_tension_eq hz]

/-- **Anisotropy.** Along the diagonal, `Ψ*` moves with squared Euclidean speed `3`, while each
axis alone is bounded by `1`: the lattice speed limit is a cube, not a sphere. -/
theorem speed_sq_PsiStar3D (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    velocityX (PsiStar3D dx dy dz) ^ 2 + velocityY (PsiStar3D dx dy dz) ^ 2 +
      velocityZ (PsiStar3D dx dy dz) ^ 2 = 3 := by
  obtain ⟨h1, h2, h3⟩ := velocities_PsiStar3D hx hy hz
  rw [h1, h2, h3]
  norm_num

end Cubo

end GroupVelocity

end

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D49j_RobertsonDeterminantSplitAxis

/-!
# D49k — det|NRS³ on canonical axes

Canonical axes: the fluctuation vectors of different axes are orthogonal, the three axes `x`, `y`,
`z` meeting at one vertex. Then the covariance matrix `Σ` of `(T_x, T_y, T_z, P_x, P_y, P_z)` is
block diagonal like `Ω` (`D49b`), one `2 × 2` block per axis, and each block contributes its own
defect `g_i` (the Gram defect of the axis) and its own tension `ω_i`:

  `det Σ = (g_x + ω_x²)(g_y + ω_y²)(g_z + ω_z²)`,  `|det Ω| = ω_x² ω_y² ω_z²`,

  `det Σ / |det Ω| = (1 + g_x/ω_x²)(1 + g_y/ω_y²)(1 + g_z/ω_z²)`.

In the band every `g_i` is positive (`D49e`), so the ratio is a product of three factors larger
than `1`: det|NRS³ is strict on every box. No product structure of the state is assumed, only
orthogonal axes.

## Main results

- `CanonicalAxes.covMatrix_canonical` : `Σ` is block diagonal on canonical axes.
- `CanonicalAxes.det_covMatrix_canonical` : `det Σ = Π (g_i + ω_i²)`.
- `CanonicalAxes.det_ratio_canonical` : `det Σ = Π (1 + g_i/ω_i²) · |det Ω|`.
- `CanonicalAxes.robertson_det_canonical_strict` : strict in the band.
-/

@[expose] public noncomputable section

open Matrix TransportPosition NearMaxTension GroupVelocity PathGraph3DNRS CauchyGram
open RobertsonDeterminant RobertsonDeterminant3D AxisDefectEntangled VelocityBand
open DeterminantEqualityRelation SpectralExtremal

namespace CanonicalAxes

variable {dx dy dz : ℕ} {Φ : H3D dx dy dz}

/-- The pair `(T_i, P_i)` of axis `i`. -/
def famAxis (dx dy dz : ℕ) (i : Fin 3) (s : Fin 2) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  pairs dx dy dz (s, i)

/-- The Gram defect of axis `i`. -/
def defect (Φ : H3D dx dy dz) (i : Fin 3) : ℝ := gramDefectC (fluct Φ (0, i)) (fluct Φ (1, i))

/-- One block: `det Σ_i = g_i + ω_i²`. -/
theorem det_block (Φ : H3D dx dy dz) (i : Fin 3) :
    (covMatrix (famAxis dx dy dz i) Φ).det = defect Φ i + omega Φ i ^ 2 := by
  set u := fluct Φ (0, i)
  set v := fluct Φ (1, i)
  have hvu : inner ℂ v u = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm v u).symm
  have huu : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hvv : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [det_fin_two]
  simp only [covMatrix, covarianceG, of_apply, famAxis]
  change (inner ℂ u u).re * (inner ℂ v v).re - (inner ℂ u v).re * (inner ℂ v u).re = _
  rw [hvu, Complex.conj_re, huu, hvv, defect, gramDefectC, varianceC, varianceC,
    Complex.sq_norm, Complex.normSq_apply]
  change _ = _ - _ + ((inner ℂ u v).im) ^ 2
  ring

variable (horth : ∀ s t (i j : Fin 3), i ≠ j → inner ℂ (fluct Φ (s, i)) (fluct Φ (t, j)) = 0)
include horth

/-- **On canonical axes `Σ` is block diagonal**, one `2 × 2` block per axis. -/
theorem covMatrix_canonical :
    covMatrix (pairs dx dy dz) Φ = blockDiagonal fun i => covMatrix (famAxis dx dy dz i) Φ := by
  ext ⟨s, i⟩ ⟨t, j⟩
  rw [blockDiagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · have h0 := horth s t i j h
    simp only [fluct] at h0
    simp [covMatrix, covarianceG, h0]

/-- **`det Σ = (g_x + ω_x²)(g_y + ω_y²)(g_z + ω_z²)`** on canonical axes. -/
theorem det_covMatrix_canonical :
    (covMatrix (pairs dx dy dz) Φ).det =
      (defect Φ 0 + omega Φ 0 ^ 2) * (defect Φ 1 + omega Φ 1 ^ 2) *
        (defect Φ 2 + omega Φ 2 ^ 2) := by
  rw [covMatrix_canonical horth, det_blockDiagonal, Fin.prod_univ_three, det_block, det_block,
    det_block]

/-- **The ratio on canonical axes**: `det Σ = Π (1 + g_i/ω_i²) · |det Ω|`. -/
theorem det_ratio_canonical (h0 : omega Φ 0 ≠ 0) (h1 : omega Φ 1 ≠ 0) (h2 : omega Φ 2 ≠ 0) :
    (covMatrix (pairs dx dy dz) Φ).det =
      (1 + defect Φ 0 / omega Φ 0 ^ 2) * (1 + defect Φ 1 / omega Φ 1 ^ 2) *
        (1 + defect Φ 2 / omega Φ 2 ^ 2) * |(imMatrix (pairs dx dy dz) Φ).det| := by
  rw [det_covMatrix_canonical horth, abs_det_imMatrix_pairs]
  field_simp
  ring

/-- **det|NRS³ is strict on canonical axes in the band**: three positive defects. -/
theorem robertson_det_canonical_strict (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    (hΦ : ‖Φ‖ = 1) (hbx : |velocityX Φ| ∈ Ϙ dx) (hby : |velocityY Φ| ∈ Ϙ dy)
    (hbz : |velocityZ Φ| ∈ Ϙ dz) :
    |(imMatrix (pairs dx dy dz) Φ).det| < (covMatrix (pairs dx dy dz) Φ).det := by
  have g0 : 0 < defect Φ 0 := gramDefect_pos_of_band hx (eX dx dy dz) hΦ hbx
  have g1 : 0 < defect Φ 1 := gramDefect_pos_of_band hy (eY dx dy dz) hΦ hby
  have g2 : 0 < defect Φ 2 := gramDefect_pos_of_band hz (eZ dx dy dz) hΦ hbz
  rw [det_covMatrix_canonical horth, abs_det_imMatrix_pairs]
  have a0 := sq_nonneg (omega Φ 0)
  have a1 := sq_nonneg (omega Φ 1)
  have a2 := sq_nonneg (omega Φ 2)
  have h1 : omega Φ 0 ^ 2 * omega Φ 1 ^ 2 <
      (defect Φ 0 + omega Φ 0 ^ 2) * (defect Φ 1 + omega Φ 1 ^ 2) :=
    mul_lt_mul'' (by linarith) (by linarith) a0 a1
  have h2 := mul_lt_mul'' h1 (show omega Φ 2 ^ 2 < defect Φ 2 + omega Φ 2 ^ 2 by linarith)
    (by positivity) a2
  calc (omega Φ 0 * omega Φ 1 * omega Φ 2) ^ 2
      = omega Φ 0 ^ 2 * omega Φ 1 ^ 2 * omega Φ 2 ^ 2 := by ring
    _ < _ := h2

end CanonicalAxes

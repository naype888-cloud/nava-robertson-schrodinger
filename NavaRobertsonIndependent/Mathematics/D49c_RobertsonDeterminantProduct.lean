/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D49b_RobertsonDeterminant3D
public import NavaRobertsonIndependent.Mathematics.D37d_CubePythagoras

/-!
# D49c — det|NRS³ on product states: the defects multiply

For a product state `Φ = u ⊗ v ⊗ w` of the cube (`prod3`, unit factors) the fluctuation vectors
of different axes are orthogonal (`D37d`), so the covariance matrix `Σ` of the six observables
is block diagonal like `Ω` (`D49b`). Each block is the `2 × 2` covariance of `(T_d, P_d)` on its
axis, of determinant `s + t²/4`, with `s` the Robertson–Schrödinger surplus (`D23b`) and `t` the
tension of that factor. Hence

  `det Σ = (s_x + t_x²/4)(s_y + t_y²/4)(s_z + t_z²/4)`,  `|det Ω| = (t_x t_y t_z / 8)²`,

and a positive surplus on each of the three axes makes `det|NRS³` strict. At the state of the
cube `Ψ* = ψ* ⊗ ψ* ⊗ ψ*` every block is `C_Nava(d)² t²/4`, so

  `det Σ = C_Nava(dx)² C_Nava(dy)² C_Nava(dz)² · (t_x t_y t_z / 8)²`,

strictly above the bound on every box with at least `4` positions on each of `x`, `y`, `z`.

## Main results

- `RobertsonDeterminantProduct.covMatrix_prod3` : `Σ` is block diagonal on product states.
- `RobertsonDeterminantProduct.det_covMatrix_prod3` : `det Σ = Π (s_i + t_i²/4)`.
- `RobertsonDeterminantProduct.robertson_det_prod3_strict` : positive surplus on the three
  axes gives `(t_x t_y t_z / 8)² < det Σ`.
- `RobertsonDeterminantProduct.det_covMatrix_PsiStar3D` : at `Ψ*`, the ratio is
  `C_Nava(dx)² C_Nava(dy)² C_Nava(dz)²`.
- `RobertsonDeterminantProduct.robertson_det_PsiStar3D_strict` : strict for `dx, dy, dz ≥ 4`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition SpectralExtremal NRSInequality NearMaxTension PathGraph3DNRS
open RobertsonDeterminant RobertsonDeterminant3D CubePythagoras CubeSpectrum Gnomon

namespace RobertsonDeterminantProduct

/-- The pair `(T_d, P_d)` of one axis. -/
def pair (d : ℕ) : Fin 2 → Hd d →ₗ[ℂ] Hd d := ![TdOp d, PdOp d]

theorem pair_isSymmetric (d : ℕ) (a : Fin 2) : (pair d a).IsSymmetric := by
  fin_cases a
  exacts [TdOp_isSymmetric d, PdOp_isSymmetric d]

theorem pair_eq (d : ℕ) (a : Fin 2) : pair d a = Matrix.toEuclideanLin (![Td d, Pd d] a) := by
  fin_cases a <;> rfl

/-- The `2 × 2` covariance of `(T_d, P_d)` has determinant `s + t²/4`. -/
theorem det_covMatrix_pair (d : ℕ) (ψ : Hd d) :
    (covMatrix (pair d) ψ).det = surplus d ψ + tension d ψ ^ 2 / 4 := by
  rw [det_fin_two, surplus_eq]
  simp only [covMatrix, of_apply, pair, covarianceG, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hn (x : Hd d) : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [← inner_conj_symm (centeredG (PdOp d) ψ) (centeredG (TdOp d) ψ), Complex.conj_re, hn, hn]
  unfold variance covariance
  change _ = ‖centeredG (TdOp d) ψ‖ ^ 2 * ‖centeredG (PdOp d) ψ‖ ^ 2 -
    ((inner ℂ (centeredG (TdOp d) ψ) (centeredG (PdOp d) ψ)).re ^ 2 + tension d ψ ^ 2 / 4) +
      tension d ψ ^ 2 / 4
  ring

variable {dx dy dz : ℕ} {u : Hd dx} {v : Hd dy} {w : Hd dz}

theorem centered_pairs_x (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (a : Fin 2) :
    centeredG (pairs dx dy dz (a, 0)) (prod3 u v w) = prod3 (centeredG (pair dx a) u) v w := by
  rw [show pairs dx dy dz (a, 0) = Matrix.toEuclideanLin (liftAlong (eX dx dy dz)
    (![Td dx, Pd dx] a)) from rfl, pair_eq, prod3_eq_eX,
    centeredG_lift _ (norm_prodAlong_eq_one _ hv hw), ← prod3_eq_eX]

theorem centered_pairs_y (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (a : Fin 2) :
    centeredG (pairs dx dy dz (a, 1)) (prod3 u v w) = prod3 u (centeredG (pair dy a) v) w := by
  rw [show pairs dx dy dz (a, 1) = Matrix.toEuclideanLin (liftAlong (eY dx dy dz)
    (![Td dy, Pd dy] a)) from rfl, pair_eq, prod3_eq_eY,
    centeredG_lift _ (norm_prodAlong_eq_one _ hu hw), ← prod3_eq_eY]

theorem centered_pairs_z (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a : Fin 2) :
    centeredG (pairs dx dy dz (a, 2)) (prod3 u v w) = prod3 u v (centeredG (pair dz a) w) := by
  rw [show pairs dx dy dz (a, 2) = Matrix.toEuclideanLin (liftAlong (eZ dx dy dz)
    (![Td dz, Pd dz] a)) from rfl, pair_eq, prod3_eq_eZ,
    centeredG_lift _ (norm_prodAlong_eq_one _ hu hv), ← prod3_eq_eZ]

variable (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
include hu hv hw

/-- On a product state `Σ` is block diagonal, one `2 × 2` block per axis. -/
theorem covMatrix_prod3 :
    covMatrix (pairs dx dy dz) (prod3 u v w) =
      blockDiagonal ![covMatrix (pair dx) u, covMatrix (pair dy) v, covMatrix (pair dz) w] := by
  have ul a := inner_self_centeredG (pair_isSymmetric dx a) hu
  have ur a := inner_centeredG_self (pair_isSymmetric dx a) hu
  have vl a := inner_self_centeredG (pair_isSymmetric dy a) hv
  have vr a := inner_centeredG_self (pair_isSymmetric dy a) hv
  have wl a := inner_self_centeredG (pair_isSymmetric dz a) hw
  have wr a := inner_centeredG_self (pair_isSymmetric dz a) hw
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [covMatrix, of_apply, blockDiagonal_apply, covarianceG]
  fin_cases i <;> fin_cases j <;>
    simp [centered_pairs_x hv hw, centered_pairs_y hu hw, centered_pairs_z hu hv, inner_prod3,
      hu, hv, hw, ul, ur, vl, vr, wl, wr]

/-- `det Σ = (s_x + t_x²/4)(s_y + t_y²/4)(s_z + t_z²/4)` on product states. -/
theorem det_covMatrix_prod3 :
    (covMatrix (pairs dx dy dz) (prod3 u v w)).det =
      (surplus dx u + tension dx u ^ 2 / 4) * (surplus dy v + tension dy v ^ 2 / 4) *
        (surplus dz w + tension dz w ^ 2 / 4) := by
  rw [covMatrix_prod3 hu hv hw, det_blockDiagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, det_covMatrix_pair]

/-- The tensions of the cube at a product state are those of its factors. -/
theorem tensions_prod3 :
    tensionG (TX dx dy dz) (PX dx dy dz) (prod3 u v w) = tension dx u ∧
      tensionG (TY dx dy dz) (PY dx dy dz) (prod3 u v w) = tension dy v ∧
      tensionG (TZ dx dy dz) (PZ dx dy dz) (prod3 u v w) = tension dz w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [prod3_eq_eX]; exact tensionG_lift _ (norm_prodAlong_eq_one _ hv hw) _ _ _
  · rw [prod3_eq_eY]; exact tensionG_lift _ (norm_prodAlong_eq_one _ hu hw) _ _ _
  · rw [prod3_eq_eZ]; exact tensionG_lift _ (norm_prodAlong_eq_one _ hu hv) _ _ _

/-- **det|NRS³ strict on product states.** A positive surplus on each of the three axes makes
the bound strict. -/
theorem robertson_det_prod3_strict (hsx : 0 < surplus dx u) (hsy : 0 < surplus dy v)
    (hsz : 0 < surplus dz w) :
    ((tensionG (TX dx dy dz) (PX dx dy dz) (prod3 u v w) *
        tensionG (TY dx dy dz) (PY dx dy dz) (prod3 u v w) *
          tensionG (TZ dx dy dz) (PZ dx dy dz) (prod3 u v w)) / 8) ^ 2 <
      (covMatrix (pairs dx dy dz) (prod3 u v w)).det := by
  obtain ⟨hx, hy, hz⟩ := tensions_prod3 hu hv hw
  rw [hx, hy, hz, det_covMatrix_prod3 hu hv hw]
  have ha := sq_nonneg (tension dx u)
  have hb := sq_nonneg (tension dy v)
  have hc := sq_nonneg (tension dz w)
  have h1 : tension dx u ^ 2 / 4 * (tension dy v ^ 2 / 4) <
      (surplus dx u + tension dx u ^ 2 / 4) * (surplus dy v + tension dy v ^ 2 / 4) :=
    mul_lt_mul'' (by linarith) (by linarith) (by positivity) (by positivity)
  have h2 := mul_lt_mul'' h1 (show tension dz w ^ 2 / 4 < surplus dz w + tension dz w ^ 2 / 4
    by linarith) (by positivity) (by positivity)
  calc _ = tension dx u ^ 2 / 4 * (tension dy v ^ 2 / 4) * (tension dz w ^ 2 / 4) := by ring
    _ < _ := h2

omit hu hv hw

/-- One block at `ψ*`: `C_Nava(d)² · t²/4`. -/
theorem block_psiStar {d : ℕ} (hd : 2 ≤ d) :
    surplus d (psiStar d) + tension d (psiStar d) ^ 2 / 4 =
      CoherenceConstant d ^ 2 * (tension d (psiStar d) ^ 2 / 4) := by
  have h := surplus_eq d (psiStar d)
  rw [variance_mul_variance hd, covariance_eq_zero hd] at h
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [h, CoherenceConstant_eq_one_add_geometricGap, tension_psiStar hd,
    commutatorConstant_half_sq hd]
  field_simp
  ring

/-- **det|NRS³ at the state of the cube.** `det Σ = C_Nava(dx)² C_Nava(dy)² C_Nava(dz)² ·
(t_x t_y t_z / 8)²`. -/
theorem det_covMatrix_PsiStar3D (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    (covMatrix (pairs dx dy dz) (PsiStar3D dx dy dz)).det =
      (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 *
        ((tensionG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) *
          tensionG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) *
            tensionG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz)) / 8) ^ 2 := by
  have hu := norm_psiStar hx
  have hv := norm_psiStar hy
  have hw := norm_psiStar hz
  obtain ⟨tx, ty, tz⟩ := tensions_prod3 hu hv hw
  rw [PsiStar3D_eq_prod3, det_covMatrix_prod3 hu hv hw, tx, ty, tz, block_psiStar hx,
    block_psiStar hy, block_psiStar hz]
  ring

/-- **Strict on every box with `4` or more positions on each of `x`, `y`, `z`.** -/
theorem robertson_det_PsiStar3D_strict (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    ((tensionG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) *
        tensionG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) *
          tensionG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz)) / 8) ^ 2 <
      (covMatrix (pairs dx dy dz) (PsiStar3D dx dy dz)).det := by
  have hs (d : ℕ) (hd : 4 ≤ d) : 0 < surplus d (psiStar d) := by
    rw [surplus_eq]
    linarith [strict_inequality hd, tension_psiStar (d := d) (by omega),
      commutatorConstant_half_sq (d := d) (by omega), show tension d (psiStar d) ^ 2 / 4 =
        (commutatorConstant d / 2) ^ 2 by
          have : (d : ℝ) - 1 ≠ 0 := by
            have : (4 : ℝ) ≤ d := by exact_mod_cast hd
            linarith
          rw [tension_psiStar (by omega), commutatorConstant_half_sq (by omega)]
          field_simp
          ring]
  rw [PsiStar3D_eq_prod3]
  exact robertson_det_prod3_strict (norm_psiStar (by omega)) (norm_psiStar (by omega))
    (norm_psiStar (by omega)) (hs dx hx) (hs dy hy) (hs dz hz)

end RobertsonDeterminantProduct

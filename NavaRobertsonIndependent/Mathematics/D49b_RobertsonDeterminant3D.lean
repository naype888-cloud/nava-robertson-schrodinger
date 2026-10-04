/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D49_RobertsonDeterminant

/-!
# D49b — Robertson 1934 on the three axes of the cube

On the cube `Site3D dx dy dz` of `D37` the six observables are the pairs `(T_x, P_x)`,
`(T_y, P_y)`, `(T_z, P_z)`, one per axis. Operators on different axes commute (`D37`), so
`Ω_jk = Im ⟨c_j, c_k⟩` of `D49` is block diagonal, one `2 × 2` block per axis, and
`|det Ω| = ω_x² ω_y² ω_z²`. With `⟨i[T, P]⟩ = −2 ω` this is, for every state `Ψ` and every box,

  `det Σ ≥ (⟨i[T_x, P_x]⟩ ⟨i[T_y, P_y]⟩ ⟨i[T_z, P_z]⟩ / 8)²`,

the volume of the six-dimensional dispersion bounded by the product of the three tensions.
Each factor is the conjugate pair of its axis; no axis can be dropped.

## Main results

- `RobertsonDeterminant3D.commutator_pairs` : observables of different axes commute.
- `RobertsonDeterminant3D.imMatrix_pairs` : `Ω` is block diagonal, one block per axis.
- `RobertsonDeterminant3D.abs_det_imMatrix_pairs` : `|det Ω| = (ω_x ω_y ω_z)²`.
- `RobertsonDeterminant3D.robertson_det_cube` : `(t_x t_y t_z / 8)² ≤ det Σ`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition SpectralExtremal PathGraph3DNRS RobertsonDeterminant

namespace RobertsonDeterminant3D

/-- A lifted hermitian matrix is hermitian. -/
theorem liftAlong_isHermitian {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq α] [DecidableEq β] (e : ι ≃ α × β) {A : Matrix α α ℂ}
    (hA : A.IsHermitian) : (liftAlong e A).IsHermitian := by
  ext p q
  rw [conjTranspose_apply]
  simp only [liftAlong, of_apply, star_mul', hA.apply]
  split_ifs with h₁ h₂ h₂ <;> simp_all [eq_comm]

/-- `(inner y x).im = −(inner x y).im`. -/
theorem inner_im_swap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) :
    (inner ℂ y x).im = -(inner ℂ x y).im := by
  rw [← inner_conj_symm y x, Complex.conj_im]

variable (dx dy dz : ℕ)

/-- The six observables: `(0, i)` is the transport of axis `i`, `(1, i)` its position. -/
def pairs (p : Fin 2 × Fin 3) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  ![Matrix.toEuclideanLin (liftAlong (eX dx dy dz) (![Td dx, Pd dx] p.1)),
    Matrix.toEuclideanLin (liftAlong (eY dx dy dz) (![Td dy, Pd dy] p.1)),
    Matrix.toEuclideanLin (liftAlong (eZ dx dy dz) (![Td dz, Pd dz] p.1))] p.2

theorem pairs_isSymmetric (p : Fin 2 × Fin 3) : (pairs dx dy dz p).IsSymmetric := by
  obtain ⟨a, i⟩ := p
  fin_cases a <;> fin_cases i <;>
    first
    | exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian _ (Td_isHermitian _))
    | exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian _ (Pd_isHermitian _))

/-- Observables of different axes commute. -/
theorem commutator_pairs {a b : Fin 2} {i j : Fin 3} (h : i ≠ j) :
    opCommutator (pairs dx dy dz (a, i)) (pairs dx dy dz (b, j)) = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h
  · exact commutator_eq_zero_of_mul_comm (liftAlong_xy_comm dx dy dz _ _)
  · exact commutator_eq_zero_of_mul_comm (liftAlong_xz_comm dx dy dz _ _)
  · exact commutator_eq_zero_of_mul_comm (liftAlong_xy_comm dx dy dz _ _).symm
  · exact commutator_eq_zero_of_mul_comm (liftAlong_yz_comm dx dy dz _ _)
  · exact commutator_eq_zero_of_mul_comm (liftAlong_xz_comm dx dy dz _ _).symm
  · exact commutator_eq_zero_of_mul_comm (liftAlong_yz_comm dx dy dz _ _).symm

variable {dx dy dz} (Ψ : H3D dx dy dz)

/-- `ω_i = Im ⟨c_{T_i}, c_{P_i}⟩`, the off-diagonal entry of the block of axis `i`. -/
def omega (i : Fin 3) : ℝ :=
  (inner ℂ (centeredG (pairs dx dy dz (0, i)) Ψ) (centeredG (pairs dx dy dz (1, i)) Ψ)).im

/-- `Ω` is block diagonal, with the block `!![0, ω_i; −ω_i, 0]` on axis `i`. -/
theorem imMatrix_pairs :
    imMatrix (pairs dx dy dz) Ψ = blockDiagonal fun i => !![0, omega Ψ i; -omega Ψ i, 0] := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [imMatrix, of_apply, blockDiagonal_apply]
  split_ifs with h
  · subst h
    fin_cases a <;> fin_cases b
    · simp [← Complex.ofReal_pow]
    · rfl
    · simpa [omega] using inner_im_swap _ _
    · simp [← Complex.ofReal_pow]
  · have hs := tensionG_eq (Ψ := Ψ) (pairs_isSymmetric dx dy dz (a, i))
      (pairs_isSymmetric dx dy dz (b, j))
    simp only [tensionG, observableTension, commutator_pairs dx dy dz h, smul_zero,
      LinearMap.zero_apply, inner_zero_right, Complex.zero_re] at hs
    linarith

theorem abs_det_imMatrix_pairs :
    |(imMatrix (pairs dx dy dz) Ψ).det| = (omega Ψ 0 * omega Ψ 1 * omega Ψ 2) ^ 2 := by
  rw [imMatrix_pairs, det_blockDiagonal, Fin.prod_univ_three]
  simp only [det_fin_two_of]
  rw [← abs_of_nonneg (sq_nonneg (omega Ψ 0 * omega Ψ 1 * omega Ψ 2))]
  congr 1
  ring

/-- **Robertson 1934 on the cube.** For every state `Ψ` on every box `dx × dy × dz`, the
determinant of the `6 × 6` covariance matrix of `(T_x, T_y, T_z, P_x, P_y, P_z)` is at least
the square of the product of the three tensions over `8`. -/
theorem robertson_det_cube :
    ((tensionG (TX dx dy dz) (PX dx dy dz) Ψ * tensionG (TY dx dy dz) (PY dx dy dz) Ψ *
        tensionG (TZ dx dy dz) (PZ dx dy dz) Ψ) / 8) ^ 2 ≤
      (covMatrix (pairs dx dy dz) Ψ).det := by
  have ht (i : Fin 3) : tensionG (pairs dx dy dz (0, i)) (pairs dx dy dz (1, i)) Ψ =
      -2 * omega Ψ i :=
    tensionG_eq (pairs_isSymmetric dx dy dz _) (pairs_isSymmetric dx dy dz _)
  have h := robertson_det (pairs dx dy dz) Ψ
  rw [abs_det_imMatrix_pairs] at h
  rw [show TX dx dy dz = pairs dx dy dz (0, 0) from rfl, show PX dx dy dz = pairs dx dy dz (1, 0)
    from rfl, show TY dx dy dz = pairs dx dy dz (0, 1) from rfl,
    show PY dx dy dz = pairs dx dy dz (1, 1) from rfl, show TZ dx dy dz = pairs dx dy dz (0, 2)
    from rfl, show PZ dx dy dz = pairs dx dy dz (1, 2) from rfl, ht, ht, ht]
  convert h using 1
  ring

end RobertsonDeterminant3D

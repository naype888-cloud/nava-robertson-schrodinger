/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module
public import NavaRobertsonIndependent.Mathematics.D51_LocalCurrent
public import Mathlib.LinearAlgebra.Matrix.PosDef
/-!
# D52 — Viscosity on the lattice: the Laplacian of `A_d`

The viscous force on the positions of `T_d` is the Laplacian `L_d = D_d - A_d`, with `D_d` the
diagonal of the degrees. It is Hermitian, constants feel no force (`L_d 1 = 0`), and it shares the
noncommutativity of the transport with the position: since `D_d` is diagonal it commutes with
`P_d`, so `[L_d, P_d] = -ρ_d [T_d, P_d]`. Advection and viscosity bracket with the position by
the same matrix.

## Main results

- `Lap_isHermitian`, `Lap_mulVec_one` : Hermitian, and zero on constants.
- `Ad_eq_rho_smul_Td` : `A_d = ρ_d T_d`.
- `Lap_commutator_Pd` : `[L_d, P_d] = -ρ_d [T_d, P_d]`.
- `Lap_quadratic` : `⟨x, L_d x⟩ = ½ ∑ A_{ij} |x_i - x_j|²`.
- `Lap_posSemidef` : the viscosity dissipates.
-/
@[expose] public noncomputable section
open Matrix
open scoped ComplexOrder
namespace TransportPosition

variable {d : ℕ}

/-- The degree of the position `i` in the path. -/
def degree (d : ℕ) (i : Fin d) : ℂ := ∑ j, Ad d i j

/-- The Laplacian `L_d = D_d - A_d`: the viscosity of the lattice. -/
def Lap (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (degree d) - Ad d

lemma Ad_symm (i j : Fin d) : Ad d i j = Ad d j i := by
  unfold Ad
  by_cases h : MinStep i j
  · simp [h, minStep_symm.mp h]
  · have h' : ¬ MinStep j i := fun h' => h (minStep_symm.mp h')
    simp [h, h']

lemma Ad_isHermitian (d : ℕ) : (Ad d).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  rw [Ad_symm j i]
  unfold Ad
  split_ifs <;> simp

lemma Lap_isHermitian (d : ℕ) : (Lap d).IsHermitian := by
  unfold Lap
  refine IsHermitian.sub ?_ (Ad_isHermitian d)
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  by_cases h : i = j
  · subst h
    simp only [diagonal_apply_eq]
    unfold degree
    rw [star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold Ad
    split_ifs <;> simp
  · simp [diagonal_apply_ne, h, Ne.symm h]

/-- Constants feel no viscous force. -/
lemma Lap_mulVec_one (d : ℕ) : Lap d *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  ext i
  simp [Lap, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, degree]

/-- `A_d = ρ_d T_d`. -/
lemma Ad_eq_rho_smul_Td (hd : 2 ≤ d) : Ad d = (rho d : ℂ) • Td d := by
  have hρ : (rho d : ℂ) ≠ 0 := by exact_mod_cast (rho_pos d hd).ne'
  ext i j
  simp [Td, mul_div_cancel₀ _ hρ]

/-- The position is the diagonal matrix of the coordinates. -/
lemma Pd_eq_diagonal (d : ℕ) : Pd d = Matrix.diagonal fun i => (posCoord d i : ℂ) := by
  ext i j
  simp [Pd, Matrix.diagonal_apply]

/-- **Viscosity and advection bracket with the position by the same matrix**:
`[L_d, P_d] = -ρ_d [T_d, P_d]`. -/
theorem Lap_commutator_Pd (hd : 2 ≤ d) :
    Lap d * Pd d - Pd d * Lap d = -((rho d : ℂ) • (Td d * Pd d - Pd d * Td d)) := by
  have hD : Matrix.diagonal (degree d) * Pd d - Pd d * Matrix.diagonal (degree d) = 0 := by
    rw [Pd_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, sub_eq_zero]
    congr 1
    ext i
    exact mul_comm _ _
  unfold Lap
  rw [Matrix.sub_mul, Matrix.mul_sub, Ad_eq_rho_smul_Td hd, Matrix.smul_mul, Matrix.mul_smul]
  rw [smul_sub, neg_sub]
  have := hD
  rw [sub_eq_zero] at this
  rw [this]
  abel

/-- **The energy of the viscosity is the sum of the squared differences over the links**:
`⟨x, L_d x⟩ = ½ ∑ A_{ij} |x_i - x_j|²`. -/
theorem Lap_quadratic (x : Fin d → ℂ) :
    star x ⬝ᵥ (Lap d *ᵥ x) =
      ∑ i, ∑ j, (Ad d i j / 2) * (star (x i - x j) * (x i - x j)) := by
  have row : ∀ i, (Lap d *ᵥ x) i = ∑ j, Ad d i j * (x i - x j) := by
    intro i
    simp only [Lap, Matrix.mulVec, dotProduct, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib,
      mul_sub]
    congr 1
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rw [degree, Finset.sum_mul]
  have h1 : star x ⬝ᵥ (Lap d *ᵥ x) = ∑ i, ∑ j, Ad d i j * (star (x i) * (x i - x j)) := by
    simp only [dotProduct, Pi.star_apply, row, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∑ i, ∑ j, Ad d i j * (star (x i) * (x i - x j)) =
      ∑ i, ∑ j, Ad d i j * (star (x j) * (x j - x i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Ad_symm j i]
  have h3 : (2 : ℂ) * ∑ i, ∑ j, Ad d i j * (star (x i) * (x i - x j)) =
      ∑ i, ∑ j, Ad d i j * (star (x i - x j) * (x i - x j)) := by
    rw [two_mul]
    nth_rewrite 2 [h2]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [star_sub]
    ring
  rw [h1]
  have : ∑ i, ∑ j, (Ad d i j / 2) * (star (x i - x j) * (x i - x j)) =
      (∑ i, ∑ j, Ad d i j * (star (x i - x j) * (x i - x j))) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, ← h3]
  ring

lemma Ad_nonneg (i j : Fin d) : (0 : ℂ) ≤ Ad d i j := by
  unfold Ad
  split_ifs <;> simp

/-- **The viscosity dissipates**: `L_d` is positive semidefinite. -/
theorem Lap_posSemidef (d : ℕ) : Matrix.PosSemidef (Lap d) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨Lap_isHermitian d, fun x => ?_⟩
  rw [Lap_quadratic]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have h2 : (0 : ℂ) ≤ star (x i - x j) * (x i - x j) := star_mul_self_nonneg _
  have h3 : (0 : ℂ) ≤ Ad d i j / 2 := by
    have := Ad_nonneg (d := d) i j
    exact div_nonneg this (by norm_num)
  exact mul_nonneg h3 h2

end TransportPosition

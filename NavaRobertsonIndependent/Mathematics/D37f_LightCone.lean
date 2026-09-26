/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# D37f — The light cone of transport

`T_d` only connects neighbours (`D3`). Counting time in steps of transport, after `k` steps an
amplitude has moved at most `k` sites, and exactly `k` is reached: the speed limit is one site
per step. On the cube the cone is the octahedron `|Δx| + |Δy| + |Δz| ≤ k`.

## Main results

- `LightCone.pow_apply_eq_zero_of_lt` : powers of a local matrix are local.
- `LightCone.lightCone` : `(T_d^k) i j = 0` for `|i − j| > k`.
- `LightCone.lightCone_edge_ne_zero` : `(T_d^k) i (i + k) = ρ_d^{−k} ≠ 0`.
- `LightCone.lightCone_cube` : `(T_x + T_y + T_z)^k` vanishes beyond lattice distance `k`.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS
open PathGraph3D (Site3D)

namespace LightCone

/-! ## 1. Generic cone for powers of a local matrix -/

theorem pow_apply_eq_zero_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (dist : ι → ι → ℕ)
    (hself : ∀ p, dist p p = 0) (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (M : Matrix ι ι ℂ) (hM : ∀ p q, 1 < dist p q → M p q = 0) :
    ∀ (k : ℕ) (p q : ι), k < dist p q → (M ^ k) p q = 0 := by
  intro k
  induction k with
  | zero =>
    intro p q h
    have hpq : p ≠ q := by rintro rfl; rw [hself] at h; exact absurd h (lt_irrefl 0)
    simp [hpq]
  | succ k ih =>
    intro p q h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge k (dist p l) with hl | hl
    · rw [ih p l hl, zero_mul]
    · have := htri p l q
      rw [hM l q (by omega), mul_zero]

/-! ## 2. The path -/

/-- Distance between sites of the path: `|i − j|`. -/
def distPath {d : ℕ} (i j : Fin d) : ℕ := (i.val - j.val) + (j.val - i.val)

theorem distPath_self {d : ℕ} (i : Fin d) : distPath i i = 0 := by simp [distPath]

theorem distPath_tri {d : ℕ} (a b c : Fin d) :
    distPath a c ≤ distPath a b + distPath b c := by
  unfold distPath; omega

theorem Td_local {d : ℕ} (i j : Fin d) (h : 1 < distPath i j) : Td d i j = 0 := by
  have hnp : ¬ MinStep i j := by
    unfold MinStep distPath at *; omega
  simp [Td, Ad, hnp]

/-- **Light cone on the path.** After `k` steps of transport, nothing connects sites more than
`k` apart. -/
theorem lightCone {d : ℕ} (k : ℕ) (i j : Fin d) (h : k < distPath i j) :
    (Td d ^ k) i j = 0 :=
  pow_apply_eq_zero_of_lt distPath distPath_self distPath_tri (Td d) Td_local k i j h

/-- **No signal outruns the cone.** If `ψ` vanishes on every site within `k` of `i`, then after
`k` steps of transport the amplitude at `i` is still zero. -/
theorem lightCone_state {d : ℕ} (k : ℕ) (ψ : Hd d) (i : Fin d)
    (hψ : ∀ j, distPath i j ≤ k → ψ j = 0) :
    Matrix.toEuclideanLin (Td d ^ k) ψ i = 0 := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases le_or_gt (distPath i j) k with h | h
  · simp [hψ j h]
  · simp [lightCone k i j h]

/-- **The edge of the cone is reached.** For `j = i + k` the amplitude after `k` steps is
`ρ_d^{−k} ≠ 0`: the maximal speed is exactly one site per step. -/
theorem lightCone_edge {d : ℕ} (k : ℕ) (i j : Fin d) (hij : j.val = i.val + k) :
    (Td d ^ k) i j = ((rho d : ℂ)⁻¹) ^ k := by
  induction k generalizing j with
  | zero =>
    have : i = j := Fin.ext (by omega)
    subst this; simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    have hj' : i.val + k < d := by have := j.isLt; omega
    set l : Fin d := ⟨i.val + k, hj'⟩
    rw [Finset.sum_eq_single l]
    · rw [ih l rfl]
      have hpl : MinStep l j := Or.inl (by simp [l]; omega)
      simp [Td, Ad, hpl, pow_succ, div_eq_mul_inv]
    · intro m _ hm
      rcases lt_or_ge k (distPath i m) with h | h
      · rw [lightCone k i m h, zero_mul]
      · have hnp : ¬ MinStep m j := by
          intro hp
          apply hm; apply Fin.ext
          unfold MinStep at hp; unfold distPath at h; simp [l]; omega
        simp [Td, Ad, hnp]
    · intro h; exact absurd (Finset.mem_univ l) h

theorem lightCone_edge_ne_zero {d : ℕ} (hd : 2 ≤ d) (k : ℕ) (i j : Fin d)
    (hij : j.val = i.val + k) : (Td d ^ k) i j ≠ 0 := by
  rw [lightCone_edge k i j hij]
  have hr : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos d hd).ne'
  exact pow_ne_zero _ (inv_ne_zero hr)

/-! ## 3. The cube -/

/-- Lattice distance on the cube: `|Δx| + |Δy| + |Δz|`. -/
def distCube {dx dy dz : ℕ} (p q : Site3D dx dy dz) : ℕ :=
  distPath p.1 q.1 + distPath p.2.1 q.2.1 + distPath p.2.2 q.2.2

theorem distCube_self {dx dy dz : ℕ} (p : Site3D dx dy dz) : distCube p p = 0 := by
  simp [distCube, distPath_self]

theorem distCube_tri {dx dy dz : ℕ} (a b c : Site3D dx dy dz) :
    distCube a c ≤ distCube a b + distCube b c := by
  unfold distCube
  have := distPath_tri a.1 b.1 c.1
  have := distPath_tri a.2.1 b.2.1 c.2.1
  have := distPath_tri a.2.2 b.2.2 c.2.2
  omega

/-- Total transport of the cube: one step along one axis. -/
def T3 (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (Td dx) + liftAlong (eY dx dy dz) (Td dy) +
    liftAlong (eZ dx dy dz) (Td dz)

theorem T3_local {dx dy dz : ℕ} (p q : Site3D dx dy dz) (h : 1 < distCube p q) :
    T3 dx dy dz p q = 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [T3, Matrix.add_apply, liftAlong, Matrix.of_apply, eX, eY, eZ, Equiv.refl_apply,
    Equiv.coe_fn_mk, Prod.mk.injEq]
  unfold distCube at h
  simp only at h
  have ex : (Td dx i i' * if j = j' ∧ k = k' then 1 else 0) = 0 := by
    by_cases hc : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Td_local i i' (by rw [distPath_self, distPath_self] at h; omega), zero_mul]
    · simp [hc]
  have ey : (Td dy j j' * if i = i' ∧ k = k' then 1 else 0) = 0 := by
    by_cases hc : i = i' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Td_local j j' (by rw [distPath_self, distPath_self] at h; omega), zero_mul]
    · simp [hc]
  have ez : (Td dz k k' * if i = i' ∧ j = j' then 1 else 0) = 0 := by
    by_cases hc : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Td_local k k' (by rw [distPath_self, distPath_self] at h; omega), zero_mul]
    · simp [hc]
  rw [ex, ey, ez]; ring

/-- **Light cone on the cube.** After `k` steps of total transport, nothing connects sites at
lattice distance `|Δx| + |Δy| + |Δz| > k`. -/
theorem lightCone_cube {dx dy dz : ℕ} (k : ℕ) (p q : Site3D dx dy dz)
    (h : k < distCube p q) : (T3 dx dy dz ^ k) p q = 0 :=
  pow_apply_eq_zero_of_lt distCube distCube_self distCube_tri (T3 dx dy dz) T3_local k p q h

end LightCone

end

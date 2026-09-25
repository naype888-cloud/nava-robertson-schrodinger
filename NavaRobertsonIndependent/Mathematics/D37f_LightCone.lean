import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# D37f — The light cone of transport between neighbours

`T_d` only connects neighbouring sites (`D3`). Counting time in steps of transport, this is a
**light cone**: after `k` steps an amplitude cannot have moved more than `k` sites, and the
cone is sharp — at exactly `k` sites the amplitude arrives. The maximal speed is exactly one site
per step.

* `pow_apply_eq_zero_of_lt`: generic — if a matrix only connects points at distance `≤ 1` for a
  distance satisfying the triangle inequality, its `k`-th power only connects points at
  distance `≤ k`.
* `cono_de_luz`: on the path, `(T_d^k) i j = 0` whenever `|i − j| > k`.
* `cono_de_luz_estado`: if `ψ` vanishes on every site within `k` of `i`, then `T_d^k ψ` vanishes
  at `i` — no signal outruns the cone.
* `borde_del_cono`: the edge is reached, `(T_d^k) i j = ρ_d^{−k} ≠ 0` for `j = i + k`.
* `cono_de_luz_cubo`: on the cube of `D37`, the total transport `T_x + T_y + T_z` has
  `k`-th power vanishing beyond distance `|Δx| + |Δy| + |Δz| > k`: the cone of the lattice is the
  octahedron of that distance, one axis step per unit of time.
-/

noncomputable section

open TransportePosicion PathGraph3DNRS
open PathGraph3D (Sitio3D)

namespace ConoDeLuz

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
def distCamino {d : ℕ} (i j : Fin d) : ℕ := (i.val - j.val) + (j.val - i.val)

theorem distCamino_self {d : ℕ} (i : Fin d) : distCamino i i = 0 := by simp [distCamino]

theorem distCamino_tri {d : ℕ} (a b c : Fin d) :
    distCamino a c ≤ distCamino a b + distCamino b c := by
  unfold distCamino; omega

theorem Td_local {d : ℕ} (i j : Fin d) (h : 1 < distCamino i j) : Td d i j = 0 := by
  have hnp : ¬ PasoMinimo i j := by
    unfold PasoMinimo distCamino at *; omega
  simp [Td, Ad, hnp]

/-- **Light cone on the path.** After `k` steps of transport, nothing connects sites more than
`k` apart. -/
theorem cono_de_luz {d : ℕ} (k : ℕ) (i j : Fin d) (h : k < distCamino i j) :
    (Td d ^ k) i j = 0 :=
  pow_apply_eq_zero_of_lt distCamino distCamino_self distCamino_tri (Td d) Td_local k i j h

/-- **No signal outruns the cone.** If `ψ` vanishes on every site within `k` of `i`, then after
`k` steps of transport the amplitude at `i` is still zero. -/
theorem cono_de_luz_estado {d : ℕ} (k : ℕ) (ψ : Hd d) (i : Fin d)
    (hψ : ∀ j, distCamino i j ≤ k → ψ j = 0) :
    Matrix.toEuclideanLin (Td d ^ k) ψ i = 0 := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases le_or_gt (distCamino i j) k with h | h
  · simp [hψ j h]
  · simp [cono_de_luz k i j h]

/-- **The edge of the cone is reached.** For `j = i + k` the amplitude after `k` steps is
`ρ_d^{−k} ≠ 0`: the maximal speed is exactly one site per step. -/
theorem borde_del_cono {d : ℕ} (k : ℕ) (i j : Fin d) (hij : j.val = i.val + k) :
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
      have hpl : PasoMinimo l j := Or.inl (by simp [l]; omega)
      simp [Td, Ad, hpl, pow_succ, div_eq_mul_inv]
    · intro m _ hm
      rcases lt_or_ge k (distCamino i m) with h | h
      · rw [cono_de_luz k i m h, zero_mul]
      · have hnp : ¬ PasoMinimo m j := by
          intro hp
          apply hm; apply Fin.ext
          unfold PasoMinimo at hp; unfold distCamino at h; simp [l]; omega
        simp [Td, Ad, hnp]
    · intro h; exact absurd (Finset.mem_univ l) h

theorem borde_del_cono_ne_zero {d : ℕ} (hd : 2 ≤ d) (k : ℕ) (i j : Fin d)
    (hij : j.val = i.val + k) : (Td d ^ k) i j ≠ 0 := by
  rw [borde_del_cono k i j hij]
  have hr : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos d hd).ne'
  exact pow_ne_zero _ (inv_ne_zero hr)

/-! ## 3. The cube -/

/-- Lattice distance on the cube: `|Δx| + |Δy| + |Δz|`. -/
def distCubo {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : ℕ :=
  distCamino p.1 q.1 + distCamino p.2.1 q.2.1 + distCamino p.2.2 q.2.2

theorem distCubo_self {dx dy dz : ℕ} (p : Sitio3D dx dy dz) : distCubo p p = 0 := by
  simp [distCubo, distCamino_self]

theorem distCubo_tri {dx dy dz : ℕ} (a b c : Sitio3D dx dy dz) :
    distCubo a c ≤ distCubo a b + distCubo b c := by
  unfold distCubo
  have := distCamino_tri a.1 b.1 c.1
  have := distCamino_tri a.2.1 b.2.1 c.2.1
  have := distCamino_tri a.2.2 b.2.2 c.2.2
  omega

/-- Total transport of the cube: one step along one axis. -/
def T3 (dx dy dz : ℕ) : Matrix (Sitio3D dx dy dz) (Sitio3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (Td dx) + liftAlong (eY dx dy dz) (Td dy) +
    liftAlong (eZ dx dy dz) (Td dz)

theorem T3_local {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) (h : 1 < distCubo p q) :
    T3 dx dy dz p q = 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only [T3, Matrix.add_apply, liftAlong, Matrix.of_apply, eX, eY, eZ, Equiv.refl_apply,
    Equiv.coe_fn_mk, Prod.mk.injEq]
  unfold distCubo at h
  simp only at h
  have ex : (Td dx i i' * if j = j' ∧ k = k' then 1 else 0) = 0 := by
    by_cases hc : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Td_local i i' (by rw [distCamino_self, distCamino_self] at h; omega), zero_mul]
    · simp [hc]
  have ey : (Td dy j j' * if i = i' ∧ k = k' then 1 else 0) = 0 := by
    by_cases hc : i = i' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Td_local j j' (by rw [distCamino_self, distCamino_self] at h; omega), zero_mul]
    · simp [hc]
  have ez : (Td dz k k' * if i = i' ∧ j = j' then 1 else 0) = 0 := by
    by_cases hc : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Td_local k k' (by rw [distCamino_self, distCamino_self] at h; omega), zero_mul]
    · simp [hc]
  rw [ex, ey, ez]; ring

/-- **Light cone on the cube.** After `k` steps of total transport, nothing connects sites at
lattice distance `|Δx| + |Δy| + |Δz| > k`. -/
theorem cono_de_luz_cubo {dx dy dz : ℕ} (k : ℕ) (p q : Sitio3D dx dy dz)
    (h : k < distCubo p q) : (T3 dx dy dz ^ k) p q = 0 :=
  pow_apply_eq_zero_of_lt distCubo distCubo_self distCubo_tri (T3 dx dy dz) T3_local k p q h

end ConoDeLuz

end

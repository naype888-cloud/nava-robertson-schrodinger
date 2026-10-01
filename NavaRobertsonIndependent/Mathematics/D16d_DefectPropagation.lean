/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37f_LightCone

/-!
# D16d — A local change of transport travels inside the cone

`D16c` describes the excitation of the defect globally, as a change of `b₁`. This module asks
how fast a local change of transport is felt. Replace `T_d` by any `M'` that differs from it
only on the rows of a set `S` of sites.

* After `k` steps, every site `i` with `k ≤ |i − a|` for all `a ∈ S` sees exactly what it saw
  without the change (`pow_row_eq_of_le`, `change_unseen`). No modification of transport is
  felt outside the cone of `D37f`.
* The bound is sharp. An on-site change `ε` at `s = i + k` is unseen at `i` after `k` steps,
  and after `k + 1` steps the amplitude from `i` to `s` differs by `ε ρ_d^{−k} ≠ 0`
  (`onSite_front`). The front moves at one site per step, the speed of `D37f`.

Not here: that a local change of this kind creates a cycle (the bridge to `D16c`), and the
spin and mass of the excitation. The continuous-time version would follow `D37g`.

## Main results

- `DefectPropagation.pow_row_eq_of_le` : the cone of a local change, for any local matrix.
- `DefectPropagation.change_unseen` : on the path, for any state.
- `DefectPropagation.onSite_front` : the front arrives exactly on time.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone

namespace DefectPropagation

/-! ## 1. Generic cone of a local change -/

/-- **The cone of a local change.** `M` is local, and `M'` agrees with `M` outside the rows of
`S`. Row `p` of `M'^k` equals row `p` of `M^k` while `k ≤ dist p a` for every `a ∈ S`. -/
theorem pow_row_eq_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] (dist : ι → ι → ℕ)
    (hself : ∀ p, dist p p = 0) (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (M M' : Matrix ι ι ℂ) (hM : ∀ p q, 1 < dist p q → M p q = 0)
    (S : Set ι) (hrow : ∀ p, p ∉ S → M' p = M p) :
    ∀ (k : ℕ) (p : ι), (∀ a ∈ S, k ≤ dist p a) → (M' ^ k) p = (M ^ k) p := by
  intro k
  induction k with
  | zero => intro p _; simp
  | succ k ih =>
    intro p hp
    have hpS : p ∉ S := fun h => by have := hp p h; rw [hself] at this; omega
    funext q
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply, hrow p hpS]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases le_or_gt (dist p l) 1 with hl | hl
    · rw [ih l fun a ha => by have := hp a ha; have := htri p l a; omega]
    · rw [hM p l hl, zero_mul, zero_mul]

/-! ## 2. The path -/

/-- **A local change is unseen outside the cone.** Change `T_d` on the rows of `S`. After `k`
steps, a site `i` with `k ≤ |i − a|` for all `a ∈ S` carries the same amplitude as before. -/
theorem change_unseen {d : ℕ} (M' : Matrix (Fin d) (Fin d) ℂ) (S : Set (Fin d))
    (hrow : ∀ p, p ∉ S → M' p = Td d p) (k : ℕ) (i : Fin d)
    (hi : ∀ a ∈ S, k ≤ distPath i a) (ψ : Hd d) :
    Matrix.toEuclideanLin (M' ^ k) ψ i = Matrix.toEuclideanLin (Td d ^ k) ψ i := by
  have h := pow_row_eq_of_le distPath distPath_self distPath_tri (Td d) M' Td_local S hrow k i hi
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, h]

/-- `T_d` with an on-site change `ε` at `s`. -/
def onSite {d : ℕ} (s : Fin d) (ε : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Td d + Matrix.diagonal (Pi.single s ε)

theorem onSite_row {d : ℕ} (s : Fin d) (ε : ℂ) (p : Fin d) (hp : p ∉ ({s} : Set (Fin d))) :
    onSite s ε p = Td d p := by
  have hps : p ≠ s := hp
  funext q
  simp [onSite, Matrix.diagonal_apply, hps]

/-- **The front arrives on time.** For `s = i + k`, the change at `s` is unseen at `i` after
`k` steps, and after `k + 1` steps the amplitude from `i` to `s` differs by `ε ρ_d^{−k}`. -/
theorem onSite_front {d : ℕ} (k : ℕ) (i s : Fin d) (hs : s.val = i.val + k) (ε : ℂ) :
    (onSite s ε ^ k) i = (Td d ^ k) i ∧
      (onSite s ε ^ (k + 1)) i s - (Td d ^ (k + 1)) i s = ε * ((rho d : ℂ)⁻¹) ^ k := by
  have hrow := pow_row_eq_of_le distPath distPath_self distPath_tri (Td d) (onSite s ε)
    Td_local {s} (onSite_row s ε) k i fun a ha => by
      rw [Set.mem_singleton_iff] at ha; subst ha; unfold distPath; omega
  refine ⟨hrow, ?_⟩
  rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, hrow, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single s]
  · simp only [onSite, Matrix.add_apply, Matrix.diagonal_apply_eq, Pi.single_eq_same]
    rw [lightCone_edge k i s hs]
    ring
  · intro l _ hl
    simp [onSite, hl]
  · simp

/-- The difference at the front is nonzero for `ε ≠ 0`. -/
theorem onSite_front_ne_zero {d : ℕ} (hd : 2 ≤ d) (k : ℕ) (i s : Fin d)
    (hs : s.val = i.val + k) {ε : ℂ} (hε : ε ≠ 0) :
    (onSite s ε ^ (k + 1)) i s - (Td d ^ (k + 1)) i s ≠ 0 := by
  rw [(onSite_front k i s hs ε).2]
  have hr : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos d hd).ne'
  exact mul_ne_zero hε (pow_ne_zero _ (inv_ne_zero hr))

end DefectPropagation

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum
public import NavaRobertsonIndependent.Mathematics.D37h_OctahedralSymmetry

/-!
# D37i — The three families of boxes

A box is the number of positions on each of the three axes, `b : Fin 3 → ℕ`. With `4` or more
positions on every axis, each axis has its own NRS angle `θ_NRS(b i)` (`D37b`), and a box is a
deformation of the regular `4 × 4 × 4`. The boxes split into three families by how many axes have
the same length:

* **regular**, `b 0 = b 1 = b 2` (`4 × 4 × 4`, `5 × 5 × 5`, …): `48` symmetries (`O_h`), orbit `1`;
* **two equal axes** (`4 × 10 × 10`, `100 × 100 × 4`): `16` symmetries (`D₄h`), orbit `3`;
* **three different axes** (`67 × 25 × 1600`): `8` symmetries (`D₂h`), orbit `6`.

The symmetries are the signed permutations of the axes that keep the angle of every axis
(`D37h`, `keepsAngles_iff`); the reflections always do, so only the permutation of the axes
matters. The orbit of a box is the set of boxes obtained by reordering its axes: the same figure,
turned. Orbit and stabilizer multiply to `3! = 6` (`card_orbit_mul_card_stab`).

## Main results

- `BoxFamilies.family_partition` : every box is in exactly one of the three families.
- `BoxFamilies.card_axisStab_regular`, `_twoEqual`, `_distinct` : `6`, `2`, `1` permutations of
  the axes keep a box of each family.
- `BoxFamilies.card_keepsAngles_family` : `48`, `16`, `8` signed permutations keep every angle.
- `BoxFamilies.card_orbit_mul_card_stab` : orbit × stabilizer = `6`.
- `BoxFamilies.card_orbit_regular`, `_twoEqual`, `_distinct` : orbits of `1`, `3`, `6` boxes.
- `BoxFamilies.count_ten` : with `4` to `10` positions per axis, `7 + 126 + 210 = 343` boxes,
  that is `7 + 42 + 35 = 84` different figures.
- `BoxFamilies.quantum_never_erased` : for every box with `4` or more positions per axis, of any
  family and turned or reflected in any of the `48` ways, every axis opens between `θ_NRS(4) > 0`
  and the unattained `arccos (1 / C_∞)`, and `0 < δ(4)³ ≤ 𝒱 < δ_∞³`. The quantum changes,
  turns and deforms, but it is not erased.
- `BoxFamilies.quantum_erased_iff` : it is erased only when some axis has `2` or `3` positions.
-/

@[expose] public section

open OctahedralSymmetry NRSAngle VolumetricQuantum DimensionalQuantum Gnomon

namespace BoxFamilies

/-- A box: the number of positions on each of the three axes. -/
abbrev Box := Fin 3 → ℕ

/-! ## 1. The three families -/

/-- All three axes have the same length. -/
def IsRegular (b : Box) : Prop := b 0 = b 1 ∧ b 1 = b 2

/-- Exactly two axes have the same length. -/
def IsTwoEqual (b : Box) : Prop := ¬IsRegular b ∧ (b 0 = b 1 ∨ b 1 = b 2 ∨ b 0 = b 2)

/-- The three axes have different lengths. -/
def IsDistinct (b : Box) : Prop := b 0 ≠ b 1 ∧ b 1 ≠ b 2 ∧ b 0 ≠ b 2

instance (b : Box) : Decidable (IsRegular b) := by unfold IsRegular; infer_instance
instance (b : Box) : Decidable (IsTwoEqual b) := by unfold IsTwoEqual; infer_instance
instance (b : Box) : Decidable (IsDistinct b) := by unfold IsDistinct; infer_instance

/-- **The partition.** Every box is in exactly one of the three families. -/
theorem family_partition (b : Box) :
    (IsRegular b ∨ IsTwoEqual b ∨ IsDistinct b) ∧ ¬(IsRegular b ∧ IsTwoEqual b) ∧
      ¬(IsRegular b ∧ IsDistinct b) ∧ ¬(IsTwoEqual b ∧ IsDistinct b) := by
  simp only [IsTwoEqual, IsRegular, IsDistinct]
  refine ⟨?_, by tauto, by tauto, by tauto⟩
  by_cases h01 : b 0 = b 1 <;> by_cases h12 : b 1 = b 2 <;> by_cases h02 : b 0 = b 2 <;> tauto

/-! ## 2. The stabilizer: permutations of the axes that keep the box -/

/-- The permutations of the axes that keep the length of every axis. -/
def axisStab (b : Box) : Finset (Equiv.Perm (Fin 3)) :=
  Finset.univ.filter fun σ => ∀ i, b (σ i) = b i

/-- The equality pattern of a box: which axes have the same length. -/
def pattern (b : Box) : Fin 3 → Fin 3 → Bool := fun i j => decide (b i = b j)

theorem axisStab_eq_pattern (b : Box) :
    axisStab b = Finset.univ.filter fun σ => ∀ i, pattern b (σ i) i = true := by
  simp [axisStab, pattern]

/-- The stabilizer depends only on the equality pattern. -/
private theorem card_axisStab_of_pattern {b : Box} {M : Fin 3 → Fin 3 → Bool}
    (h : pattern b = M) :
    (axisStab b).card = (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
      ∀ i, M (σ i) i = true).card := by
  rw [axisStab_eq_pattern, h]

theorem card_axisStab_regular {b : Box} (h : IsRegular b) : (axisStab b).card = 6 := by
  obtain ⟨h01, h12⟩ := h
  rw [card_axisStab_of_pattern (M := fun _ _ => true)]
  · decide
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [pattern] <;> omega

theorem card_axisStab_distinct {b : Box} (h : IsDistinct b) : (axisStab b).card = 1 := by
  obtain ⟨h01, h12, h02⟩ := h
  rw [card_axisStab_of_pattern (M := fun i j => decide (i = j))]
  · decide
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [pattern] <;> omega

theorem card_axisStab_twoEqual {b : Box} (h : IsTwoEqual b) : (axisStab b).card = 2 := by
  obtain ⟨hr, h01 | h12 | h02⟩ := h <;> unfold IsRegular at hr
  · rw [card_axisStab_of_pattern (M := fun i j => decide (i = j) || (i ≠ 2 && j ≠ 2))]
    · decide
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [pattern] <;> omega
  · rw [card_axisStab_of_pattern (M := fun i j => decide (i = j) || (i ≠ 0 && j ≠ 0))]
    · decide
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [pattern] <;> omega
  · rw [card_axisStab_of_pattern (M := fun i j => decide (i = j) || (i ≠ 1 && j ≠ 1))]
    · decide
    · funext i j
      fin_cases i <;> fin_cases j <;> simp [pattern] <;> omega

/-- The signed permutations that keep the box are the permutations that keep it, with any
reflections: `8` times as many. -/
theorem card_signedStab (b : Box) :
    Fintype.card {g : Equiv.Perm (Fin 3) × (Fin 3 → Bool) // ∀ i, b (g.1 i) = b i} =
      8 * (axisStab b).card := by
  calc Fintype.card {g : Equiv.Perm (Fin 3) × (Fin 3 → Bool) // ∀ i, b (g.1 i) = b i}
      = Fintype.card ({σ : Equiv.Perm (Fin 3) // ∀ i, b (σ i) = b i} × (Fin 3 → Bool)) :=
        Fintype.card_congr
          (Equiv.prodSubtypeFstEquivSubtypeProd
            (p := fun σ : Equiv.Perm (Fin 3) => ∀ i, b (σ i) = b i))
    _ = 8 * (axisStab b).card := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_subtype, axisStab]
        simp [mul_comm]

/-- **The symmetries of each family.** With `4` or more positions on every axis, `48`, `16` or `8`
signed permutations keep the NRS angle of every axis. -/
theorem card_keepsAngles_family {b : Box} (h4 : ∀ i, 4 ≤ b i)
    [DecidablePred (KeepsAngles b)] :
    (IsRegular b → Fintype.card {g // KeepsAngles b g} = 48) ∧
      (IsTwoEqual b → Fintype.card {g // KeepsAngles b g} = 16) ∧
      (IsDistinct b → Fintype.card {g // KeepsAngles b g} = 8) := by
  rw [card_keepsAngles h4, card_signedStab]
  exact ⟨fun h => by rw [card_axisStab_regular h], fun h => by rw [card_axisStab_twoEqual h],
    fun h => by rw [card_axisStab_distinct h]⟩

/-! ## 3. The orbit: the same figure, turned -/

/-- The boxes obtained by reordering the axes of `b`. -/
def axisOrbit (b : Box) : Finset Box := Finset.univ.image fun σ : Equiv.Perm (Fin 3) => b ∘ σ

theorem card_fiber (b : Box) (τ : Equiv.Perm (Fin 3)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => b ∘ σ = b ∘ τ).card = (axisStab b).card := by
  refine Finset.card_nbij' (fun σ => σ * τ⁻¹) (fun ρ => ρ * τ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [axisStab, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    intro i
    have := congrFun hσ (τ⁻¹ i)
    simpa [Equiv.Perm.mul_apply] using this
  · intro ρ hρ
    simp only [axisStab, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    funext i
    simpa [Equiv.Perm.mul_apply] using hρ (τ i)
  · intro σ _
    simp
  · intro ρ _
    simp

/-- **Orbit–stabilizer.** The orbit and the stabilizer of a box multiply to `3! = 6`. -/
theorem card_orbit_mul_card_stab (b : Box) : (axisOrbit b).card * (axisStab b).card = 6 := by
  have h := Finset.card_eq_sum_card_image (fun σ : Equiv.Perm (Fin 3) => b ∘ σ) Finset.univ
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [← axisOrbit] at h
  have hc : ∀ y ∈ axisOrbit b,
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => b ∘ σ = y).card = (axisStab b).card := by
    intro y hy
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hy
    exact card_fiber b τ
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul] at h
  simpa [Nat.factorial] using h.symm

theorem card_orbit_regular {b : Box} (h : IsRegular b) : (axisOrbit b).card = 1 := by
  have := card_orbit_mul_card_stab b
  rw [card_axisStab_regular h] at this
  omega

theorem card_orbit_twoEqual {b : Box} (h : IsTwoEqual b) : (axisOrbit b).card = 3 := by
  have := card_orbit_mul_card_stab b
  rw [card_axisStab_twoEqual h] at this
  omega

theorem card_orbit_distinct {b : Box} (h : IsDistinct b) : (axisOrbit b).card = 6 := by
  have := card_orbit_mul_card_stab b
  rw [card_axisStab_distinct h] at this
  omega

/-! ## 4. Counting up to ten positions per axis -/

/-- The boxes with `4` to `N` positions on every axis, as triples. -/
def boxesUpTo (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.Icc 4 N ×ˢ Finset.Icc 4 N ×ˢ Finset.Icc 4 N

/-- The box of a triple. -/
def ofTriple (t : ℕ × ℕ × ℕ) : Box := ![t.1, t.2.1, t.2.2]

set_option maxRecDepth 100000 in
/-- **The count at `N = 10`.** Of the `343` boxes with `4` to `10` positions per axis, `7` are
regular, `126` have two equal axes and `210` three different axes. Dividing by the orbits
`1`, `3`, `6`, they are `7 + 42 + 35 = 84` different figures. -/
theorem count_ten :
    ((boxesUpTo 10).filter fun t => IsRegular (ofTriple t)).card = 7 ∧
      ((boxesUpTo 10).filter fun t => IsTwoEqual (ofTriple t)).card = 126 ∧
      ((boxesUpTo 10).filter fun t => IsDistinct (ofTriple t)).card = 210 ∧
      (boxesUpTo 10).card = 343 ∧ 7 / 1 + 126 / 3 + 210 / 6 = 84 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩ <;> decide +kernel

/-! ## 5. The quantum is never erased -/

/-- The volumetric quantum of a box, the product of the quanta of its three axes. -/
theorem volQuantum_eq_prod (b : Box) :
    volQuantum (b 0) (b 1) (b 2) = ∏ i, dimQuantum (b i) := by
  simp [volQuantum, Fin.prod_univ_three]

/-- Reordering the axes does not change the volumetric quantum. -/
theorem volQuantum_perm (b : Box) (σ : Equiv.Perm (Fin 3)) :
    volQuantum (b (σ 0)) (b (σ 1)) (b (σ 2)) = volQuantum (b 0) (b 1) (b 2) := by
  have h := volQuantum_eq_prod (b ∘ σ)
  simp only [Function.comp_apply] at h
  rw [h, volQuantum_eq_prod b]
  exact Equiv.prod_comp σ fun i => dimQuantum (b i)

/-- **The quantum is never erased.** Take any box with `4` or more positions on every axis.
Whatever its family, each axis opens at an angle between `θ_NRS(4) > 0` (the regular
`4 × 4 × 4`) and the ceiling `arccos (1 / C_∞)` that no box attains; the volumetric quantum lies
between the floor `δ(4)³ > 0` and the unattained ceiling `δ_∞³`; and turning or reflecting the
box, in any of the `48` ways, leaves the quantum as it is. -/
theorem quantum_never_erased (b : Box) (h4 : ∀ i, 4 ≤ b i) :
    (IsRegular b ∨ IsTwoEqual b ∨ IsDistinct b) ∧
      (∀ i, 0 < angleNRS 4 ∧ angleNRS 4 ≤ angleNRS (b i) ∧
        angleNRS (b i) < Real.arccos (1 / CoherenceConstantInf)) ∧
      (0 < dimQuantum 4 ^ 3 ∧ dimQuantum 4 ^ 3 ≤ volQuantum (b 0) (b 1) (b 2) ∧
        volQuantum (b 0) (b 1) (b 2) < deltaInf ^ 3) ∧
      ∀ g : Equiv.Perm (Fin 3) × (Fin 3 → Bool),
        volQuantum (b (g.1 0)) (b (g.1 1)) (b (g.1 2)) = volQuantum (b 0) (b 1) (b 2) :=
  ⟨(family_partition b).1, fun i => angle_floor (h4 i),
    ⟨pow_pos (dimQuantum_pos le_rfl) 3, (volQuantum_certificate (h4 0) (h4 1) (h4 2)).2⟩,
    fun g => volQuantum_perm b g.1⟩

/-- **The only way to erase it** is to leave the rule: some axis with `2` or `3` positions. -/
theorem quantum_erased_iff (b : Box) (h2 : ∀ i, 2 ≤ b i) :
    volQuantum (b 0) (b 1) (b 2) = 0 ↔ ∃ i, b i = 2 ∨ b i = 3 := by
  rw [volQuantum_eq_zero_iff (h2 0) (h2 1) (h2 2)]
  constructor
  · rintro (h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  · rintro ⟨i, h⟩
    fin_cases i
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

end BoxFamilies

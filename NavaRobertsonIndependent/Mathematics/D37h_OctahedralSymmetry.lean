/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle

/-!
# D37h — The octahedral symmetry of the cube `d × d × d`

The cube with `d` positions on each of its three axes has positions `Fin 3 → Fin d`, and each
axis `i` carries the pair `(T_d, P_d)` of `D3` on its coordinate (`liftAlong` of `D37` along
`Equiv.piSplitAt i`). Its symmetry group is the octahedral group `O_h`: the `3! · 2³ = 48`
signed permutations `(σ, s)`, where `σ` permutes the axes and `s i` reflects axis `i`,
`j ↦ d − 1 − j`.

Relabelling the positions by `(σ, s)` sends `T` of axis `i` to `T` of axis `σ i` (the path is
symmetric under reflection) and `P` of axis `i` to `± P` of axis `σ i` (reflection reverses the
position). A sign does not change the angle between the fluctuation vectors, so the NRS angle of
axis `σ i` in the relabelled state is the NRS angle of axis `i` in the original one, for every
state. At the maximal current state of the cube all three axes have the angle `θ_NRS(d)` of `D37b`:
the angles, and
with them the volumetric quantum `δ(d)³` of `D37e`, are invariant under all of `O_h`.

## Main results

- `OctahedralSymmetry.card_signedPerm` : there are `48` signed permutations of the three axes.
- `OctahedralSymmetry.cubeSym_injective` : for `d ≥ 2` they act on the positions in `48` different
  ways.
- `OctahedralSymmetry.reindex_liftAxis` : relabelling by `(σ, s)` moves an operator of axis `i`
  to axis `σ i`, reflected when `s (σ i)` is set.
- `OctahedralSymmetry.angleAxis_cubeSym` : the angle of axis `σ i` after `(σ, s)` is the angle
  of axis `i` before, at every unit state.
- `OctahedralSymmetry.angleAxis_psiCube` : at the maximal current state of the cube every axis has
  the angle `θ_NRS(d)`.
- `OctahedralSymmetry.octahedral_symmetry` : for all `48` elements and all three axes, the angle
  at the image of the maximal current state of the cube is `θ_NRS(d)`; from `d = 4` on it is
  positive and below
  `arccos (1 / C_∞)`.
- `OctahedralSymmetry.keepsAngles_iff` : with unequal axes, all with `4` or more positions, a signed
  permutation keeps the angle of every axis iff it only exchanges axes of the same length.
- `OctahedralSymmetry.card_keepsAngles_equal`, `card_keepsAngles_two_equal`,
  `card_keepsAngles_distinct` : `48` for `d × d × d`, `16` for `100 × 100 × 4`, `8` for
  `67 × 25 × 1600`.
-/

@[expose] public noncomputable section

open TransportPosition NRSInequality SpectralExtremal PathGraph3DNRS NRSAngle

namespace OctahedralSymmetry

/-! ## 1. Relabelling the positions preserves the angle -/

section Relabel

variable {ι : Type*}

/-- The state relabelled by a permutation `π` of the positions: `(π • Ψ) p = Ψ (π⁻¹ p)`. -/
def permState (π : Equiv.Perm ι) (Ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun p => Ψ (π.symm p)

theorem permState_apply (π : Equiv.Perm ι) (Ψ : EuclideanSpace ℂ ι) (p : ι) :
    permState π Ψ p = Ψ (π.symm p) := rfl

theorem permState_sub (π : Equiv.Perm ι) (Ψ Φ : EuclideanSpace ℂ ι) :
    permState π (Ψ - Φ) = permState π Ψ - permState π Φ := by
  ext p
  simp [permState_apply]

theorem permState_smul (π : Equiv.Perm ι) (c : ℂ) (Ψ : EuclideanSpace ℂ ι) :
    permState π (c • Ψ) = c • permState π Ψ := by
  ext p
  simp [permState_apply]

variable [Fintype ι]

/-- Relabelling preserves inner products. -/
theorem inner_permState (π : Equiv.Perm ι) (Ψ Φ : EuclideanSpace ℂ ι) :
    inner ℂ (permState π Ψ) (permState π Φ) = inner ℂ Ψ Φ := by
  simp only [PiLp.inner_apply, permState_apply]
  exact Equiv.sum_comp π.symm (fun p => inner ℂ (Ψ p) (Φ p))

theorem norm_permState (π : Equiv.Perm ι) (Ψ : EuclideanSpace ℂ ι) :
    ‖permState π Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_permState]

/-- A sign on the second observable does not change the angle. -/
theorem angleG_neg_right (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : angleG L (-M) Ψ = angleG L M Ψ := by
  have hm : meanG (-M) Ψ = -meanG M Ψ := by
    simp [meanG, inner_neg_right]
  have hc : centeredG (-M) Ψ = -centeredG M Ψ := by
    rw [centeredG, centeredG, hm]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg, neg_smul]
    abel
  rw [angleG, angleG, hc, inner_neg_right, norm_neg, norm_neg]

variable [DecidableEq ι]

/-- The relabelled operator acts on the relabelled state as the operator on the state. -/
theorem toEuclideanLin_reindex (π : Equiv.Perm ι) (A : Matrix ι ι ℂ)
    (Ψ : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (Matrix.reindex π π A) (permState π Ψ) =
      permState π (Matrix.toEuclideanLin A Ψ) := by
  ext p
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.reindex_apply, Matrix.submatrix_apply, permState_apply]
  exact Equiv.sum_comp π.symm (fun q => A (π.symm p) q * Ψ q)

theorem meanG_reindex (π : Equiv.Perm ι) (A : Matrix ι ι ℂ) (Ψ : EuclideanSpace ℂ ι) :
    meanG (Matrix.toEuclideanLin (Matrix.reindex π π A)) (permState π Ψ) =
      meanG (Matrix.toEuclideanLin A) Ψ := by
  rw [meanG, meanG, toEuclideanLin_reindex, inner_permState]

theorem centeredG_reindex (π : Equiv.Perm ι) (A : Matrix ι ι ℂ) (Ψ : EuclideanSpace ℂ ι) :
    centeredG (Matrix.toEuclideanLin (Matrix.reindex π π A)) (permState π Ψ) =
      permState π (centeredG (Matrix.toEuclideanLin A) Ψ) := by
  rw [centeredG, centeredG, meanG_reindex, toEuclideanLin_reindex, permState_sub,
    permState_smul]

/-- **Relabelling invariance.** The angle between the fluctuation vectors is unchanged when the
positions, the operators and the state are relabelled together. -/
theorem angleG_reindex (π : Equiv.Perm ι) (A B : Matrix ι ι ℂ) (Ψ : EuclideanSpace ℂ ι) :
    angleG (Matrix.toEuclideanLin (Matrix.reindex π π A))
        (Matrix.toEuclideanLin (Matrix.reindex π π B)) (permState π Ψ) =
      angleG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) Ψ := by
  rw [angleG, angleG, centeredG_reindex, centeredG_reindex, inner_permState, norm_permState,
    norm_permState]

end Relabel

/-! ## 2. The path is symmetric under reflection; the position reverses -/

section Reflection

variable {d : ℕ}

theorem minStep_rev (a b : Fin d) : MinStep (Fin.rev a) (Fin.rev b) ↔ MinStep a b := by
  simp only [MinStep, Fin.val_rev]
  omega

/-- `T_d` is invariant under the reflection `j ↦ d − 1 − j`. -/
theorem Td_submatrix_rev : (Td d).submatrix Fin.revPerm Fin.revPerm = Td d := by
  ext a b
  simp [Td, Ad, minStep_rev]

theorem posCoord_rev (a : Fin d) : posCoord d (Fin.rev a) = -posCoord d a := by
  have ha := a.isLt
  rw [posCoord, posCoord, Fin.val_rev, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- `P_d` changes sign under the reflection `j ↦ d − 1 − j`. -/
theorem Pd_submatrix_rev : (Pd d).submatrix Fin.revPerm Fin.revPerm = -Pd d := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Pd, posCoord_rev]
  · simp [Pd, h, Fin.rev_inj]

end Reflection

/-! ## 3. The cube with `d` positions on each axis -/

section Cube

variable (d : ℕ)

/-- The positions of the cube `d × d × d`: a coordinate in `Fin d` for each of the three axes. -/
abbrev CubeSite := Fin 3 → Fin d

/-- Splitting a position into its coordinate on axis `i` and the other two. -/
abbrev axisSplit (i : Fin 3) : CubeSite d ≃ Fin d × ({j // j ≠ i} → Fin d) :=
  Equiv.piSplitAt i fun _ => Fin d

/-- An operator on axis `i`: `A` on that coordinate, the identity on the other two. -/
def liftAxis (i : Fin 3) (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (CubeSite d) (CubeSite d) ℂ :=
  liftAlong (axisSplit d i) A

variable {d}

theorem liftAxis_apply (i : Fin 3) (A : Matrix (Fin d) (Fin d) ℂ) (p q : CubeSite d) :
    liftAxis d i A p q = A (p i) (q i) * if ∀ j, j ≠ i → p j = q j then 1 else 0 := by
  simp only [liftAxis, liftAlong, Matrix.of_apply, Equiv.piSplitAt_apply]
  congr 1
  refine if_congr ⟨fun h j hj => congrFun h ⟨j, hj⟩, fun h => funext fun j => h j j.2⟩ rfl rfl

/-- The reflection `j ↦ d − 1 − j` when `b` is set, the identity otherwise. -/
def flip (b : Bool) : Equiv.Perm (Fin d) := if b then Fin.revPerm else Equiv.refl _

theorem flip_flip (b : Bool) (a : Fin d) : flip b (flip b a) = a := by
  cases b <;> simp [flip]

/-- The signed permutation `(σ, s)` on the positions: axis `σ⁻¹ j` goes to axis `j`, reflected when
`s j` is set. -/
def cubeSym (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : Equiv.Perm (CubeSite d) where
  toFun p j := flip (s j) (p (σ.symm j))
  invFun p k := flip (s (σ k)) (p (σ k))
  left_inv p := by
    funext k
    simp [flip_flip]
  right_inv p := by
    funext j
    simp [flip_flip]

theorem cubeSym_symm_apply (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (p : CubeSite d)
    (k : Fin 3) : (cubeSym σ s).symm p k = flip (s (σ k)) (p (σ k)) := rfl

/-- There are `3! · 2³ = 48` signed permutations of the three axes. -/
theorem card_signedPerm : Fintype.card (Equiv.Perm (Fin 3) × (Fin 3 → Bool)) = 48 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun]
  rfl

/-- **The action is faithful.** For `d ≥ 2` the `48` signed permutations move the positions in `48`
different ways: `s` is read off the corner `0`, then `σ` off one step along each axis. -/
theorem cubeSym_injective (hd : 2 ≤ d) :
    Function.Injective fun g : Equiv.Perm (Fin 3) × (Fin 3 → Bool) => cubeSym (d := d) g.1 g.2 := by
  rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
  simp only at h
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
  have hflip (b b' : Bool) (hb : flip (d := d) b z = flip b' z) : b = b' := by
    cases b <;> cases b' <;> simp_all [flip, z, Fin.ext_iff, Fin.val_rev] <;> omega
  have hs : s = s' := by
    funext j
    have := congrArg (fun π : Equiv.Perm (CubeSite d) => π (fun _ => z) j) h
    exact hflip _ _ this
  subst hs
  refine Prod.ext (Equiv.ext fun a => ?_) rfl
  have := congrArg (fun π : Equiv.Perm (CubeSite d) =>
    π (fun k => if k = a then o else z) (σ a)) h
  simp only [cubeSym, Equiv.coe_fn_mk, Equiv.symm_apply_apply, ite_true] at this
  by_contra hne
  have hne' : σ'.symm (σ a) ≠ a := fun e => by
    have h' := congrArg σ' e
    rw [Equiv.apply_symm_apply] at h'
    exact hne h'
  simp only [hne', ↓reduceIte] at this
  exact hzo ((flip (s (σ a))).injective this).symm

/-- **Relabelling moves the axes.** Under `(σ, s)`, an operator of axis `i` becomes the same
operator on axis `σ i`, reflected when `s (σ i)` is set. -/
theorem reindex_liftAxis (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (i : Fin 3)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.reindex (cubeSym σ s) (cubeSym σ s) (liftAxis d i A) =
      liftAxis d (σ i) (A.submatrix (flip (s (σ i))) (flip (s (σ i)))) := by
  ext p q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, liftAxis_apply, cubeSym_symm_apply]
  congr 1
  refine if_congr ⟨fun h k hk => ?_, fun h j hj => ?_⟩ rfl rfl
  · have := h (σ.symm k) (fun e => hk (by rw [← e, Equiv.apply_symm_apply]))
    rw [Equiv.apply_symm_apply] at this
    exact (flip (s k)).injective this
  · rw [h (σ j) (fun e => hj (σ.injective e))]

theorem Td_submatrix_flip (b : Bool) : (Td d).submatrix (flip b) (flip b) = Td d := by
  cases b
  · rfl
  · exact Td_submatrix_rev

theorem Pd_submatrix_flip (b : Bool) :
    (Pd d).submatrix (flip b) (flip b) = ((if b then -1 else 1 : ℝ) : ℂ) • Pd d := by
  cases b
  · simp [flip]
  · simpa [flip] using Pd_submatrix_rev

theorem liftAxis_smul (i : Fin 3) (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    liftAxis d i (c • A) = c • liftAxis d i A := by
  ext p q
  simp [liftAxis_apply]

/-- Transport and position on axis `i` of the cube. -/
def TAxis (i : Fin 3) : EuclideanSpace ℂ (CubeSite d) →ₗ[ℂ] EuclideanSpace ℂ (CubeSite d) :=
  Matrix.toEuclideanLin (liftAxis d i (Td d))

def PAxis (i : Fin 3) : EuclideanSpace ℂ (CubeSite d) →ₗ[ℂ] EuclideanSpace ℂ (CubeSite d) :=
  Matrix.toEuclideanLin (liftAxis d i (Pd d))

/-- The NRS angle of axis `i` at the state `Ψ`. -/
def angleAxis (i : Fin 3) (Ψ : EuclideanSpace ℂ (CubeSite d)) : ℝ :=
  angleG (TAxis i) (PAxis i) Ψ

/-- **The angle follows the axis.** The NRS angle of axis `σ i` after `(σ, s)` is the NRS angle of
axis `i` before, at every state. -/
theorem angleAxis_cubeSym (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (i : Fin 3)
    (Ψ : EuclideanSpace ℂ (CubeSite d)) :
    angleAxis (σ i) (permState (cubeSym σ s) Ψ) = angleAxis i Ψ := by
  have h := angleG_reindex (cubeSym σ s) (liftAxis d i (Td d)) (liftAxis d i (Pd d)) Ψ
  rw [reindex_liftAxis, reindex_liftAxis, Td_submatrix_flip, Pd_submatrix_flip,
    liftAxis_smul, map_smul] at h
  simp only [angleAxis, TAxis, PAxis]
  rw [← h]
  cases s (σ i)
  · simp
  · simp only [ite_true, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul]
    exact (angleG_neg_right _ _ _).symm

end Cube

/-! ## 4. The maximal-tension state of the cube -/

section Star

variable {d : ℕ}

/-- The maximal current state of the cube: the maximal current state on each axis. -/
def psiCube (d : ℕ) : EuclideanSpace ℂ (CubeSite d) :=
  WithLp.toLp 2 fun p => ∏ j, maxCurrentState d (p j)

/-- The product of unit states over any finite set of axes has norm one. -/
theorem norm_prodState {κ : Type*} [Fintype κ] [DecidableEq κ] {ψ : EuclideanSpace ℂ (Fin d)}
    (hψ : ‖ψ‖ = 1) :
    ‖(WithLp.toLp 2 fun q : κ → Fin d => ∏ j, ψ (q j) : EuclideanSpace ℂ (κ → Fin d))‖ = 1 := by
  have h1 : ∑ a, ‖ψ a‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  have h2 : ‖(WithLp.toLp 2 fun q : κ → Fin d => ∏ j, ψ (q j) :
      EuclideanSpace ℂ (κ → Fin d))‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun (_ : κ) (a : Fin d) => ‖ψ a‖ ^ 2), h1, Finset.prod_const_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-- The maximal current state of the cube is the maximal current state on axis `i` times the product
state on the other two axes. -/
theorem psiCube_eq_prodAlong (i : Fin 3) :
    psiCube d = prodAlong (axisSplit d i) (maxCurrentState d)
      (WithLp.toLp 2 fun q : {j // j ≠ i} → Fin d => ∏ j, maxCurrentState d (q j)) := by
  ext p
  simp only [psiCube, prodAlong_apply, Equiv.piSplitAt_apply]
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => maxCurrentState d (p j)) i

/-- **At the maximal current state of the cube every axis has the angle `θ_NRS(d)`.** -/
theorem angleAxis_psiCube (hd : 2 ≤ d) (i : Fin 3) : angleAxis i (psiCube d) = angleNRS d := by
  rw [angleAxis, TAxis, PAxis, psiCube_eq_prodAlong i, liftAxis, liftAxis]
  exact angleG_lift _ (norm_prodState (norm_maxCurrentState hd)) _ _ _

/-- **Octahedral symmetry.** For each of the `48` signed permutations `(σ, s)` of the axes and each
axis `j`, the NRS angle of axis `j` at the image of the maximal current state of the cube is
`θ_NRS(d)`: the three angles of the
cube `d × d × d` are the same number and are carried into one another by all of `O_h`. From
`d = 4` on this common angle is positive and below `arccos (1 / C_∞)`. -/
theorem octahedral_symmetry (hd : 2 ≤ d) (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (j : Fin 3) : angleAxis j (permState (cubeSym σ s) (psiCube d)) = angleNRS d := by
  have h := angleAxis_cubeSym σ s (σ.symm j) (psiCube d)
  rw [Equiv.apply_symm_apply] at h
  rw [h, angleAxis_psiCube hd]

theorem octahedral_angle_bounds (hd : 4 ≤ d) (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (j : Fin 3) :
    0 < angleAxis j (permState (cubeSym σ s) (psiCube d)) ∧
      angleAxis j (permState (cubeSym σ s) (psiCube d)) <
        Real.arccos (1 / Gnomon.CoherenceConstantInf) := by
  rw [octahedral_symmetry (by omega)]
  exact ⟨angleNRS_pos hd, angleNRS_lt_limit hd⟩

end Star

/-! ## 5. Unequal axes: which signed permutations keep every angle -/

section Unequal

/-- The signed permutation `(σ, s)` keeps the NRS angle of every axis of the box with `dims i`
positions on axis `i`: axis `i` and axis `σ i` have the same angle. A reflection never changes an
angle (it depends only on the number of positions), so only `σ` matters. -/
def KeepsAngles (dims : Fin 3 → ℕ) (g : Equiv.Perm (Fin 3) × (Fin 3 → Bool)) : Prop :=
  ∀ i, angleNRS (dims (g.1 i)) = angleNRS (dims i)

/-- With `4` or more positions on every axis, a signed permutation keeps every angle iff it only
exchanges axes of the same length: `θ_NRS` is strictly increasing from `4` on (`D37b`). -/
theorem keepsAngles_iff {dims : Fin 3 → ℕ} (h4 : ∀ i, 4 ≤ dims i)
    (g : Equiv.Perm (Fin 3) × (Fin 3 → Bool)) :
    KeepsAngles dims g ↔ ∀ i, dims (g.1 i) = dims i :=
  forall_congr' fun i => angleNRS_strictMonoOn.injOn.eq_iff (h4 (g.1 i)) (h4 i)

/-- The number of signed permutations that keep every angle equals the number that only exchange
axes of the same length. -/
theorem card_keepsAngles {dims : Fin 3 → ℕ} (h4 : ∀ i, 4 ≤ dims i)
    [DecidablePred (KeepsAngles dims)] :
    Fintype.card {g // KeepsAngles dims g} =
      Fintype.card {g : Equiv.Perm (Fin 3) × (Fin 3 → Bool) // ∀ i, dims (g.1 i) = dims i} :=
  Fintype.card_congr (Equiv.subtypeEquivRight (keepsAngles_iff h4))

/-- **Equal axes, `d × d × d`:** all `48` signed permutations keep every angle. -/
theorem card_keepsAngles_equal {d : ℕ} (hd : 4 ≤ d) [DecidablePred (KeepsAngles fun _ => d)] :
    Fintype.card {g // KeepsAngles (fun _ => d) g} = 48 := by
  rw [card_keepsAngles fun _ => hd,
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ _ => rfl)]
  exact card_signedPerm

/-- **Two equal axes, `100 × 100 × 4`:** `16` signed permutations keep every angle. -/
theorem card_keepsAngles_two_equal [DecidablePred (KeepsAngles ![100, 100, 4])] :
    Fintype.card {g // KeepsAngles ![100, 100, 4] g} = 16 := by
  rw [card_keepsAngles (by decide)]
  decide

/-- **Three different axes, `67 × 25 × 1600`:** only the `8` reflections keep every angle. -/
theorem card_keepsAngles_distinct [DecidablePred (KeepsAngles ![67, 25, 1600])] :
    Fintype.card {g // KeepsAngles ![67, 25, 1600] g} = 8 := by
  rw [card_keepsAngles (by decide)]
  decide

end Unequal

end OctahedralSymmetry

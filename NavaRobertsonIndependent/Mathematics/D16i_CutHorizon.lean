/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16h_CutCycles

/-!
# D16i — The cut is a horizon: its configurations are hidden inside the cone

`D16h` counts the graphs of a cut; `D16d` says a change of transport is unseen outside its
cone. Together they say which information a site cannot read.

* `linksMatrix S ε` is `T_d` with amplitude `ε` on every link of `S`. It differs from `T_d`
  only on the rows of the ends of `S` (`linksMatrix_row`), so after `k` steps a site at
  distance `≥ k` from every end sees exactly `T_d^k` (`links_unseen`), for every state.
* `nearLinks n c w` are the crossing links with both ends within `w` sites of the cut. A site
  `i` with `i + k + w ≤ c + 1` cannot tell any two configurations of `nearLinks` apart for `k`
  steps (`horizon_hides`).
* So the information hidden from `i` is the entropy of `D16g` on `nearLinks`: there are
  `C(M_w, m)` configurations of `m` links, all read identically at `i`, each carrying the
  defect `m δ_∞` (`hidden_configurations`).

The hiding lasts while the cone has not reached the cut; it is the finite-time horizon of
`D37f`, not a black hole.

## Main results

- `CutHorizon.links_unseen` : a set of links is unseen outside the cone of its ends.
- `CutHorizon.nearLinks_nonempty` : the window holds a link from `w = 2`.
- `CutHorizon.horizon_hides` : two configurations near the cut look the same from afar.
- `CutHorizon.hidden_configurations` : what is hidden, how much, and its defect.
-/

@[expose] public noncomputable section

open SimpleGraph TransportPosition LightCone DefectCycle CutEntropy CutCycles

namespace CutHorizon

/-- The ends of the links of `S`. -/
def ends {m : ℕ} (S : Finset (Fin m × Fin m)) : Set (Fin m) :=
  {a | ∃ p ∈ S, a = p.1 ∨ a = p.2}

/-- `T_d` with amplitude `ε` on every link of `S`. -/
def linksMatrix {m : ℕ} (S : Finset (Fin m × Fin m)) (ε : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Td m + Matrix.of fun i j => if (i, j) ∈ S ∨ (j, i) ∈ S then ε else 0

theorem linksMatrix_row {m : ℕ} (S : Finset (Fin m × Fin m)) (ε : ℂ) (p : Fin m)
    (hp : p ∉ ends S) : linksMatrix S ε p = Td m p := by
  funext j
  have h1 : (p, j) ∉ S := fun h => hp ⟨(p, j), h, Or.inl rfl⟩
  have h2 : (j, p) ∉ S := fun h => hp ⟨(j, p), h, Or.inr rfl⟩
  simp [linksMatrix, h1, h2]

/-- **A set of links is unseen outside the cone of its ends.** -/
theorem links_unseen {m : ℕ} (S : Finset (Fin m × Fin m)) (ε : ℂ) (k : ℕ) (i : Fin m)
    (hi : ∀ a ∈ ends S, k ≤ distPath i a) (ψ : Hd m) :
    Matrix.toEuclideanLin (linksMatrix S ε ^ k) ψ i =
      Matrix.toEuclideanLin (Td m ^ k) ψ i :=
  DefectPropagation.change_unseen _ (ends S) (linksMatrix_row S ε) k i hi ψ

/-- The crossing links with both ends within `w` sites of the cut. -/
def nearLinks (n c w : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  (crossLinks n c).filter fun p => c + 1 ≤ p.1.val + w ∧ p.2.val ≤ c + w

theorem nearLinks_subset (n c w : ℕ) : nearLinks n c w ⊆ crossLinks n c :=
  Finset.filter_subset _ _

/-- From `w = 2` the window is not empty: it holds the link `{c − 1, c + 1}`. -/
theorem nearLinks_nonempty {n c w : ℕ} (hc : 1 ≤ c) (hcn : c + 1 ≤ n) (hw : 2 ≤ w) :
    (nearLinks n c w).Nonempty :=
  ⟨(⟨c - 1, by omega⟩, ⟨c + 1, by omega⟩), by
    simp only [nearLinks, Finset.mem_filter, mem_crossLinks]
    omega⟩

/-- A site far to the left is outside the cone of every end of `nearLinks`. -/
theorem far_of_near {n c w k : ℕ} {S : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ⊆ nearLinks n c w) {i : Fin (n + 1)} (hi : i.val + k + w ≤ c + 1) :
    ∀ a ∈ ends S, k ≤ distPath i a := by
  rintro a ⟨p, hp, ha⟩
  have hpn := hS hp
  simp only [nearLinks, Finset.mem_filter, mem_crossLinks] at hpn
  unfold distPath
  rcases ha with rfl | rfl <;> omega

/-- **The horizon hides the configuration.** Two sets of links near the cut give the same
amplitude at a far site for `k` steps, for every state. -/
theorem horizon_hides {n c w k : ℕ} {S S' : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ⊆ nearLinks n c w) (hS' : S' ⊆ nearLinks n c w) (ε : ℂ) {i : Fin (n + 1)}
    (hi : i.val + k + w ≤ c + 1) (ψ : Hd (n + 1)) :
    Matrix.toEuclideanLin (linksMatrix S ε ^ k) ψ i =
      Matrix.toEuclideanLin (linksMatrix S' ε ^ k) ψ i := by
  rw [links_unseen S ε k i (far_of_near hS hi), links_unseen S' ε k i (far_of_near hS' hi)]

/-- **What the horizon hides.** For `m` links near the cut and a site `i` with
`i + k + w ≤ c + 1`: every configuration reads as `T_d^k` at `i`, each carries the defect
`m δ_∞`, and there are `C(M_w, m)` of them, whose logarithm is the entropy of `D16g`. -/
theorem hidden_configurations {n c w k m : ℕ} (ε : ℂ) {i : Fin (n + 1)}
    (hi : i.val + k + w ≤ c + 1) (ψ : Hd (n + 1)) :
    (∀ S ∈ (nearLinks n c w).powersetCard m,
      Matrix.toEuclideanLin (linksMatrix S ε ^ k) ψ i =
          Matrix.toEuclideanLin (Td (n + 1) ^ k) ψ i ∧
        Gnomon.cycleDefectSum (cycleRank (linksGraph n S)) (fun _ => Gnomon.deltaInf) =
          defect m) ∧
      ((nearLinks n c w).powersetCard m).card = (nearLinks n c w).card.choose m := by
  refine ⟨fun S hS => ⟨?_, ?_⟩, Finset.card_powersetCard _ _⟩
  · exact links_unseen S ε k i (far_of_near (Finset.mem_powersetCard.mp hS).1 hi) ψ
  · have hS' := Finset.mem_powersetCard.mp hS
    exact defect_of_config (Finset.mem_powersetCard.mpr
      ⟨hS'.1.trans (nearLinks_subset n c w), hS'.2⟩)

end CutHorizon

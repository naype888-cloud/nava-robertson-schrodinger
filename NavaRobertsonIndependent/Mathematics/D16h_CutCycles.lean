/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16g_CutEntropy

/-!
# D16h — The configurations of a cut are graphs with `k` new cycles

`D16g` counts configurations of `k` distinct crossing links. This module shows that each one
is a graph of transport with exactly `k` cycles, so the entropy of `D16g` counts graphs, not
labels.

* `linksGraph n S` is the path on `n + 1` positions with the links of `S`.
* For any set `S` of crossing links of one cut, its cycle rank is `|S|`
  (`cycleRank_linksGraph`): distinct crossing links never repeat an edge, and no crossing link
  is an edge of the path.
* So every configuration counted by `simpleEntropy n c k` carries the defect `k δ_∞`
  (`defect_of_config`), and `simpleEntropy` is the logarithm of the number of graphs of
  transport whose new cycles all cross the cut (`simpleEntropy_eq_log_card_graphs`).

## Main results

- `CutCycles.cycleRank_linksGraph` : `|S|` crossing links, cycle rank `|S|`.
- `CutCycles.defect_of_config` : each configuration carries `k δ_∞`.
- `CutCycles.simpleEntropy_eq_log_card_graphs` : the entropy counts graphs.
-/

@[expose] public noncomputable section

open SimpleGraph TransportPosition LightCone DefectCycle CutEntropy

namespace CutCycles

/-- The path on `n + 1` positions with the links of `S`. -/
def linksGraph (n : ℕ) (S : Finset (Fin (n + 1) × Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  graphTP (n + 1) ⊔ S.sup fun p => edge p.1 p.2

theorem linksGraph_connected (n : ℕ) (S : Finset (Fin (n + 1) × Fin (n + 1))) :
    (linksGraph n S).Connected :=
  (pathGraph_connected n).mono le_sup_left

theorem linksGraph_insert (n : ℕ) (S : Finset (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1) × Fin (n + 1)) :
    linksGraph n (insert p S) = linksGraph n S ⊔ edge p.1 p.2 := by
  simp only [linksGraph, Finset.sup_insert]
  ac_rfl

/-- An adjacency of the links of `S` is one of them. -/
theorem exists_of_adj_sup {m : ℕ} (S : Finset (Fin m × Fin m)) {u v : Fin m}
    (h : (S.sup fun p => edge p.1 p.2).Adj u v) :
    ∃ q ∈ S, (u = q.1 ∧ v = q.2) ∨ (u = q.2 ∧ v = q.1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at h
  | insert q S _ ih =>
    rw [Finset.sup_insert, sup_adj, edge_adj] at h
    rcases h with ⟨hq, -⟩ | h
    · exact ⟨q, Finset.mem_insert_self _ _, hq⟩
    · obtain ⟨r, hr, hr'⟩ := ih h
      exact ⟨r, Finset.mem_insert_of_mem hr, hr'⟩

/-- A crossing link outside `S` is not yet an edge. -/
theorem not_adj_of_cross {n c : ℕ} {S : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ⊆ crossLinks n c) {p : Fin (n + 1) × Fin (n + 1)} (hp : p ∈ crossLinks n c)
    (hpS : p ∉ S) : ¬ (linksGraph n S).Adj p.1 p.2 := by
  rw [linksGraph, sup_adj]
  rintro (h | h)
  · exact absurd h (not_adj_of_far (two_le_distPath_of_mem hp))
  · obtain ⟨q, hq, ⟨h1, h2⟩ | ⟨h1, -⟩⟩ := exists_of_adj_sup S h
    · exact hpS (by rw [Prod.ext h1 h2]; exact hq)
    · have hp' := mem_crossLinks.mp hp
      have hq' := mem_crossLinks.mp (hS hq)
      have := congrArg Fin.val h1
      omega

/-- **`|S|` crossing links, cycle rank `|S|`.** -/
theorem cycleRank_linksGraph {n c : ℕ} {S : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ⊆ crossLinks n c) : cycleRank (linksGraph n S) = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [linksGraph] using cycleRank_graphTP n
  | insert p S hpS ih =>
    have hSs : S ⊆ crossLinks n c := (Finset.subset_insert p S).trans hS
    have hp : p ∈ crossLinks n c := hS (Finset.mem_insert_self p S)
    have hne : p.1 ≠ p.2 := by
      intro h
      have := two_le_distPath_of_mem hp
      rw [h, distPath_self] at this
      omega
    rw [linksGraph_insert, cycleRank_sup_edge (linksGraph_connected n S)
      (not_adj_of_cross hSs hp hpS) hne, ih hSs, Finset.card_insert_of_notMem hpS]

/-- **Each configuration carries `k δ_∞`.** -/
theorem defect_of_config {n c k : ℕ} {S : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ∈ (crossLinks n c).powersetCard k) :
    Gnomon.cycleDefectSum (cycleRank (linksGraph n S)) (fun _ => Gnomon.deltaInf) =
      defect k := by
  rw [Finset.mem_powersetCard] at hS
  rw [Gnomon.cycleDefectSum_of_constant _ _ _ fun _ => rfl, cycleRank_linksGraph hS.1, hS.2,
    defect_eq]

/-- A crossing link of `S` is an edge of `linksGraph n S`. -/
theorem adj_of_mem {n c : ℕ} {S : Finset (Fin (n + 1) × Fin (n + 1))}
    {p : Fin (n + 1) × Fin (n + 1)} (hp : p ∈ crossLinks n c) (hpS : p ∈ S) :
    (linksGraph n S).Adj p.1 p.2 := by
  have hne : p.1 ≠ p.2 := by
    intro he
    have := two_le_distPath_of_mem hp
    rw [he, distPath_self] at this
    omega
  rw [linksGraph, sup_adj]
  exact Or.inr ((Finset.le_sup (f := fun p => edge p.1 p.2) hpS)
    (show (edge p.1 p.2).Adj p.1 p.2 by rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩))

/-- Different configurations give different graphs. -/
theorem linksGraph_injOn {n c : ℕ} :
    Set.InjOn (linksGraph n) {S | S ⊆ crossLinks n c} := by
  intro S hS T hT h
  ext p
  constructor
  · intro hp
    by_contra hpT
    exact not_adj_of_cross hT (hS hp) hpT (h ▸ adj_of_mem (hS hp) hp)
  · intro hp
    by_contra hpS
    exact not_adj_of_cross hS (hT hp) hpS (h ▸ adj_of_mem (hT hp) hp)

open Classical in
/-- **The entropy counts graphs:** `simpleEntropy n c k` is the logarithm of the number of
graphs of transport made of the path and `k` links across the cut. -/
theorem simpleEntropy_eq_log_card_graphs (n c k : ℕ) :
    simpleEntropy n c k =
      Real.log (((crossLinks n c).powersetCard k).image (linksGraph n)).card := by
  classical
  rw [simpleEntropy, Finset.card_image_of_injOn]
  intro S hS T hT h
  exact linksGraph_injOn (Finset.mem_powersetCard.mp hS).1 (Finset.mem_powersetCard.mp hT).1 h

end CutCycles

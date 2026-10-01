/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16c_DefectExcitation
public import NavaRobertsonIndependent.Mathematics.D16d_DefectPropagation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# D16e — Cycles come from non-local links

`D16c` counts cycles; `D16d` shows that a local change of transport stays inside the cone. This
module connects them on the graph of `T_d`.

* The path `graphTP (n + 1)` has `n` edges and is a tree: cycle rank `0`
  (`card_edgeSet_pathGraph`, `graphTP_isTree`).
* Adding a link `{a, b}` creates a cycle exactly when the link is not local, `2 ≤ |a − b|`
  (`withLink_isAcyclic_iff`). The path is the only local complete graph (`D3`), so every cycle
  of transport costs locality.
* Every new link raises the cycle rank `|E| + 1 − |V|` by one (`cycleRank_sup_edge`), and so the
  defect `cycleRank · q` by one quantum `q`. Two links give the step `2q` of `D16c`
  (`two_links_step`).
* The transport with a link `{a, b}` differs from `T_d` only on the rows `a` and `b`, so `D16d`
  applies: the new cycle is unseen at `i` for `k` steps while `k ≤ |i − a|` and `k ≤ |i − b|`
  (`link_unseen`).

Identifying the cycle rank of the graph with `b₁` of the surface of `D16`, and so with its
curvature under `HGaussBonnet`, is a premise; it is not proved here.

## Main results

- `DefectCycle.graphTP_isTree` : the path has no cycle.
- `DefectCycle.withLink_isAcyclic_iff` : a link creates a cycle iff it is not local.
- `DefectCycle.cycleRank_sup_edge`, `DefectCycle.two_links_step` : one quantum per link.
- `DefectCycle.link_unseen` : the cycle travels inside the cone.
-/

@[expose] public noncomputable section

open SimpleGraph TransportPosition LightCone DefectExcitation

namespace DefectCycle

/-! ## 1. The path is a tree -/

theorem card_edgeSet_pathGraph (n : ℕ) : Nat.card (pathGraph (n + 1)).edgeSet = n := by
  have hbij : Nat.card (Fin n) = Nat.card (pathGraph (n + 1)).edgeSet := by
    refine Nat.card_eq_of_bijective (fun i : Fin n =>
      (⟨s(i.castSucc, i.succ), by simp [pathGraph_adj]⟩ : (pathGraph (n + 1)).edgeSet))
      ⟨fun i j h => ?_, ?_⟩
    · have h := congrArg Subtype.val h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h, h'⟩
      · exact Fin.castSucc_injective _ h
      · have := congrArg Fin.val h; have := congrArg Fin.val h'; simp at *; omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h u v =>
        rw [mem_edgeSet, pathGraph_adj] at he
        rcases he with h | h
        · exact ⟨⟨u.val, by omega⟩, Subtype.ext (Sym2.eq_iff.mpr
            (Or.inl ⟨Fin.ext rfl, Fin.ext (by simp only [Fin.val_succ]; omega)⟩))⟩
        · exact ⟨⟨v.val, by omega⟩, Subtype.ext (Sym2.eq_iff.mpr
            (Or.inr ⟨Fin.ext rfl, Fin.ext (by simp only [Fin.val_succ]; omega)⟩))⟩
  rw [← hbij, Nat.card_fin]

theorem graphTP_isTree (n : ℕ) : (graphTP (n + 1)).IsTree :=
  isTree_iff_connected_and_card.mpr ⟨pathGraph_connected n, by
    rw [card_edgeSet_pathGraph, Nat.card_fin]⟩

/-! ## 2. Cycle rank -/

/-- The cycle rank `|E| + 1 − |V|` of a graph on `Fin m`. -/
def cycleRank {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ := Nat.card G.edgeSet + 1 - m

theorem card_edgeSet_sup_edge {m : ℕ} (G : SimpleGraph (Fin m)) {s t : Fin m}
    (hn : ¬ G.Adj s t) (h : s ≠ t) :
    Nat.card (G ⊔ edge s t).edgeSet = Nat.card G.edgeSet + 1 := by
  classical
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card]
  convert card_edgeFinset_sup_edge (G := G) hn h

/-- A new edge in a connected graph raises the cycle rank by one. -/
theorem cycleRank_sup_edge {m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.Connected) {s t : Fin m}
    (hn : ¬ G.Adj s t) (h : s ≠ t) : cycleRank (G ⊔ edge s t) = cycleRank G + 1 := by
  have hle := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_fin] at hle
  unfold cycleRank
  rw [card_edgeSet_sup_edge G hn h]
  omega

/-- A connected graph is a tree iff its cycle rank is `0`. -/
theorem isTree_iff_cycleRank {m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.Connected) :
    G.IsTree ↔ cycleRank G = 0 := by
  have hle := hG.card_vert_le_card_edgeSet_add_one
  rw [isTree_iff_connected_and_card, Nat.card_fin]
  rw [Nat.card_fin] at hle
  unfold cycleRank
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨hG, by omega⟩

theorem cycleRank_graphTP (n : ℕ) : cycleRank (graphTP (n + 1)) = 0 :=
  (isTree_iff_cycleRank (pathGraph_connected n)).mp (graphTP_isTree n)

/-! ## 3. A link creates a cycle iff it is not local -/

/-- The path with one more link `{a, b}`. -/
def withLink {n : ℕ} (a b : Fin (n + 1)) : SimpleGraph (Fin (n + 1)) := graphTP (n + 1) ⊔ edge a b

theorem withLink_connected {n : ℕ} (a b : Fin (n + 1)) : (withLink a b).Connected :=
  (pathGraph_connected n).mono le_sup_left

theorem not_adj_of_far {n : ℕ} {a b : Fin (n + 1)} (h : 2 ≤ distPath a b) :
    ¬ (graphTP (n + 1)).Adj a b := by
  rw [graphTP_adj]; unfold distPath at h; omega

/-- A non-local link gives cycle rank exactly `1`. -/
theorem cycleRank_withLink {n : ℕ} {a b : Fin (n + 1)} (h : 2 ≤ distPath a b) :
    cycleRank (withLink a b) = 1 := by
  have hab : a ≠ b := by rintro rfl; rw [distPath_self] at h; omega
  rw [withLink, cycleRank_sup_edge (pathGraph_connected n) (not_adj_of_far h) hab,
    cycleRank_graphTP]

/-- **A link creates a cycle iff it is not local.** -/
theorem withLink_isAcyclic_iff {n : ℕ} {a b : Fin (n + 1)} (hab : a ≠ b) :
    (withLink a b).IsAcyclic ↔ distPath a b ≤ 1 := by
  constructor
  · intro hac
    by_contra hfar
    have ht : (withLink a b).IsTree := ⟨withLink_connected a b, hac⟩
    rw [isTree_iff_cycleRank (withLink_connected a b), cycleRank_withLink (by omega)] at ht
    omega
  · intro hnear
    have hadj : (graphTP (n + 1)).Adj a b := by
      rw [graphTP_adj]
      have : a.val ≠ b.val := Fin.val_ne_of_ne hab
      unfold distPath at hnear; omega
    rw [withLink, sup_edge_of_adj _ hadj]
    exact (graphTP_isTree n).isAcyclic

/-! ## 4. One quantum per link -/

/-- Two new links on a connected graph add `2q` to the defect, the step of `D16c`. -/
theorem two_links_step {m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.Connected) {s t u v : Fin m}
    (hst : ¬ G.Adj s t) (hst' : s ≠ t) (huv : ¬ (G ⊔ edge s t).Adj u v) (huv' : u ≠ v)
    (q : ℝ) (g : ℕ) :
    Gnomon.cycleDefectSum (cycleRank (G ⊔ edge s t ⊔ edge u v)) (fun _ => q) -
        Gnomon.cycleDefectSum (cycleRank G) (fun _ => q) =
      defectWith q (g + 1) - defectWith q g := by
  have hG' : (G ⊔ edge s t).Connected := hG.mono le_sup_left
  rw [cycleRank_sup_edge hG' huv huv', cycleRank_sup_edge hG hst hst', defectWith_step,
    Gnomon.cycleDefectSum_of_constant _ _ q fun _ => rfl,
    Gnomon.cycleDefectSum_of_constant _ _ q fun _ => rfl]
  push_cast
  ring

/-! ## 5. The cycle travels inside the cone -/

/-- `T_d` with a link of amplitude `ε` between `a` and `b`. -/
def linkMatrix {d : ℕ} (a b : Fin d) (ε : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Td d + Matrix.of fun i j => if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then ε else 0

theorem linkMatrix_row {d : ℕ} (a b : Fin d) (ε : ℂ) (p : Fin d)
    (hp : p ∉ ({a, b} : Set (Fin d))) : linkMatrix a b ε p = Td d p := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp
  funext q
  simp [linkMatrix, hp.1, hp.2]

/-- **The new cycle is unseen outside the cone.** -/
theorem link_unseen {d : ℕ} (a b : Fin d) (ε : ℂ) (k : ℕ) (i : Fin d)
    (ha : k ≤ distPath i a) (hb : k ≤ distPath i b) (ψ : Hd d) :
    Matrix.toEuclideanLin (linkMatrix a b ε ^ k) ψ i =
      Matrix.toEuclideanLin (Td d ^ k) ψ i := by
  refine DefectPropagation.change_unseen _ {a, b} (linkMatrix_row a b ε) k i ?_ ψ
  intro c hc
  rcases hc with rfl | rfl
  · exact ha
  · exact hb

end DefectCycle

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16e_DefectCycle

/-!
# D16f — The path with `2g` links carries the defect of `Σ_g`

`D16` defines the defect of `Σ_g` as `δ_∞` on each of `b₁ = 2g` cycles; `D16e` shows that each
non-local link of the path adds one cycle. This module builds the graph that realizes `b₁ = 2g`.

* `handleGraph n k` is the path on `n + 1` sites with the `k` links `{0, j + 2}`, `j < k`. Every
  link is non-local (`two_le_distPath_link`) and new (`not_adj_link`).
* Its cycle rank is exactly `k` for `k + 1 ≤ n` (`cycleRank_handleGraph`).
* With `k = 2g` and quantum `δ_∞`, its defect is the defect of `Σ_g` of `D16`
  (`handleGraph_defect`); under `HGaussBonnet` it fixes the total curvature of `Σ_g`
  (`handleGraph_curvature`). One more handle is two more links and the step `2δ_∞` of `D16c`
  (`handleGraph_step`).

So the number of cycles of `D16` is no longer an input: it is the cycle rank of an explicit
graph of transport. What remains declared is `HGaussBonnet` and the classical fact that `Σ_g`
has a cell structure whose `1`-skeleton has `2g` independent cycles.

## Main results

- `HandleGraph.cycleRank_handleGraph` : `k` links, cycle rank `k`.
- `HandleGraph.handleGraph_defect` : `2g` links carry `Ω(Σ_g) = 2g δ_∞`.
- `HandleGraph.handleGraph_curvature` : the graph fixes `∫K dA` of `Σ_g`.
- `HandleGraph.handleGraph_step` : one handle, two links, `2δ_∞`.
-/

@[expose] public noncomputable section

open SimpleGraph TransportPosition LightCone DefectCycle

namespace HandleGraph

/-- The far end `j + 2` of the `j`-th link. -/
def link (n j : ℕ) : Fin (n + 1) := ⟨(j + 2) % (n + 1), Nat.mod_lt _ n.succ_pos⟩

theorem link_val {n j : ℕ} (h : j + 2 ≤ n) : (link n j).val = j + 2 :=
  Nat.mod_eq_of_lt (by omega)

/-- The path on `n + 1` sites with the links `{0, j + 2}` for `j < k`. -/
def handleGraph (n : ℕ) : ℕ → SimpleGraph (Fin (n + 1))
  | 0 => graphTP (n + 1)
  | k + 1 => handleGraph n k ⊔ edge 0 (link n k)

theorem handleGraph_connected (n k : ℕ) : (handleGraph n k).Connected := by
  induction k with
  | zero => exact pathGraph_connected n
  | succ k ih => exact ih.mono le_sup_left

/-- Every link is non-local. -/
theorem two_le_distPath_link {n j : ℕ} (h : j + 2 ≤ n) : 2 ≤ distPath 0 (link n j) := by
  unfold distPath
  rw [link_val h]
  simp

/-- The `k`-th link is not yet in the graph with `i ≤ k` links. -/
theorem not_adj_link {n k : ℕ} (h : k + 2 ≤ n) :
    ∀ i ≤ k, ¬ (handleGraph n i).Adj 0 (link n k) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [handleGraph, graphTP_adj, link_val h]
    simp
  | succ i ih =>
    intro hi
    rw [handleGraph, sup_adj, edge_adj]
    rintro (hadj | ⟨⟨-, heq⟩ | ⟨h0, -⟩, -⟩)
    · exact ih (by omega) hadj
    · have := congrArg Fin.val heq
      rw [link_val h, link_val (by omega)] at this
      omega
    · have := congrArg Fin.val h0
      rw [link_val (by omega)] at this
      simp at this

theorem link_ne_zero {n j : ℕ} (h : j + 2 ≤ n) : (0 : Fin (n + 1)) ≠ link n j := by
  intro h0
  have := congrArg Fin.val h0
  rw [link_val h] at this
  simp at this

/-- **`k` links, cycle rank `k`.** -/
theorem cycleRank_handleGraph {n k : ℕ} (h : k + 1 ≤ n) : cycleRank (handleGraph n k) = k := by
  induction k with
  | zero => exact cycleRank_graphTP n
  | succ k ih =>
    rw [handleGraph, cycleRank_sup_edge (handleGraph_connected n k)
      (not_adj_link (by omega) k le_rfl) (link_ne_zero (by omega)), ih (by omega)]

/-- **The path with `2g` links carries the defect of `Σ_g`.** -/
theorem handleGraph_defect {n g : ℕ} (h : 2 * g + 1 ≤ n) :
    Gnomon.cycleDefectSum (cycleRank (handleGraph n (2 * g))) (fun _ => Gnomon.deltaInf) =
      Gnomon.closedSurfaceDefect g := by
  rw [Gnomon.cycleDefectSum_of_constant _ _ Gnomon.deltaInf fun _ => rfl,
    cycleRank_handleGraph h, Gnomon.closedSurfaceDefect_eq_firstBetti_mul]

/-- **The graph fixes the curvature of `Σ_g`** under `HGaussBonnet`. -/
theorem handleGraph_curvature (H : Gnomon.HGaussBonnet) {n g : ℕ} (h : 2 * g + 1 ≤ n) :
    H.totalCurvature g = 4 * Real.pi - (2 * Real.pi / Gnomon.deltaInf) *
      Gnomon.cycleDefectSum (cycleRank (handleGraph n (2 * g))) (fun _ => Gnomon.deltaInf) := by
  rw [handleGraph_defect h, H.totalCurvature_of_defect]

/-- **One handle, two links, `2δ_∞`.** -/
theorem handleGraph_step {n g : ℕ} (h : 2 * g + 3 ≤ n) :
    Gnomon.cycleDefectSum (cycleRank (handleGraph n (2 * (g + 1)))) (fun _ => Gnomon.deltaInf) -
        Gnomon.cycleDefectSum (cycleRank (handleGraph n (2 * g))) (fun _ => Gnomon.deltaInf) =
      2 * Gnomon.deltaInf := by
  rw [handleGraph_defect h, handleGraph_defect (by omega),
    Gnomon.closedSurfaceDefect_eq_two_mul_genus_mul,
    Gnomon.closedSurfaceDefect_eq_two_mul_genus_mul]
  push_cast
  ring

end HandleGraph

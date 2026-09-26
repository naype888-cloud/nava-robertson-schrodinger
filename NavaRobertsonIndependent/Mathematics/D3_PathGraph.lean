/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D0_Habitat
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# D3 — Transport and position on the path graph

The support is Mathlib's `SimpleGraph.pathGraph d`: `d` vertices, edges between consecutive
ones. On it, `T_d = A_d / ρ_d` (transport, supported on the edges, `ρ_d = 2 cos(π/(d+1))`) and
`P_d` (position, diagonal, coordinates centred in `[-1, 1]`).

The path graph is forced: a graph on `Fin d` whose edges are minimal steps (ordered locality)
and which contains every minimal step (completeness) is `pathGraph d` (`graph_eq_pathGraph`).

## Main results

- `minStep_iff_adj` : minimal steps are the edges of `pathGraph d`.
- `Td_eq_zero_of_not_adj`, `Pd_eq_zero_offdiag` : `T_d` lives on edges, `P_d` is diagonal.
- `PathUniqueness.graph_eq_pathGraph` : ordered locality and completeness force the path.
-/

@[expose] public section

namespace TransportPosition

open SimpleGraph

/-- The graph of the transport–position channel: `pathGraph d`. -/
abbrev graphTP (d : ℕ) : SimpleGraph (Fin d) :=
  SimpleGraph.pathGraph d

/-- Adjacency on the path is a step of one site. -/
theorem graphTP_adj {d : ℕ} {i j : Fin d} :
    (graphTP d).Adj i j ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simpa [graphTP] using
    (SimpleGraph.pathGraph_adj (n := d) (u := i) (v := j))

/-- The minimal step `|i − j| = 1`, decidable. -/
def MinStep {d : ℕ} (i j : Fin d) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance minStep_decidable {d : ℕ} (i j : Fin d) :
    Decidable (MinStep i j) := by
  unfold MinStep
  infer_instance

/-- Minimal steps are the edges of `pathGraph d`. -/
theorem minStep_iff_adj {d : ℕ} {i j : Fin d} :
    MinStep i j ↔ (graphTP d).Adj i j := by
  rw [graphTP_adj]
  rfl

/-- The support of `T_d`, `P_d` is `pathGraph d`. -/
theorem graphTP_iso_pathGraph (d : ℕ) :
    Nonempty (graphTP d ≃g SimpleGraph.pathGraph d) := by
  change Nonempty (SimpleGraph.pathGraph d ≃g SimpleGraph.pathGraph d)
  exact ⟨SimpleGraph.Iso.refl⟩

/-- The adjacency matrix `A_d`. -/
noncomputable def Ad (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if MinStep i j then 1 else 0

/-- `ρ_d = 2 cos(π/(d+1))`, the spectral radius of `A_d`. -/
noncomputable def rho (d : ℕ) : ℝ :=
  2 * Real.cos (Real.pi / ((d : ℝ) + 1))

/-- Transport `T_d = A_d / ρ_d`. -/
noncomputable def Td (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Ad d i j / (rho d : ℂ)

/-- The position of site `j`, centred in `[-1, 1]`. -/
noncomputable def posCoord (d : ℕ) (j : Fin d) : ℝ :=
  (2 * ((j.val : ℝ) + 1) - ((d : ℝ) + 1)) / ((d : ℝ) - 1)

/-- Position `P_d`, diagonal. -/
noncomputable def Pd (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j then (posCoord d i : ℂ) else 0

theorem Ad_eq_one_iff {d : ℕ} {i j : Fin d} :
    Ad d i j = 1 ↔ (graphTP d).Adj i j := by
  unfold Ad
  rw [← minStep_iff_adj]
  by_cases h : MinStep i j
  · simp [h]
  · simp [h]

theorem Td_eq_zero_of_not_adj {d : ℕ} {i j : Fin d}
    (h : ¬ (graphTP d).Adj i j) :
    Td d i j = 0 := by
  have hpaso : ¬ MinStep i j := by
    intro hp
    exact h (minStep_iff_adj.mp hp)
  simp [Td, Ad, hpaso]

/-- `P_d` is diagonal. -/
theorem Pd_eq_zero_offdiag {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    Pd d i j = 0 := by
  simp [Pd, hij]

/-- The diagonal of `P_d` is the site position. -/
theorem Pd_diag {d : ℕ} (i : Fin d) :
    Pd d i i = (posCoord d i : ℂ) := by
  simp [Pd]

end TransportPosition

/-!
## Why `pathGraph d`

A local channel (every edge is a minimal step) that is complete (every minimal step is an
edge) is `pathGraph d`: removing an edge breaks completeness.
-/

namespace PathUniqueness

open SimpleGraph

/-- Ordered locality: every edge is a minimal step. -/
def OrderedLocality {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {i j : Fin d}, G.Adj i j → TransportPosition.MinStep i j

/-- Completeness: every minimal step is an edge. -/
def CompleteSteps {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∀ {i j : Fin d}, TransportPosition.MinStep i j → G.Adj i j

/-- The graph omits a minimal step. -/
def OmitsStep {d : ℕ} (G : SimpleGraph (Fin d)) : Prop :=
  ∃ i j : Fin d, TransportPosition.MinStep i j ∧ ¬ G.Adj i j

/-- A local, complete channel on `Fin d`. -/
structure LocalChannel (d : ℕ) where
  graph : SimpleGraph (Fin d)
  ordered_locality : OrderedLocality graph
  complete_steps : CompleteSteps graph

/-- In a local channel, adjacency is the minimal step. -/
theorem LocalChannel.adj_iff_minStep
    {d : ℕ} (C : LocalChannel d) {i j : Fin d} :
    C.graph.Adj i j ↔ TransportPosition.MinStep i j := by
  exact ⟨fun h => C.ordered_locality h,
    fun h => C.complete_steps h⟩

/-- **Uniqueness of the path.** A local, complete channel is `pathGraph d`. -/
theorem graph_eq_pathGraph
    {d : ℕ} (C : LocalChannel d) :
    C.graph = SimpleGraph.pathGraph d := by
  ext i j
  rw [C.adj_iff_minStep]
  simpa [TransportPosition.graphTP] using
    (TransportPosition.minStep_iff_adj (d := d) (i := i) (j := j))

/-- The same, as a graph isomorphism. -/
theorem graph_iso_pathGraph
    {d : ℕ} (C : LocalChannel d) :
    Nonempty (C.graph ≃g SimpleGraph.pathGraph d) := by
  rw [graph_eq_pathGraph C]
  exact ⟨SimpleGraph.Iso.refl⟩

/-- The channel of `T_d`, `P_d` is local and complete. -/
def localChannelTP (d : ℕ) :
    LocalChannel d where
  graph := TransportPosition.graphTP d
  ordered_locality := by
    intro i j h
    exact (TransportPosition.minStep_iff_adj
      (d := d) (i := i) (j := j)).mpr h
  complete_steps := by
    intro i j h
    exact (TransportPosition.minStep_iff_adj
      (d := d) (i := i) (j := j)).mp h

/-- A local channel omits no minimal step. -/
theorem not_omitsStep
    {d : ℕ} (C : LocalChannel d) :
    ¬ OmitsStep C.graph := by
  rintro ⟨i, j, hpaso, hno⟩
  exact hno (C.complete_steps hpaso)

/-- The channel of `T_d`, `P_d` is `pathGraph d` and omits no minimal step. -/
theorem localChannelTP_minimal (d : ℕ) :
    (localChannelTP d).graph = SimpleGraph.pathGraph d ∧
      ¬ OmitsStep (localChannelTP d).graph := by
  exact ⟨graph_eq_pathGraph
      (localChannelTP d),
    not_omitsStep
      (localChannelTP d)⟩

end PathUniqueness

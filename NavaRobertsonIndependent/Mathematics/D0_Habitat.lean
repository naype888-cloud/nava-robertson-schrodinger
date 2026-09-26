/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# D0 — The finite Hilbert space `H_d`

Everything takes place in `H_d = ℂ^d` with its standard inner product. `d = ∞` is never a
space of the family, only a limit of `{H_d}` (`D8`).
-/

@[expose] public section

namespace TransportPosition

/-- The Hilbert space `H_d = ℂ^d`. -/
abbrev Hd (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- `H_d` is `EuclideanSpace ℂ (Fin d)` by definition. -/
theorem Hd_eq_euclidean (d : ℕ) :
    Hd d = EuclideanSpace ℂ (Fin d) := rfl

end TransportPosition

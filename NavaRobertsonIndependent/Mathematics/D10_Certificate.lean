/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D6_Fiedler
public import NavaRobertsonIndependent.Mathematics.D7_Niven
public import NavaRobertsonIndependent.Mathematics.D8_Szego
public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!
# D10 — Joint certificate: Fiedler, Niven, Szegő on `H_d`

One certificate for the results that rest on `H_d = ℂ^d` (`D0`): the spectrum of the path and
its Fiedler vector (`D6`), Niven (`D7`), the Szegő limit with the positivity of the gap (`D8`)
and monotonicity (`D9`). Saturation happens only at `d ∈ {2, 3}`; for every `d ≥ 4` the gap is
at least `δ(4)`, and as `d` grows it converges to `δ_∞ > 0`. `d = ∞` is only that limit.

## Main results

- `HdCertificate.certificate` : the joint certificate is inhabited.
- `HdCertificate.lt_geometricGap_of_lt_four` : no gap in `d ≥ 4` is below `δ(4)`.
-/

@[expose] public noncomputable section

open Real
open Filter
open scoped Topology

namespace HdCertificate

open TransportPosition
open Gnomon

/-! ## The space `H_d` -/

def FiniteHabitat (d : ℕ) : Prop :=
  Hd d = EuclideanSpace ℂ (Fin d)

theorem finiteHabitat (d : ℕ) : FiniteHabitat d :=
  Hd_eq_euclidean d

theorem deltaInf_is_limit_of_Hd :
    Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      deltaInf = CoherenceConstantInf - 1 ∧
      0 < deltaInf :=
  deltaInf_is_limit

/-! ## Niven: no saturation from `d = 4` -/

theorem niven_saturation_iff (d : ℕ) (hd : 2 ≤ d) :
    cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3 :=
  saturation_iff d hd

/-- No saturation for `d ≥ 4`. -/
theorem niven_not_saturated (d : ℕ) (hd : 4 ≤ d) :
    cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 :=
  not_saturated_of_four_le d hd

theorem niven_geometricGap_pos (d : ℕ) (hd : 4 ≤ d) :
    0 < geometricGap d :=
  geometricGap_pos_of_four_le d hd

theorem geometricGap_four_le_of_Hd (d : ℕ) (hd : 4 ≤ d) :
    geometricGap 4 ≤ geometricGap d :=
  geometricGap_four_le d hd

/-- For `d ≥ 4` every gap is above any `ε < δ(4)`. -/
theorem lt_geometricGap_of_lt_four
    (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : ε < geometricGap 4) :
    ε < geometricGap d :=
  lt_of_lt_of_le hε (geometricGap_four_le_of_Hd d hd)

/-! ## Fiedler: spectrum of `K_d` on `H_d` -/

theorem fiedler_eigenvector_Hd (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (fiedlerVec d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • fiedlerVec d :=
  KdOp_fiedlerVec d hd

theorem fiedler_specRadius (d : ℕ) (hd : 2 ≤ d) :
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    letI : Nontrivial (Hd d) := inferInstance
    SpectralExtremal.specRadius (KdOp d) (KdOp_isSymmetric d) =
      2 / ((d : ℝ) - 1) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (Hd d) := inferInstance
  exact specRadius_KdOp_eq_step d hd

/-! ## Szegő: the limit of the finite family -/

theorem szego_limit_family :
    Tendsto CoherenceConstant atTop (𝓝 CoherenceConstantInf) :=
  tendsto_CoherenceConstant

theorem szego_deltaInf_pos : 0 < deltaInf :=
  deltaInf_pos

theorem geometricGap_pos_and_tendsto :
    (∀ d : ℕ, 4 ≤ d → 0 < geometricGap d) ∧
      Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      0 < deltaInf :=
  ⟨niven_geometricGap_pos, tendsto_geometricGap, szego_deltaInf_pos⟩

/-! ## The joint certificate -/

structure Certificate where
  habitat : ∀ d : ℕ, FiniteHabitat d
  niven_iff :
    ∀ d : ℕ, 2 ≤ d →
      (cos (π / ((d : ℝ) + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3)
  niven_not_saturated_of_four_le :
    ∀ d : ℕ, 4 ≤ d →
      cos (π / ((d : ℝ) + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4
  geometricGap_pos : ∀ d : ℕ, 4 ≤ d → 0 < geometricGap d
  geometricGap_floor : ∀ d : ℕ, 4 ≤ d → geometricGap 4 ≤ geometricGap d
  fiedler_eigenvector :
    ∀ d : ℕ, 2 ≤ d →
      KdOp d (fiedlerVec d) =
        ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • fiedlerVec d
  szego_limit : Tendsto CoherenceConstant atTop (𝓝 CoherenceConstantInf)
  szego_deltaInf : 0 < deltaInf
  gap_pos_and_limit :
    (∀ d : ℕ, 4 ≤ d → 0 < geometricGap d) ∧
      Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      0 < deltaInf
  infinity_is_limit :
    Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      deltaInf = CoherenceConstantInf - 1 ∧ 0 < deltaInf

theorem certificate : Nonempty Certificate :=
  ⟨{ habitat := finiteHabitat
     niven_iff := fun d hd => niven_saturation_iff d hd
     niven_not_saturated_of_four_le := fun d hd => niven_not_saturated d hd
     geometricGap_pos := fun d hd => niven_geometricGap_pos d hd
     geometricGap_floor := fun d hd => geometricGap_four_le_of_Hd d hd
     fiedler_eigenvector := fun d hd => fiedler_eigenvector_Hd d hd
     szego_limit := szego_limit_family
     szego_deltaInf := szego_deltaInf_pos
     gap_pos_and_limit := geometricGap_pos_and_tendsto
     infinity_is_limit := deltaInf_is_limit_of_Hd }⟩

end HdCertificate

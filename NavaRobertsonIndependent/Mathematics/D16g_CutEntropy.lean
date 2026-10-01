/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D16f_HandleGraph
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# D16g — The entropy of a cut counts its quanta

Cut the path on `n + 1` sites between `c` and `c + 1`. A crossing link joins `a ≤ c` to
`b > c` with `b − a ≥ 2`; there are `M` of them (`crossLinks`). Each one closes a cycle
(`crossLink_closes_cycle`, from `D16e`) and so carries one quantum `δ_∞` of defect (`D16f`).

* **Area law.** Let `k` distinguishable quanta cross the cut, each on one of the `M` crossing
  links. There are `M^k` configurations, so the entropy `log M^k` is proportional to the
  defect `k δ_∞` they carry: `S = (log M / δ_∞) Ω` (`entropy_eq_mul_defect`).
* **Simple links.** If the `k` links must be distinct, there are `C(M, k)` configurations and
  `log C(M, k) ≤ S` (`simpleEntropy_le_entropy`). Over all `k` the count is at most `2^M`:
  no configuration of the cut has more than `M log 2` (`simpleEntropy_le_max`).
* **The Bekenstein–Hawking bridge (declared).** If the defect has an area `A = a₀ Ω` and
  `S = A / (4 ℓ_P²)`, the area per unit of defect is forced: `a₀ = 4 ℓ_P² log M / δ_∞`
  (`HBekensteinHawking.areaPerDefect_eq`). The bridge is satisfiable
  (`hBekensteinHawking_satisfiable`).

The coefficient `log M` depends on the cut: `M` grows with the sizes of both sides. Lean does
not give the `1/4`; it is the declared bridge, as `HGaussBonnet` is for the curvature.

## Main results

- `CutEntropy.crossLink_closes_cycle` : every crossing link closes a cycle.
- `CutEntropy.entropy_eq_mul_defect` : `S = (log M / δ_∞) · Ω`.
- `CutEntropy.simpleEntropy_le_entropy`, `CutEntropy.simpleEntropy_le_max` : the bounds.
- `CutEntropy.HBekensteinHawking.areaPerDefect_eq` : the bridge fixes the area quantum.
-/

@[expose] public noncomputable section

open SimpleGraph TransportPosition LightCone DefectCycle

namespace CutEntropy

/-! ## 1. Crossing links -/

/-- The non-local links across the cut between `c` and `c + 1`. -/
def crossLinks (n c : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter fun p => p.1.val ≤ c ∧ c < p.2.val ∧ p.1.val + 2 ≤ p.2.val

/-- The number `M` of crossing links. -/
def numCross (n c : ℕ) : ℕ := (crossLinks n c).card

theorem mem_crossLinks {n c : ℕ} {p : Fin (n + 1) × Fin (n + 1)} :
    p ∈ crossLinks n c ↔ p.1.val ≤ c ∧ c < p.2.val ∧ p.1.val + 2 ≤ p.2.val := by
  simp [crossLinks]

theorem two_le_distPath_of_mem {n c : ℕ} {p : Fin (n + 1) × Fin (n + 1)}
    (hp : p ∈ crossLinks n c) : 2 ≤ distPath p.1 p.2 := by
  rw [mem_crossLinks] at hp
  unfold distPath
  omega

/-- **Every crossing link closes a cycle.** -/
theorem crossLink_closes_cycle {n c : ℕ} {p : Fin (n + 1) × Fin (n + 1)}
    (hp : p ∈ crossLinks n c) : ¬ (withLink p.1 p.2).IsAcyclic := by
  have h2 := two_le_distPath_of_mem hp
  have hne : p.1 ≠ p.2 := by
    intro h
    rw [h, distPath_self] at h2
    omega
  rw [withLink_isAcyclic_iff hne]
  omega

/-- A cut with at least two sites on the left and one on the right has a crossing link. -/
theorem one_le_numCross {n c : ℕ} (hc : 1 ≤ c) (hcn : c + 1 ≤ n) : 1 ≤ numCross n c := by
  unfold numCross
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  exact ⟨(⟨0, by omega⟩, ⟨c + 1, by omega⟩), by rw [mem_crossLinks]; simp; omega⟩

/-! ## 2. Entropy of distinguishable quanta -/

/-- `k` distinguishable quanta, each on a crossing link. -/
abbrev Config (n c k : ℕ) := Fin k → crossLinks n c

/-- The entropy `log #configurations`. -/
def entropy (n c k : ℕ) : ℝ := Real.log (Fintype.card (Config n c k))

/-- The defect `k δ_∞` carried by `k` quanta. -/
def defect (k : ℕ) : ℝ := Gnomon.cycleDefectSum k fun _ => Gnomon.deltaInf

theorem card_config (n c k : ℕ) : Fintype.card (Config n c k) = numCross n c ^ k := by
  simp [Config, numCross]

theorem entropy_eq (n c k : ℕ) : entropy n c k = k * Real.log (numCross n c) := by
  rw [entropy, card_config]
  push_cast
  rw [Real.log_pow]

theorem defect_eq (k : ℕ) : defect k = k * Gnomon.deltaInf :=
  Gnomon.cycleDefectSum_of_constant _ _ _ fun _ => rfl

/-- **Area law: the entropy is proportional to the defect.** -/
theorem entropy_eq_mul_defect (n c k : ℕ) :
    entropy n c k = Real.log (numCross n c) / Gnomon.deltaInf * defect k := by
  rw [entropy_eq, defect_eq]
  field_simp [Gnomon.deltaInf_pos.ne']

/-! ## 3. Distinct links -/

/-- The entropy of `k` distinct crossing links. -/
def simpleEntropy (n c k : ℕ) : ℝ := Real.log ((crossLinks n c).powersetCard k).card

theorem simpleEntropy_eq (n c k : ℕ) :
    simpleEntropy n c k = Real.log ((numCross n c).choose k) := by
  rw [simpleEntropy, Finset.card_powersetCard, numCross]

/-- Distinct links never have more entropy than distinguishable quanta. -/
theorem simpleEntropy_le_entropy {n c k : ℕ} (hk : k ≤ numCross n c) :
    simpleEntropy n c k ≤ entropy n c k := by
  rw [simpleEntropy_eq, entropy, card_config]
  have hpos : (0 : ℝ) < (numCross n c).choose k := by exact_mod_cast Nat.choose_pos hk
  exact Real.log_le_log hpos (by exact_mod_cast Nat.choose_le_pow _ _)

/-- **No configuration of the cut has more than `M log 2`.** -/
theorem simpleEntropy_le_max {n c k : ℕ} (hk : k ≤ numCross n c) :
    simpleEntropy n c k ≤ numCross n c * Real.log 2 := by
  rw [simpleEntropy_eq, ← Real.log_pow]
  have hpos : (0 : ℝ) < (numCross n c).choose k := by exact_mod_cast Nat.choose_pos hk
  exact Real.log_le_log hpos (by exact_mod_cast Nat.choose_le_two_pow _ _)

/-! ## 4. The Bekenstein–Hawking bridge -/

/-- **Bekenstein–Hawking (declared hypothesis).** The defect of the cut has an area
`A = a₀ Ω`, and the entropy is `A / (4 ℓ_P²)`. -/
structure HBekensteinHawking (n c : ℕ) where
  areaPerDefect : ℝ
  planckArea : ℝ
  planckArea_pos : 0 < planckArea
  law : ∀ k, entropy n c k = areaPerDefect * defect k / (4 * planckArea)

/-- **The bridge fixes the area quantum:** `a₀ = 4 ℓ_P² log M / δ_∞`. -/
theorem HBekensteinHawking.areaPerDefect_eq {n c : ℕ} (H : HBekensteinHawking n c) :
    H.areaPerDefect = 4 * H.planckArea * Real.log (numCross n c) / Gnomon.deltaInf := by
  have h := H.law 1
  rw [entropy_eq, defect_eq] at h
  have hd := Gnomon.deltaInf_pos.ne'
  have hp := H.planckArea_pos.ne'
  field_simp at h ⊢
  linarith

theorem hBekensteinHawking_satisfiable (n c : ℕ) : Nonempty (HBekensteinHawking n c) :=
  ⟨{ areaPerDefect := 4 * Real.log (numCross n c) / Gnomon.deltaInf
     planckArea := 1
     planckArea_pos := one_pos
     law := fun k => by
       rw [entropy_eq, defect_eq]
       field_simp [Gnomon.deltaInf_pos.ne'] }⟩

end CutEntropy

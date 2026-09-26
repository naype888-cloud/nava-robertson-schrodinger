/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D28_BakryEmeryCurvature

/-!
# D28b — Ollivier–Ricci curvature of the path: `κ = 0` in the interior

By Kantorovich–Rubinstein duality, `W₁(μ, ν) = sup {E_μ f − E_ν f : f 1-Lipschitz}`. For the
uniform random walk on the path, the one-step laws from consecutive interior vertices are
`m_j = ½δ_{j−1} + ½δ_{j+1}` and `m_{j+1} = ½δ_j + ½δ_{j+2}`. The gap is computed directly:
the upper bound from the Lipschitz property, the lower bound from a witness. So `W₁ = 1 = d(j, j+1)`
and `κ(j, j+1) = 1 − W₁/d = 0`, as in `D28`.

## Main results

- `OllivierCurvature.W1_eq_one` : `W₁ = 1`, as an `IsGreatest`.
- `OllivierCurvature.kappaOllivier_eq_zero` : `κ = 0` on interior edges.
- `OllivierCurvature.bakryEmery_ollivier_agree` : both curvatures vanish on the path.
-/

@[expose] public noncomputable section

namespace OllivierCurvature

open TransportPosition BakryEmery

/-! ## The Kantorovich–Rubinstein gap on four points -/

/-- `f` is 1-Lipschitz along the steps `x−1 → x → x+1 → x+2`. -/
def Lip1Four (fm1 f0 fp1 fp2 : ℝ) : Prop :=
  |fm1 - f0| ≤ 1 ∧ |f0 - fp1| ≤ 1 ∧ |fp1 - fp2| ≤ 1

/-- The Kantorovich–Rubinstein gap `E_{m_x} f − E_{m_{x+1}} f`. -/
def gapKR (fm1 f0 fp1 fp2 : ℝ) : ℝ := (fm1 + fp1) / 2 - (f0 + fp2) / 2

/-- A 1-Lipschitz function has gap at most `1`. -/
theorem gapKR_le_one {fm1 f0 fp1 fp2 : ℝ} (h : Lip1Four fm1 f0 fp1 fp2) :
    gapKR fm1 f0 fp1 fp2 ≤ 1 := by
  obtain ⟨h1, _h2, h3⟩ := h
  unfold gapKR
  have e1 := abs_le.mp h1
  have e3 := abs_le.mp h3
  linarith [e1.1, e1.2, e3.1, e3.2]

theorem neg_one_le_gapKR {fm1 f0 fp1 fp2 : ℝ} (h : Lip1Four fm1 f0 fp1 fp2) :
    -1 ≤ gapKR fm1 f0 fp1 fp2 := by
  obtain ⟨h1, _h2, h3⟩ := h
  unfold gapKR
  have e1 := abs_le.mp h1
  have e3 := abs_le.mp h3
  linarith [e1.1, e1.2, e3.1, e3.2]

/-- The witness `f = (1, 0, −1, −2)` has gap `1`. -/
theorem gapKR_witness : gapKR 1 0 (-1) (-2) = 1 := by
  unfold gapKR; norm_num

theorem lip1Four_witness : Lip1Four 1 0 (-1) (-2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **`W₁ = 1`.** The supremum of the gap over 1-Lipschitz functions is `1`. -/
theorem W1_eq_one :
    IsGreatest
      {v : ℝ | ∃ fm1 f0 fp1 fp2 : ℝ, Lip1Four fm1 f0 fp1 fp2 ∧ gapKR fm1 f0 fp1 fp2 = v} 1 := by
  constructor
  · exact ⟨1, 0, -1, -2, lip1Four_witness, gapKR_witness⟩
  · rintro v ⟨fm1, f0, fp1, fp2, h, rfl⟩
    exact gapKR_le_one h

/-- The Ollivier–Ricci curvature of an edge, `κ = 1 − W₁/d`. -/
def kappaOllivier (W1 d : ℝ) : ℝ := 1 - W1 / d

/-- The Ollivier–Ricci curvature of an interior edge of the path is `0`. -/
theorem kappaOllivier_eq_zero : kappaOllivier 1 1 = 0 := by
  unfold kappaOllivier; norm_num

/-! ## The edge lies on the path -/

/-- The edge `(j, j+1)` is an edge of `graphTP d`. -/
theorem edge_adj_graphTP {d : ℕ} (j : Fin d) (h2 : j.val + 1 < d) :
    (graphTP d).Adj j (ip1 j h2) :=
  adj_ip1 j h2

/-- On every interior edge `(j, j+1)` of `graphTP d` with `1 ≤ j` and `j + 2 < d`, the
Ollivier–Ricci curvature is `0`, as the Bakry–Émery curvature of `D28`. -/
theorem bakryEmery_ollivier_agree {d : ℕ} (j : Fin d) (_h1 : 1 ≤ j.val)
    (h2 : j.val + 2 < d) :
    (graphTP d).Adj j (ip1 j (by omega)) ∧ kappaOllivier 1 1 = 0 :=
  ⟨edge_adj_graphTP j (by omega), kappaOllivier_eq_zero⟩

end OllivierCurvature

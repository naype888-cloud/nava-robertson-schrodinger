/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D45b_IntervalChecker

/-!
# D45c — From the checker to the packet

A half is checked either exactly, from its end, or truncated at depth `D` when it is deeper,
which makes one check valid for every `d` large enough. The weighted sum of a glued packet splits
into its two halves, and the Casoratian at the glue position is read from the first ratios.

## Main results

- `BandCertificate.half_sound` : the checked bound of a half sum, exact or truncated.
- `StarkPacket.spread_sub` : `X − K N` is the sum of the two half sums.
- `StarkPacket.casoratian_eq` : the Casoratian through the first ratios.
-/

@[expose] public noncomputable section

open Finset

namespace StarkPacket

variable {z c K : ℝ} {t : ℕ}

/-- The half sum `Σ_{m0 ≤ m ≤ t} ((m + c − t)² − K) A_{t−m}²`. -/
def halfSum (z c K : ℝ) (t m0 : ℕ) : ℝ :=
  ∑ m ∈ range (t + 1), if m0 ≤ m then ((m + (c - t)) ^ 2 - K) * seq z c (t - m) ^ 2 else 0

lemma halfSum_eq (hz : 0 < z) (hc : (t : ℝ) - 1 < c) (m0 : ℕ) :
    halfSum z c K t m0 =
      seq z c t ^ 2 * BandCertificate.wsum (ratio z c t) (c - t + 1) K m0 (t + 1) := by
  rw [halfSum, BandCertificate.wsum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [seq_eq_prod hz hc (by simpa [Nat.lt_succ_iff] using hm), BandCertificate.vprod,
    prod_pow]
  split_ifs <;> ring

end StarkPacket

namespace BandCertificate

open StarkPacket

variable {p : Half} {z c K : ℝ} {t : ℕ}

/-! ## A. Exact and truncated halves -/

/-- Exact (`none`) or truncated at depth `D` with `w` terms (`some (D, w)`). -/
abbrev Depth := Option (ℕ × ℕ)

/-- The top of the enclosure. -/
def top (t : ℕ) : Depth → ℕ
  | none => t
  | some (D, _) => D

/-- The enclosure of the ratio at the top. -/
def start (p : Half) : Depth → ℕ × ℕ
  | none => (0, 0)
  | some (D, _) => startTrunc p D

/-- The number of checked terms. -/
def nterms (t : ℕ) : Depth → ℕ
  | none => t + 1
  | some (_, w) => w

/-- The checked side conditions of a truncation. -/
def valid (p : Half) : Depth → Bool
  | none => true
  | some (D, w) => 1 ≤ w && w ≤ D && p.Kn * p.ud * p.ud ≤ wsq p w * p.Kd

/-- A truncated half is deeper than its truncation. -/
def Deep (t : ℕ) : Depth → Prop
  | none => True
  | some (D, _) => D < t

/-- The checked pair `(pos, neg)` of a half. -/
def half (p : Half) (t m0 : ℕ) (o : Depth) : ℕ × ℕ :=
  ((sums p (top t o) (start p o) m0 (nterms t o)).2.2.1,
    (sums p (top t o) (start p o) m0 (nterms t o)).2.2.2)

lemma kLo_pos (h0 : 0 < kLo p 0) (m : ℕ) : 0 < kLo p m :=
  h0.trans_le <| Nat.div_le_div_right <| by gcongr; omega

lemma top_lt (o : Depth) (hd : Deep t o) {m : ℕ} (hm : m < top t o) : m < t := by
  rcases o with _ | ⟨D, w⟩
  · exact hm
  · exact hm.trans hd

/-- The ratios of a half lie in their enclosures. -/
lemma ratio_mem (hp : Fits p z (c - t + 1) K) (hz : 0 < z) (hc : (t : ℝ) - 1 < c)
    (h0 : 0 < kLo p 0) (o : Depth) (hd : Deep t o) :
    ∀ m ≤ top t o, Mem (ivs p (top t o) (start p o) (top t o - m)) (ratio z c t m) := by
  have hrec : ∀ m < top t o, ratio z c t m =
      1 / (2 * (m + (c - t + 1)) / z + ratio z c t (m + 1)) := fun m hm =>
    ratio_rec hz hc (top_lt o hd hm)
  have hs : Mem (start p o) (ratio z c t (top t o)) := by
    rcases o with _ | ⟨D, w⟩
    · simp [start, top, Mem, ratio]
    · have hS := S_pos
      have hk := kLo_le hp D
      have hk0 : (0 : ℝ) < kLo p D := by exact_mod_cast kLo_pos h0 D
      refine ⟨by simpa [start, startTrunc, top] using ratio_nonneg hz hc D, ?_⟩
      rw [top, ratio_rec hz hc hd]
      calc 1 / (2 * (D + (c - t + 1)) / z + ratio z c t (D + 1))
          ≤ 1 / ((kLo p D : ℝ) / S) := one_div_le_one_div_of_le (by positivity)
            (by linarith [ratio_nonneg hz hc (D + 1)])
        _ = ((S * S : ℕ) : ℝ) / kLo p D / S := by push_cast; field_simp
        _ ≤ ((startTrunc p D).2 : ℝ) / S := by
            gcongr; exact le_cdiv _ (kLo_pos h0 D)
  intro m hm
  simpa [Nat.sub_sub_self hm] using ivs_sound hp (kLo_pos h0) hrec hs (top t o - m) (by omega)

/-- **The checked bound of a half sum.** -/
theorem half_sound (hp : Fits p z (c - t + 1) K) (hz : 0 < z) (hc : (t : ℝ) - 1 < c)
    (h0 : 0 < kLo p 0) (m0 : ℕ) (o : Depth) (hd : Deep t o) (hv : valid p o = true) :
    seq z c t ^ 2 * (((half p t m0 o).1 : ℝ) - (half p t m0 o).2) / S ≤
      halfSum z c K t m0 := by
  have hmem := ratio_mem hp hz hc h0 o hd
  have hn : nterms t o ≤ top t o + 1 := by
    rcases o with _ | ⟨D, w⟩
    · exact le_rfl
    · simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      simp only [nterms, top]
      omega
  have hsum := (sums_sound hp (ratio_nonneg hz hc) hmem (m0 := m0) _ hn).2
  have htail : wsum (ratio z c t) (c - t + 1) K m0 (nterms t o) ≤
      wsum (ratio z c t) (c - t + 1) K m0 (t + 1) := by
    rcases o with _ | ⟨D, w⟩
    · exact le_rfl
    · simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hw1, hwD⟩, hK⟩ := hv
      have hDt : D < t := hd
      rw [wsum, wsum, nterms, ← sum_range_add_sum_Ico _ (by omega : w ≤ t + 1),
        le_add_iff_nonneg_right]
      refine sum_nonneg fun m hm => ?_
      split_ifs
      · refine mul_nonneg ?_ (prod_nonneg fun _ _ => sq_nonneg _)
        have hw := wsq_le hp w
        have hud : (0 : ℝ) < p.ud := by exact_mod_cast hp.ud_pos
        have hKd : (0 : ℝ) < p.Kd := by exact_mod_cast hp.Kd_pos
        have hKw : K ≤ (wsq p w : ℝ) / p.ud ^ 2 := by
          rw [hp.hK, div_le_div_iff₀ hKd (by positivity)]
          exact_mod_cast (by nlinarith [hK] : p.Kn * p.ud ^ 2 ≤ wsq p w * p.Kd)
        have hm' : (w : ℝ) ≤ m := by exact_mod_cast (mem_Ico.mp hm).1
        have hu : 0 ≤ (w : ℝ) + (c - t + 1) - 1 := by
          have : (0 : ℝ) ≤ p.ulo / p.ud := by positivity
          have : (1 : ℝ) ≤ w := by exact_mod_cast hw1
          linarith [hp.hlo]
        nlinarith
      · exact le_rfl
  rw [halfSum_eq hz hc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hsum.trans htail) (sq_nonneg _)

end BandCertificate

namespace StarkPacket

/-! ## B. The packet through its halves -/

variable {d g : ℕ} {z c₀ K : ℝ}

/-- **`X − K N` splits into the two half sums.** -/
theorem spread_sub (hg : g < d) :
    spread d g z c₀ - K * normSq d g z c₀ =
      right d z c₀ g ^ 2 * halfSum z c₀ K g 0 +
        left z c₀ g ^ 2 * halfSum z ((d : ℝ) - 1 - c₀) K (d - 1 - g) 1 := by
  set t := d - 1 - g
  set f : ℕ → ℝ := fun j => (((j : ℝ) - c₀) ^ 2 - K) * phi d g z c₀ j ^ 2
  have hsplit := sum_range_add f (g + 1) t
  rw [show g + 1 + t = d by omega] at hsplit
  have hL : ∑ j ∈ range (g + 1), f j = right d z c₀ g ^ 2 * halfSum z c₀ K g 0 := by
    rw [← sum_range_reflect, halfSum, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm : m ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hm)
    simp only [f, add_tsub_cancel_right, zero_le, ite_true]
    rw [phi_of_le (by omega), left, Nat.cast_sub hm]
    ring
  have hR : ∑ k ∈ range t, f (g + 1 + k) =
      left z c₀ g ^ 2 * halfSum z ((d : ℝ) - 1 - c₀) K t 1 := by
    have hcast : ((t : ℕ) : ℝ) = d - 1 - g := by
      simp only [t]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [halfSum, sum_range_succ']
    simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, add_zero]
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k < t := mem_range.mp hk
    simp only [f, show 1 ≤ k + 1 by omega, ite_true]
    rw [phi_of_lt (by omega), right, show d - 1 - (g + 1 + k) = t - (k + 1) by omega, hcast]
    push_cast
    ring
  rw [spread, normSq, mul_sum, ← sum_sub_distrib, ← hL, ← hR, ← hsplit,
    ← Fin.sum_univ_eq_sum_range f]
  exact sum_congr rfl fun j _ => by ring

/-- **The Casoratian through the first ratios.** -/
theorem casoratian_eq (hg : 1 ≤ g) (hgd : g + 1 < d) (hz : 0 < z) (hc₁ : (g : ℝ) - 1 < c₀)
    (hc₂ : c₀ < g + 1) :
    casoratian d g z c₀ = left z c₀ g * right d z c₀ g *
      (ratio z ((d : ℝ) - 1 - c₀) (d - 1 - g) 0 - ratio z c₀ g 0 - 2 * (c₀ - g) / z) := by
  have hR : ((d - 1 - g : ℕ) : ℝ) - 1 < (d : ℝ) - 1 - c₀ := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith
  have hL0 := (seq_pos hz hc₁ g le_rfl).ne'
  have hR0 := (seq_pos hz hR _ le_rfl).ne'
  obtain ⟨h, rfl⟩ : ∃ h, g = h + 1 := ⟨g - 1, by omega⟩
  simp only [casoratian, left, right, ratio, show 0 < h + 1 by omega,
    show 0 < d - 1 - (h + 1) by omega, ite_true, Nat.add_sub_cancel,
    Nat.sub_zero, show d - 1 - (h + 1) - 1 = d - 1 - (h + 1 + 1) by omega,
    seq_add_two] at hL0 hR0 ⊢
  field_simp
  push_cast
  ring

end StarkPacket

end

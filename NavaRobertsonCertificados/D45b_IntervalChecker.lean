/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D45_StarkPackets

/-!
# D45b — An interval checker for Stark packets

Each half of a Stark packet (`D45`) is read from its top `t` downwards through the ratios
`Q m = A_{t−m−1}/A_{t−m}`, a continued fraction `Q m = 1/(2(m + u)/z + Q (m + 1))` with
`u = c − t + 1`. The checker encloses the ratios in fixed-point intervals of scale `2⁹⁶`, and
with them the weighted sum `Σ ((m + u − 1)² − K) (A_{t−m}/A_t)²`. Everything is natural-number
arithmetic, evaluated by the kernel; the soundness theorems turn the verdicts into real
inequalities.

## Main results

- `StarkPacket.ratio_rec` : the continued fraction of the ratios.
- `BandCertificate.ivs_sound` : the intervals enclose the ratios.
-/

@[expose] public noncomputable section

namespace StarkPacket

/-! ## A. The ratios of one half -/

/-- The ratio `Q m = A_{t−m−1}/A_{t−m}` at distance `m` from the top `t`, with `Q t = 0`. -/
def ratio (z c : ℝ) (t m : ℕ) : ℝ :=
  if m < t then seq z c (t - m - 1) / seq z c (t - m) else 0

variable {z c : ℝ} {t : ℕ}

lemma ratio_nonneg (hz : 0 < z) (hc : (t : ℝ) - 1 < c) (m : ℕ) : 0 ≤ ratio z c t m := by
  unfold ratio
  split_ifs
  · exact div_nonneg (seq_pos hz hc _ (by omega)).le (seq_pos hz hc _ (by omega)).le
  · exact le_rfl

/-- The ratios are a continued fraction. -/
lemma ratio_rec (hz : 0 < z) (hc : (t : ℝ) - 1 < c) {m : ℕ} (hm : m < t) :
    ratio z c t m = 1 / (2 * (m + (c - t + 1)) / z + ratio z c t (m + 1)) := by
  obtain ⟨i, hi⟩ : ∃ i, t = m + 1 + i := ⟨t - m - 1, by omega⟩
  have hpos := seq_pos hz hc
  rcases i with _ | i
  · subst hi
    simp only [ratio, hm, lt_irrefl, ite_true, ite_false, add_zero, Nat.sub_self,
      show m + 1 - m = 1 by omega, seq_one, seq_zero]
    push_cast
    field_simp
    ring
  · subst hi
    have h1 := hpos (i + 1) (by omega)
    simp only [ratio, hm, show m + 1 < m + 1 + (i + 1) by omega, ite_true,
      show m + 1 + (i + 1) - m = i + 2 by omega, show m + 1 + (i + 1) - (m + 1) = i + 1 by omega,
      seq_add_two]
    push_cast
    field_simp
    ring

/-- Below the top, the half is its top times the product of the ratios. -/
lemma seq_eq_prod (hz : 0 < z) (hc : (t : ℝ) - 1 < c) {m : ℕ} (hm : m ≤ t) :
    seq z c (t - m) = seq z c t * ∏ i ∈ Finset.range m, ratio z c t i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih (by omega)]
    simp only [ratio, show m < t by omega, ↓reduceIte]
    rw [mul_div_cancel₀ _ (seq_pos hz hc _ (by omega)).ne', show t - m - 1 = t - (m + 1) by omega]

end StarkPacket

namespace BandCertificate

/-! ## B. The checker -/

/-- The scale `S = 2⁹⁶` of the fixed-point arithmetic. -/
def S : ℕ := 2 ^ 96

/-- `⌈a/b⌉`. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- One half: `z = zn/zd`, `u ∈ [ulo/ud, uhi/ud]`, `K = Kn/Kd`. -/
structure Half where
  zn : ℕ
  zd : ℕ
  ud : ℕ
  ulo : ℕ
  uhi : ℕ
  Kn : ℕ
  Kd : ℕ

variable (p : Half)

/-- `S · 2(m + u)/z` rounded down, at `u = ulo/ud`. -/
def kLo (m : ℕ) : ℕ := 2 * S * (m * p.ud + p.ulo) * p.zd / (p.ud * p.zn)

/-- `S · 2(m + u)/z` rounded up, at `u = uhi/ud`. -/
def kHi (m : ℕ) : ℕ := cdiv (2 * S * (m * p.ud + p.uhi) * p.zd) (p.ud * p.zn)

/-- The step `Q ↦ 1/(k + Q)` on intervals. -/
def step (klo khi : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ :=
  (S * S / (khi + ab.2), cdiv (S * S) (klo + ab.1))

/-- `ivs top start j` encloses `Q (top − j)`, given the enclosure `start` of `Q top`. -/
def ivs (top : ℕ) (start : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => start
  | j + 1 => step (kLo p (top - j - 1)) (kHi p (top - j - 1)) (ivs top start j)

/-- The enclosure `[0, 1/k]` of `Q D` in a half deeper than `D`. -/
def startTrunc (D : ℕ) : ℕ × ℕ := (0, cdiv (S * S) (kLo p D))

/-- A lower bound of `(m + u − 1)²`, times `ud²`. -/
def wsq (m : ℕ) : ℕ :=
  let a : ℤ := m * p.ud + p.ulo - p.ud
  let b : ℤ := m * p.ud + p.uhi - p.ud
  if 0 ≤ a then (a * a).toNat else if b ≤ 0 then (b * b).toNat else 0

/-- Bounds `(pos, neg)` of `((m + u − 1)² − K) v` for `v ∈ [lo, hi]/S`. -/
def term (m lo hi : ℕ) : ℕ × ℕ :=
  let w := wsq p m * p.Kd
  let k := p.Kn * p.ud * p.ud
  let den := p.ud * p.ud * p.Kd
  if k ≤ w then (S * (w - k) / den * lo / S, 0) else (0, cdiv (cdiv (S * (k - w)) den * hi) S)

/-- After `n` terms: `vₙ = ∏_{i<n} Q i² ∈ [lo, hi]/S` and the sums `pos`, `neg`. -/
def sums (top : ℕ) (start : ℕ × ℕ) (m0 : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (S, S, 0, 0)
  | n + 1 =>
    let r := sums top start m0 n
    let t := if m0 ≤ n then term p n r.1 r.2.1 else (0, 0)
    let q := ivs p top start (top - n)
    (r.1 * q.1 * q.1 / (S * S), cdiv (r.2.1 * q.2 * q.2) (S * S), r.2.2.1 + t.1, r.2.2.2 + t.2)

end BandCertificate

namespace BandCertificate

/-! ## C. Soundness of the steps -/

/-- `x ∈ [a, b]/S`. -/
def Mem (ab : ℕ × ℕ) (x : ℝ) : Prop := (ab.1 : ℝ) / S ≤ x ∧ x ≤ ab.2 / S

lemma S_pos : (0 : ℝ) < S := by unfold S; positivity

lemma le_cdiv (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  have h := Nat.lt_div_mul_add (a := a + b - 1) hb
  have : a ≤ (a + b - 1) / b * b := by
    generalize (a + b - 1) / b * b = P at h ⊢
    omega
  rw [div_le_iff₀ (by exact_mod_cast hb), cdiv]
  exact_mod_cast this

lemma step_sound {k x : ℝ} {klo khi : ℕ} {ab : ℕ × ℕ} (hk₁ : (klo : ℝ) / S ≤ k)
    (hk₂ : k ≤ khi / S) (hx : Mem ab x) (hklo : 0 < klo) :
    Mem (step klo khi ab) (1 / (k + x)) := by
  obtain ⟨ha, hb⟩ := hx
  have hS := S_pos
  have h0 : (0 : ℝ) < klo := by exact_mod_cast hklo
  have hlo : ((klo + ab.1 : ℕ) : ℝ) / S ≤ k + x := by push_cast; rw [add_div]; linarith
  have hhi : k + x ≤ ((khi + ab.2 : ℕ) : ℝ) / S := by push_cast; rw [add_div]; linarith
  have hl0 : 0 < ((klo + ab.1 : ℕ) : ℝ) / S := div_pos (by push_cast; positivity) hS
  have hh0 : 0 < ((khi + ab.2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((khi + ab.2 : ℕ) : ℝ) / S := hl0.trans_le (hlo.trans hhi)
    exact (div_pos_iff_of_pos_right hS).mp this
  constructor
  · calc ((S * S / (khi + ab.2) : ℕ) : ℝ) / S
        ≤ ((S * S : ℕ) : ℝ) / (khi + ab.2 : ℕ) / S := by gcongr; exact Nat.cast_div_le
      _ = 1 / (((khi + ab.2 : ℕ) : ℝ) / S) := by push_cast at hh0 ⊢; field_simp
      _ ≤ 1 / (k + x) := one_div_le_one_div_of_le (hl0.trans_le hlo) hhi
  · calc 1 / (k + x) ≤ 1 / (((klo + ab.1 : ℕ) : ℝ) / S) := one_div_le_one_div_of_le hl0 hlo
      _ = ((S * S : ℕ) : ℝ) / (klo + ab.1 : ℕ) / S := by
        have : (0 : ℝ) < ((klo + ab.1 : ℕ) : ℝ) := by push_cast; positivity
        push_cast at this ⊢; field_simp
      _ ≤ (cdiv (S * S) (klo + ab.1) : ℝ) / S := by gcongr; exact le_cdiv _ (by omega)

variable {p}

/-- The parameters of a half are those of the real problem. -/
structure Fits (p : Half) (z u K : ℝ) : Prop where
  zn_pos : 0 < p.zn
  zd_pos : 0 < p.zd
  ud_pos : 0 < p.ud
  Kd_pos : 0 < p.Kd
  hz : z = p.zn / p.zd
  hK : K = p.Kn / p.Kd
  hlo : (p.ulo : ℝ) / p.ud ≤ u
  hhi : u ≤ p.uhi / p.ud

variable {z u K : ℝ}

lemma kLo_le (hp : Fits p z u K) (m : ℕ) : (kLo p m : ℝ) / S ≤ 2 * (m + u) / z := by
  have := hp.zn_pos; have := hp.zd_pos; have := hp.ud_pos; have := hp.hlo
  have hS := S_pos
  calc (kLo p m : ℝ) / S
      ≤ ((2 * S * (m * p.ud + p.ulo) * p.zd : ℕ) : ℝ) / (p.ud * p.zn : ℕ) / S := by
        gcongr; exact Nat.cast_div_le
    _ = 2 * (m + p.ulo / p.ud) / (p.zn / p.zd) := by push_cast; field_simp
    _ ≤ 2 * (m + u) / z := by rw [hp.hz]; gcongr

lemma le_kHi (hp : Fits p z u K) (m : ℕ) : 2 * (m + u) / z ≤ (kHi p m : ℝ) / S := by
  have := hp.zn_pos; have := hp.zd_pos; have := hp.ud_pos; have := hp.hhi
  have hS := S_pos
  calc 2 * (m + u) / z ≤ 2 * (m + p.uhi / p.ud) / (p.zn / p.zd) := by rw [hp.hz]; gcongr
    _ = ((2 * S * (m * p.ud + p.uhi) * p.zd : ℕ) : ℝ) / (p.ud * p.zn : ℕ) / S := by
        push_cast; field_simp
    _ ≤ (kHi p m : ℝ) / S := by gcongr; exact le_cdiv _ (by positivity)

/-- **The intervals enclose the ratios.** -/
theorem ivs_sound (hp : Fits p z u K) (hk : ∀ m, 0 < kLo p m) {Q : ℕ → ℝ} {top : ℕ}
    {start : ℕ × ℕ} (hrec : ∀ m < top, Q m = 1 / (2 * (m + u) / z + Q (m + 1)))
    (hs : Mem start (Q top)) :
    ∀ j ≤ top, Mem (ivs p top start j) (Q (top - j)) := by
  intro j
  induction j with
  | zero => simpa [ivs] using hs
  | succ j ih =>
    intro hj
    rw [ivs, hrec _ (by omega), show top - (j + 1) + 1 = top - j by omega,
      show top - j - 1 = top - (j + 1) by omega]
    exact step_sound (kLo_le hp _) (le_kHi hp _) (ih (by omega)) (hk _)

end BandCertificate

end

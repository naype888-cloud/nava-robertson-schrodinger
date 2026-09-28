/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.D44_VelocityBand
public import NavaRobertsonCertificados.D45c_HalfSums

/-!
# D45d — `d = 4` has the widest band

For every `d ≥ 5` a Stark packet (`D45`) moves with minimum uncertainty at speed at least
`κ = 0.9272 > v*(4)`. The glue offset is located by the intermediate value theorem between two
points where the checker fixes the sign of the Casoratian; on the subinterval that contains it,
the checker bounds `X − K N ≥ 0`, so `v = 4X/(ρ_d z N) ≥ κ`. For `5 ≤ d ≤ 27` each half is checked
exactly; for `d ≥ 28` one truncated check (`z = 8`, depth `12`) covers every `d`.

## Main results

- `BandCertificate.check_sound` : a passed check gives a fast minimum-uncertainty state.
-/

@[expose] public noncomputable section

open Set StarkPacket NearMaxTension GroupVelocity TransportPosition VelocityBand

namespace BandCertificate

/-! ## A. The sign of the Casoratian -/

/-- The speed `κ = 0.9272` certified for every `d ≥ 5`. -/
def kappa : ℝ := 9272 / 10000

/-- `S · 2(u − 1)/z · ud zn` at `u = l/ud`. -/
def wnum (zd ud l : ℕ) : ℤ := 2 * ((l : ℤ) - ud) * zd * S

/-- The sign test of the Casoratian at `u = l/ud`: `1`, `-1`, or `0` if undecided. -/
def wsign (zn zd ud l tL tR : ℕ) (o : Depth) : ℤ :=
  let pL : Half := ⟨zn, zd, ud, l, l, 0, 1⟩
  let pR : Half := ⟨zn, zd, ud, 2 * ud - l, 2 * ud - l, 0, 1⟩
  let qL := ivs pL (top tL o) (start pL o) (top tL o)
  let qR := ivs pR (top tR o) (start pR o) (top tR o)
  if kLo pL 0 = 0 ∨ kLo pR 0 = 0 then 0
  else if 0 < (qR.1 : ℤ) - qL.2 + (-wnum zd ud l) / ((ud * zn : ℕ) : ℤ) then 1
  else if (qR.2 : ℤ) - qL.1 - wnum zd ud l / ((ud * zn : ℕ) : ℤ) < 0 then -1 else 0

lemma intDiv_le (a : ℤ) {b : ℕ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ a / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a (by exact_mod_cast hb.ne')

variable {d g : ℕ} {zn zd ud l : ℕ} {o : Depth}

lemma wsign_sound (hg : 1 ≤ g) (hgd : g + 1 < d) (hzn : 0 < zn) (hzd : 0 < zd) (hl : 0 < l)
    (hl' : l < 2 * ud) (hL : Deep g o) (hR : Deep (d - 1 - g) o) :
    let F := casoratian d g ((zn : ℝ) / zd) (g + ((l : ℝ) / ud - 1))
    (wsign zn zd ud l g (d - 1 - g) o = 1 → 0 < F) ∧
      (wsign zn zd ud l g (d - 1 - g) o = -1 → F < 0) := by
  intro F
  have hud : 0 < ud := by omega
  have hudR : (0 : ℝ) < ud := by exact_mod_cast hud
  have hz : (0 : ℝ) < zn / zd := by positivity
  have hS := S_pos
  set c₀ : ℝ := g + ((l : ℝ) / ud - 1)
  have hlR : (0 : ℝ) < l / ud := by positivity
  have hlR' : (l : ℝ) / ud < 2 := by
    rw [div_lt_iff₀ hudR]; exact_mod_cast (by omega : l < 2 * ud)
  have hc₁ : (g : ℝ) - 1 < c₀ := by simp only [c₀]; linarith
  have hc₂ : c₀ < g + 1 := by simp only [c₀]; linarith
  have htR : (((d - 1 - g : ℕ) : ℝ)) = d - 1 - g := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  have hcR : ((d - 1 - g : ℕ) : ℝ) - 1 < (d : ℝ) - 1 - c₀ := by rw [htR]; linarith
  have hFL : Fits ⟨zn, zd, ud, l, l, 0, 1⟩ (zn / zd) (c₀ - g + 1) 0 := by
    have : (l : ℝ) / ud = c₀ - g + 1 := by simp only [c₀]; ring
    exact ⟨hzn, hzd, hud, one_pos, rfl, by simp, this.le, this.ge⟩
  have hFR : Fits ⟨zn, zd, ud, 2 * ud - l, 2 * ud - l, 0, 1⟩ (zn / zd)
      ((d : ℝ) - 1 - c₀ - ((d - 1 - g : ℕ) : ℝ) + 1) 0 := by
    have : (((2 * ud - l : ℕ) : ℝ)) / ud = (d : ℝ) - 1 - c₀ - ((d - 1 - g : ℕ) : ℝ) + 1 := by
      rw [htR, Nat.cast_sub hl'.le]; simp only [c₀]; push_cast; field_simp; ring
    exact ⟨hzn, hzd, hud, one_pos, rfl, by simp, this.le, this.ge⟩
  set N : ℝ := (wnum zd ud l : ℝ) / (ud * zn : ℕ)
  have hN : 2 * (c₀ - g) / (zn / zd) = N / S := by
    simp only [N, c₀, wnum]; push_cast; field_simp; ring
  have hfl := intDiv_le (wnum zd ud l) (b := ud * zn) (by positivity)
  have hce : (((-wnum zd ud l) / ((ud * zn : ℕ) : ℤ) : ℤ) : ℝ) ≤ -N := by
    refine (intDiv_le _ (by positivity)).trans (le_of_eq ?_)
    simp only [N]; push_cast; ring
  have hF : F = left ((zn : ℝ) / zd) c₀ g * right d ((zn : ℝ) / zd) c₀ g *
      (ratio (zn / zd) ((d : ℝ) - 1 - c₀) (d - 1 - g) 0 - ratio (zn / zd) c₀ g 0 - N / S) := by
    rw [← hN]; exact casoratian_eq hg hgd hz hc₁ hc₂
  have hLR : 0 < left ((zn : ℝ) / zd) c₀ g * right d ((zn : ℝ) / zd) c₀ g :=
    mul_pos (seq_pos hz hc₁ g le_rfl) (seq_pos hz hcR _ le_rfl)
  set pL : Half := ⟨zn, zd, ud, l, l, 0, 1⟩
  set pR : Half := ⟨zn, zd, ud, 2 * ud - l, 2 * ud - l, 0, 1⟩
  have encl : ¬(kLo pL 0 = 0 ∨ kLo pR 0 = 0) →
      Mem (ivs pL (top g o) (start pL o) (top g o - 0)) (ratio (zn / zd) c₀ g 0) ∧
        Mem (ivs pR (top (d - 1 - g) o) (start pR o) (top (d - 1 - g) o - 0))
          (ratio (zn / zd) ((d : ℝ) - 1 - c₀) (d - 1 - g) 0) := fun h0 => by
    rw [not_or] at h0
    exact ⟨ratio_mem hFL hz hc₁ (Nat.pos_of_ne_zero h0.1) o hL 0 (Nat.zero_le _),
      ratio_mem hFR hz hcR (Nat.pos_of_ne_zero h0.2) o hR 0 (Nat.zero_le _)⟩
  constructor <;> intro hw <;> simp only [wsign] at hw <;> split_ifs at hw with h0 h1 h2 <;>
    simp only [Int.reduceNeg, zero_ne_one] at hw
  · obtain ⟨⟨hL1, hL2⟩, ⟨hR1, hR2⟩⟩ := encl h0
    simp only [Nat.sub_zero] at hL2 hR1
    have h1' : (0 : ℝ) < _ := Int.cast_pos.mpr h1
    push_cast at h1'
    rw [hF]
    refine mul_pos hLR ?_
    have : 0 < (((_ : ℕ) : ℝ) - (_ : ℕ) + (((-wnum zd ud l) / ((ud * zn : ℕ) : ℤ) : ℤ) : ℝ)) / S :=
      div_pos h1' hS
    rw [add_div, sub_div] at this
    linarith [div_le_div_of_nonneg_right hce hS.le, neg_div (S : ℝ) N]
  · obtain ⟨⟨hL1, hL2⟩, ⟨hR1, hR2⟩⟩ := encl h0
    simp only [Nat.sub_zero] at hL1 hR2
    have h2' : (_ : ℝ) < 0 := Int.cast_lt_zero.mpr h2
    push_cast at h2'
    rw [hF]
    refine mul_neg_of_pos_of_neg hLR ?_
    have : (((_ : ℕ) : ℝ) - (_ : ℕ) - ((wnum zd ud l / ((ud * zn : ℕ) : ℤ) : ℤ) : ℝ)) / S < 0 :=
      div_neg_of_neg_of_pos h2' hS
    rw [sub_div, sub_div] at this
    linarith [div_le_div_of_nonneg_right hfl hS.le]

lemma wsign_cases (zn zd ud l tL tR : ℕ) (o : Depth) :
    wsign zn zd ud l tL tR o = 1 ∨ wsign zn zd ud l tL tR o = -1 ∨
      wsign zn zd ud l tL tR o = 0 := by
  unfold wsign; dsimp only; split_ifs <;> simp

/-! ## B. The check and its soundness -/

/-- The checked bound `X − K N ≥ 0` on a subinterval `u ∈ [a, b]/ud` of the left half. -/
def velOK (zn zd ud a b Kn Kd tL tR : ℕ) (o : Depth) : Bool :=
  let pL : Half := ⟨zn, zd, ud, a, b, Kn, Kd⟩
  let pR : Half := ⟨zn, zd, ud, 2 * ud - b, 2 * ud - a, Kn, Kd⟩
  valid pL o && valid pR o && 0 < kLo pL 0 && 0 < kLo pR 0 &&
    (half pL tL 0 o).2 + (half pR tR 1 o).2 ≤ (half pL tL 0 o).1 + (half pR tR 1 o).1

/-- The certificate: a sign change of the Casoratian on `u ∈ [la, lb]/ud` and the bound on
each of `nsub` subintervals. -/
def check (tL tR zn zd ud la lb nsub Kn Kd : ℕ) (o : Depth) : Bool :=
  0 < zn && 0 < zd && 0 < Kd && 0 < la && la < lb && lb < 2 * ud &&
    (lb - la) / nsub * nsub == lb - la &&
    wsign zn zd ud la tL tR o * wsign zn zd ud lb tL tR o == -1 &&
    (List.range nsub).all fun k => velOK zn zd ud (la + k * ((lb - la) / nsub))
      (la + (k + 1) * ((lb - la) / nsub)) Kn Kd tL tR o

lemma exists_sub {x a s : ℝ} (hs : 0 ≤ s) :
    ∀ n : ℕ, 0 < n → a ≤ x → x ≤ a + n * s → ∃ k < n, a + k * s ≤ x ∧ x ≤ a + (k + 1) * s
  | 0, h, _, _ => absurd h (lt_irrefl 0)
  | n + 1, _, h1, h2 => by
    by_cases h : 0 < n ∧ x ≤ a + n * s
    · obtain ⟨k, hk, hk'⟩ := exists_sub hs n h.1 h1 h.2
      exact ⟨k, by omega, hk'⟩
    · refine ⟨n, by omega, ?_, by push_cast at h2; linarith⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using h1
      · exact (not_le.mp fun h' => h ⟨hn, h'⟩).le

/-- **Soundness.** A passed check gives a minimum-uncertainty state moving at least at `κ`. -/
theorem check_sound (hd : 5 ≤ d) {la lb nsub Kn Kd : ℕ}
    (hc : check ((d - 1) / 2) (d - 1 - (d - 1) / 2) zn zd ud la lb nsub Kn Kd o = true)
    (hL : Deep ((d - 1) / 2) o) (hR : Deep (d - 1 - (d - 1) / 2) o)
    (hρ : rho d * kappa * (zn / zd) ≤ 4 * (Kn / Kd)) :
    ∃ ψ : Hd d, ‖ψ‖ = 1 ∧ surplus d ψ = 0 ∧ kappa ≤ velocity d ψ := by
  set g := (d - 1) / 2
  have hg : 1 ≤ g := by omega
  have hgd : g + 1 < d := by omega
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hzn, hzd⟩, hKd⟩, hla⟩, hlab⟩, hlb⟩, hstep⟩, hsign⟩, hvel⟩ := hc
  set sN := (lb - la) / nsub
  have hns : 0 < nsub := Nat.pos_of_ne_zero fun h => by simp [h] at hstep; omega
  have hud : 0 < ud := by omega
  have hudR : (0 : ℝ) < ud := by exact_mod_cast hud
  set z : ℝ := zn / zd
  have hz : 0 < z := by positivity
  -- the glue offset
  set F : ℝ → ℝ := fun δ => casoratian d g z (g + δ)
  have hFc : Continuous F := by
    simp only [F, casoratian, left, right]
    have := continuous_seq z
    fun_prop
  have hFa := wsign_sound (d := d) hg hgd hzn hzd hla (by omega) hL hR (o := o) (ud := ud)
  have hFb := wsign_sound (d := d) hg hgd hzn hzd (by omega) hlb hL hR (o := o) (ud := ud)
  have hab : (la : ℝ) / ud - 1 ≤ (lb : ℝ) / ud - 1 := by gcongr
  obtain ⟨δ, ⟨hδ₁, hδ₂⟩, hδ⟩ : ∃ δ ∈ Icc ((la : ℝ) / ud - 1) ((lb : ℝ) / ud - 1), F δ = 0 := by
    rcases wsign_cases zn zd ud la g (d - 1 - g) o with h | h | h <;>
      rcases wsign_cases zn zd ud lb g (d - 1 - g) o with h' | h' | h' <;>
      simp only [h, h'] at hsign <;> norm_num at hsign
    · exact intermediate_value_Icc' hab hFc.continuousOn ⟨(hFb.2 h').le, (hFa.1 h).le⟩
    · exact intermediate_value_Icc hab hFc.continuousOn ⟨(hFa.2 h).le, (hFb.1 h').le⟩
  set c₀ := (g : ℝ) + δ
  have hla' : (0 : ℝ) < la / ud := by positivity
  have hlb' : (lb : ℝ) / ud < 2 := by
    rw [div_lt_iff₀ hudR]; exact_mod_cast (by omega : lb < 2 * ud)
  have hc₁ : (g : ℝ) - 1 < c₀ := by simp only [c₀]; linarith
  have hc₂ : c₀ < g + 1 := by simp only [c₀]; linarith
  obtain ⟨ψ, hψ, hsat, hv⟩ := exists_saturated_velocity (by omega) hgd hz hc₁ hc₂ hδ
  refine ⟨ψ, hψ, hsat, ?_⟩
  -- the subinterval that contains it
  have hsN : (0 : ℝ) ≤ sN / ud := by positivity
  have hstep' : nsub * sN = lb - la := by rw [mul_comm]; exact hstep
  have hend : (lb : ℝ) / ud = la / ud + nsub * (sN / ud) := by
    have : (lb : ℝ) = la + nsub * sN := by exact_mod_cast (by omega : lb = la + nsub * sN)
    rw [this]
    field_simp
  obtain ⟨k, hk, hk₁, hk₂⟩ :=
    exists_sub hsN nsub hns (by linarith : (la : ℝ) / ud ≤ δ + 1) (by linarith)
  have hb : la + (k + 1) * sN ≤ lb := by
    have : (k + 1) * sN ≤ nsub * sN := Nat.mul_le_mul_right _ hk
    omega
  have hb' : k * sN ≤ (k + 1) * sN := Nat.mul_le_mul_right _ (Nat.le_succ k)
  have hv' := hvel k hk
  simp only [velOK, Bool.and_eq_true, decide_eq_true_eq] at hv'
  obtain ⟨⟨⟨⟨hvL, hvR⟩, hk0L⟩, hk0R⟩, hsum⟩ := hv'
  set K : ℝ := Kn / Kd
  have htR : (((d - 1 - g : ℕ) : ℝ)) = d - 1 - g := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [show (la : ℝ) / ud + k * (sN / ud) = (la + k * sN) / ud by ring, div_le_iff₀ hudR] at hk₁
  rw [show (la : ℝ) / ud + (k + 1) * (sN / ud) = (la + (k + 1) * sN) / ud by ring,
    le_div_iff₀ hudR] at hk₂
  have hFL : Fits ⟨zn, zd, ud, la + k * sN, la + (k + 1) * sN, Kn, Kd⟩ z (c₀ - g + 1) K := by
    refine ⟨hzn, hzd, hud, hKd, rfl, rfl, ?_, ?_⟩
    · rw [div_le_iff₀ hudR]; push_cast; simp only [c₀]; nlinarith
    · rw [le_div_iff₀ hudR]; push_cast; simp only [c₀]; nlinarith
  have hFR : Fits ⟨zn, zd, ud, 2 * ud - (la + (k + 1) * sN), 2 * ud - (la + k * sN), Kn, Kd⟩ z
      ((d : ℝ) - 1 - c₀ - ((d - 1 - g : ℕ) : ℝ) + 1) K := by
    refine ⟨hzn, hzd, hud, hKd, rfl, rfl, ?_, ?_⟩
    · rw [div_le_iff₀ hudR, htR, Nat.cast_sub (by omega)]; push_cast; simp only [c₀]; nlinarith
    · rw [le_div_iff₀ hudR, htR, Nat.cast_sub (by omega)]; push_cast; simp only [c₀]; nlinarith
  have hcR : ((d - 1 - g : ℕ) : ℝ) - 1 < (d : ℝ) - 1 - c₀ := by rw [htR]; linarith
  have hHL := half_sound hFL hz hc₁ hk0L 0 o hL hvL
  have hHR := half_sound hFR hz hcR hk0R 1 o hR hvR
  have hsplit := spread_sub (d := d) (g := g) (z := z) (c₀ := c₀) (K := K) (by omega)
  simp only [left, right] at hsplit
  have hS := S_pos
  have hX : K * normSq d g z c₀ ≤ spread d g z c₀ := by
    generalize half ⟨zn, zd, ud, la + k * sN, la + (k + 1) * sN, Kn, Kd⟩ g 0 o = A at hHL hsum
    generalize half ⟨zn, zd, ud, 2 * ud - (la + (k + 1) * sN), 2 * ud - (la + k * sN), Kn, Kd⟩
      (d - 1 - g) 1 o = B at hHR hsum
    generalize seq z c₀ g = L at hHL hsplit
    generalize seq z ((d : ℝ) - 1 - c₀) (d - 1 - g) = R at hHR hsplit
    have hAB : (0 : ℝ) ≤ (A.1 : ℝ) - A.2 + (B.1 - B.2) := by
      have : (A.2 + B.2 : ℝ) ≤ A.1 + B.1 := by exact_mod_cast hsum
      linarith
    have e1 := mul_le_mul_of_nonneg_left hHL (sq_nonneg R)
    have e2 := mul_le_mul_of_nonneg_left hHR (sq_nonneg L)
    have e3 : 0 ≤ L ^ 2 * R ^ 2 * ((A.1 : ℝ) - A.2 + (B.1 - B.2)) / S := by positivity
    have e4 : R ^ 2 * (L ^ 2 * ((A.1 : ℝ) - A.2) / S) + L ^ 2 * (R ^ 2 * ((B.1 : ℝ) - B.2) / S) =
        L ^ 2 * R ^ 2 * ((A.1 : ℝ) - A.2 + (B.1 - B.2)) / S := by ring
    linarith
  have hN := normSq_pos (d := d) (show g < d by omega) hz hc₁ hc₂
  have hr := rho_pos d (by omega)
  have hpos : 0 < rho d * z * normSq d g z c₀ := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  calc kappa * (rho d * z * normSq d g z c₀) = rho d * kappa * z * normSq d g z c₀ := by ring
    _ ≤ 4 * K * normSq d g z c₀ := by gcongr
    _ ≤ 4 * spread d g z c₀ := by linarith
    _ = velocity d ψ * (rho d * z * normSq d g z c₀) := by rw [← hv]; ring

end BandCertificate

end

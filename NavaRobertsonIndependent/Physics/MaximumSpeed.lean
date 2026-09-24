import NavaRobertsonIndependent.Physics.TimeEnergyRegistrationClosure

/-!
# Maximal registrable speed: light as the ratio of the two floors (Mathlib-only port)

The ratio between the two floors of registration, the spatial one (`Lsbpk`) and the
temporal one (`Tausbpk`), bounds the speed of every registrable transport process,
and that ratio is `c`. The cap of one step per tick is derived in the final section.

* **Spatial floor** (`SubPlanckianLimit`): the SBPK cell fixes the minimal
  resolvable length, `Lsbpk > 0`; elementary transport advances one cell step per
  step (`D3_PathGraph`, `D22_TransportPositionInstanceTdPd`).
* **Temporal floor** (`TimeEnergyRegistrationClosure`): the tick is the minimal
  registrable duration, `Tausbpk > 0` (Mandelstam–Tamm bound, `piso_temporal` /
  `transporte_cuesta_tiempo`).

A registrable transport process with `k` cell steps in `n` ticks (`1 ≤ k ≤ n`) has
mean speed `k·Lsbpk / (n·Tausbpk) ≤ Lsbpk / Tausbpk`. And `Lsbpk / Tausbpk` is
exactly `velocidadMaximaRegistrada = cSI`: the ratio of the spatial floor to the
temporal floor. The continuum admits arbitrary speeds; discrete registration does
not, and the limit is fixed by the ratio of its two floors. The maximal process
(`k = n = 1`: one cell step in one tick) attains it.

Status: the *existence* and the *exact obstruction* of the limit are theorems, and
the hypothesis `k ≤ n` is derived from the per-step temporal floor plus additivity
of duration (`ProcesoTransporte`, `velocidadMedia_le_luz`, `k_le_n_de_duracion`).
Explicit inputs that remain:

* H1, the spectral ceiling `DispersionAdmisible`. Since `energiaMandelstamTamm` is
  defined from `Tausbpk`, H1 restates the temporal floor as a spectral bound.
* The calibration `distanciaRecorrida k = k · Lsbpk`: the elementary step of the
  path (`D3_PathGraph`, `D22_TransportPositionInstanceTdPd`) measures one cell.
  `Lsbpk` is tied to `T_d:P_d` through `geometricGap 4` (`D8`, `D9`, `D22`), but that
  identification of the step length is a calibration, not a theorem.
* `299792458` is the SI definition and enters `Tausbpk = Lsbpk / c` and
  `E_P = ħ c / l_P`. `c` is the laboratory input; the theorem does not compute the
  number `c`: it shows that the registrable limit is the ratio of the floors, which
  in the SI convention equals `c`.
-/

noncomputable section

open LimiteSubPlanckiano ColapsoSchwarzschild CierreRegistroTiempoEnergiaSbpk

namespace VelocidadMaximaRegistrable

/-- Distance of `k` elementary cell steps. -/
def distanciaRecorrida (k : ℕ) : ℝ := (k : ℝ) * Lsbpk

/-- Mean speed of a process with `k` steps in `n` ticks (`n ≥ 1`). -/
def velocidadProceso (k n : ℕ) : ℝ := distanciaRecorrida k / tiempoFisico n

theorem distancia_pos {k : ℕ} (hk : 1 ≤ k) : 0 < distanciaRecorrida k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  unfold distanciaRecorrida
  exact mul_pos hkR Lsbpk_pos

theorem velocidad_pos {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    0 < velocidadProceso k n := by
  unfold velocidadProceso
  exact div_pos (distancia_pos hk) (tiempo_positivo_iff n |>.mpr (zero_lt_one.trans_le hn))

/-- The obstruction: more ticks than steps (or as many) lowers or keeps the mean
speed; no registrable process exceeds one cell step per tick. -/
theorem velocidad_le_cota {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    velocidadProceso k n ≤ Lsbpk / Tausbpk := by
  have hn1 : 1 ≤ n := le_trans hk hn
  have hnR : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < n * Tausbpk :=
    mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)) Tausbpk_pos
  have hkn := mul_le_mul_of_nonneg_right hnR Lsbpk_pos.le
  have e2 : (Lsbpk / Tausbpk) * ((n : ℝ) * Tausbpk) = (n : ℝ) * Lsbpk := by
    field_simp [ne_of_gt Tausbpk_pos]
  unfold velocidadProceso distanciaRecorrida tiempoFisico
  rw [div_le_iff₀ hden, e2]
  exact hkn

/-- The ratio of the two floors is the maximal registered speed. -/
theorem cota_es_velocidad_maxima : Lsbpk / Tausbpk = velocidadMaximaRegistrada := by
  unfold Tausbpk
  field_simp [ne_of_gt Lsbpk_pos, ne_of_gt velocidadMaximaRegistrada_pos]

/-- The two resolution gates with a single cell — the time gate
(`resolucion_por_tiempo`, `E_res·τ_sbpk = ħ`) and the length gate
(`resolucion_por_longitud`, `E_res = ħ·c/L_sbpk`) — give `c = L_sbpk/τ_sbpk`. It is
the same identity as `cota_es_velocidad_maxima`, obtained by another route: `c`
enters through its SI definition in `Tausbpk` and in `E_P`. -/
theorem c_despejada_desde_resolucion : cSI = Lsbpk / Tausbpk := by
  have h1 := resolucion_por_tiempo
  rw [resolucion_por_longitud] at h1
  have hL : Lsbpk ≠ 0 := ne_of_gt Lsbpk_pos
  have ht : Tausbpk ≠ 0 := ne_of_gt Tausbpk_pos
  have hb : hbarSI ≠ 0 := ne_of_gt hbarSI_pos
  rw [div_mul_eq_mul_div, mul_comm (hbarSI * cSI) Tausbpk] at h1
  rw [div_eq_iff hL] at h1
  have h2 : hbarSI * (cSI * Tausbpk) = hbarSI * Lsbpk := by nlinarith
  have hc : cSI * Tausbpk = Lsbpk := mul_left_cancel₀ hb h2
  rw [eq_div_iff ht]
  exact hc

/-- **Main theorem.** No registrable transport process exceeds the speed of light:
`v ≤ Lsbpk / Tausbpk = velocidadMaximaRegistrada = c`. -/
theorem velocidad_le_luz {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    velocidadProceso k n ≤ cSI :=
  calc velocidadProceso k n
      ≤ Lsbpk / Tausbpk := velocidad_le_cota hk hn
    _ = velocidadMaximaRegistrada := cota_es_velocidad_maxima
    _ = cSI := velocidad_coincide

/-- The maximal process — one cell step in exactly one tick — attains it: the limit
is sharp in the sense that some process realizes it. -/
theorem proceso_maximal_alcanza_c : velocidadProceso 1 1 = cSI := by
  have h : velocidadProceso 1 1 = Lsbpk / Tausbpk := by
    simp [velocidadProceso, distanciaRecorrida, tiempoFisico]
  rw [h, cota_es_velocidad_maxima, velocidad_coincide]

/-- A strictly subluminal process is one that spends more than one tick per step;
the equality `v = c` characterizes maximal transport `k = n`. -/
theorem maximal_iff_un_paso_por_tick {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    velocidadProceso k n = cSI ↔ k = n := by
  constructor
  · intro heq
    have key : k < n → velocidadProceso k n < cSI := by
      intro hltn
      have hn1 : 1 ≤ n := le_trans hk hn
      have hkn : ((k : ℝ) < n) := by exact_mod_cast hltn
      have hden : (0 : ℝ) < n * Tausbpk :=
        mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)) Tausbpk_pos
      have h1 : velocidadProceso k n < Lsbpk / Tausbpk := by
        unfold velocidadProceso distanciaRecorrida tiempoFisico
        have e2 : (Lsbpk / Tausbpk) * ((n : ℝ) * Tausbpk) = (n : ℝ) * Lsbpk := by
          field_simp [ne_of_gt Tausbpk_pos]
        rw [div_lt_iff₀ hden, e2]
        nlinarith [hkn, Lsbpk_pos]
      calc velocidadProceso k n < Lsbpk / Tausbpk := h1
        _ = cSI := by rw [cota_es_velocidad_maxima, velocidad_coincide]
    have hnot : ¬ k < n := fun hltn => absurd (key hltn) (by rw [heq]; exact lt_irrefl cSI)
    exact Nat.le_antisymm hn (Nat.le_of_not_gt hnot)
  · intro hkn
    subst hkn
    -- `k = n`: `k·Lsbpk / (k·Tausbpk) = Lsbpk / Tausbpk = c`
    have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    have e1 : (k : ℝ) * Lsbpk / ((k : ℝ) * Tausbpk) = Lsbpk / Tausbpk := by
      rw [mul_comm (k : ℝ) Lsbpk, mul_comm (k : ℝ) Tausbpk]
      exact mul_div_mul_right _ _ hkR.ne'
    unfold velocidadProceso distanciaRecorrida tiempoFisico
    rw [e1, cota_es_velocidad_maxima, velocidad_coincide]

/-! ## Closure: the cap `k ≤ n` is derived, not assumed

Above, `k ≤ n` enters as a hypothesis. Here it is derived: a process of `k`
elementary steps is a sequence of `k` admissible physical processes, each with the
Mandelstam–Tamm bound and the spectral ceiling of the sector
(`tick_es_cota_mandelstam_tamm`). Each step lasts at least one tick, and the
duration of a sequence is the sum of those of its steps. Hence `k` steps cost at
least `k` ticks, for any real duration `T`, not only for integer multiples of the
tick.
-/

/-- Transport process of `k` elementary cell steps. Step `i` lasts `tau i` and has
energy spread `deltaH i`, with Mandelstam–Tamm and the spectral ceiling
`DispersionAdmisible` (hypothesis H1 of the sector). -/
structure ProcesoTransporte (k : ℕ) where
  tau : Fin k → ℝ
  deltaH : Fin k → ℝ
  tau_nonneg : ∀ i, 0 ≤ tau i
  mt : ∀ i, MandelstamTammFisico (tau i) (deltaH i)
  admisible : ∀ i, DispersionAdmisible (deltaH i)

namespace ProcesoTransporte

/-- Total duration: the steps are consecutive and their durations add up. -/
def duracion {k : ℕ} (P : ProcesoTransporte k) : ℝ := ∑ i, P.tau i

/-- Mean speed: `k` cells over the total duration. -/
def velocidadMedia {k : ℕ} (P : ProcesoTransporte k) : ℝ :=
  distanciaRecorrida k / P.duracion

/-- Each elementary step lasts at least one tick. -/
theorem paso_dura_un_tick {k : ℕ} (P : ProcesoTransporte k) (i : Fin k) :
    Tausbpk ≤ P.tau i := by
  have h := tick_es_cota_mandelstam_tamm (P.tau_nonneg i) (P.mt i) (P.admisible i)
  rwa [primer_tick] at h

/-- `k` steps cost at least `k` SBPK intervals. -/
theorem k_pasos_cuestan_k_ticks {k : ℕ} (P : ProcesoTransporte k) :
    (k : ℝ) * Tausbpk ≤ P.duracion := by
  have h : ∑ _i : Fin k, Tausbpk ≤ ∑ i, P.tau i :=
    Finset.sum_le_sum fun i _ => P.paso_dura_un_tick i
  simpa [duracion, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using h

theorem duracion_pos {k : ℕ} (hk : 1 ≤ k) (P : ProcesoTransporte k) :
    0 < P.duracion := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  exact lt_of_lt_of_le (mul_pos hkR Tausbpk_pos) P.k_pasos_cuestan_k_ticks

/-- Bound for every real duration, without assuming an integer number of ticks. -/
theorem velocidadMedia_le_cota {k : ℕ} (hk : 1 ≤ k) (P : ProcesoTransporte k) :
    P.velocidadMedia ≤ Lsbpk / Tausbpk := by
  have hT := P.duracion_pos hk
  have hdur := P.k_pasos_cuestan_k_ticks
  have hq : 0 < Lsbpk / Tausbpk := div_pos Lsbpk_pos Tausbpk_pos
  have e : (Lsbpk / Tausbpk) * ((k : ℝ) * Tausbpk) = (k : ℝ) * Lsbpk := by
    field_simp [ne_of_gt Tausbpk_pos]
  unfold velocidadMedia distanciaRecorrida
  rw [div_le_iff₀ hT]
  calc (k : ℝ) * Lsbpk = (Lsbpk / Tausbpk) * ((k : ℝ) * Tausbpk) := e.symm
    _ ≤ (Lsbpk / Tausbpk) * P.duracion := mul_le_mul_of_nonneg_left hdur hq.le

/-- **Closure.** Every admissible transport process, of any real duration, has mean
speed `≤ c`. -/
theorem velocidadMedia_le_luz {k : ℕ} (hk : 1 ≤ k) (P : ProcesoTransporte k) :
    P.velocidadMedia ≤ cSI :=
  calc P.velocidadMedia
      ≤ Lsbpk / Tausbpk := P.velocidadMedia_le_cota hk
    _ = velocidadMaximaRegistrada := cota_es_velocidad_maxima
    _ = cSI := velocidad_coincide

/-- The hypothesis `k ≤ n` of the theorems above is a consequence: a process of `k`
steps lasting exactly `n` ticks satisfies `k ≤ n`. -/
theorem k_le_n_de_duracion {k n : ℕ} (P : ProcesoTransporte k)
    (h : P.duracion = tiempoFisico n) : k ≤ n := by
  have h1 := P.k_pasos_cuestan_k_ticks
  rw [h] at h1
  unfold tiempoFisico at h1
  have h2 : (k : ℝ) ≤ n := le_of_mul_le_mul_right h1 Tausbpk_pos
  exact_mod_cast h2

/-- The maximal process: every step saturates Mandelstam–Tamm and the spectral
ceiling. The hypotheses of the closure are satisfiable, not vacuous. -/
def maximal (k : ℕ) : ProcesoTransporte k where
  tau := fun _ => Tausbpk
  deltaH := fun _ => energiaMandelstamTamm
  tau_nonneg := fun _ => Tausbpk_pos.le
  mt := fun _ => tausbpk_mul_energiaMandelstamTamm.symm.le
  admisible := fun _ => ⟨energiaMandelstamTamm_pos.le, le_refl _⟩

theorem maximal_duracion (k : ℕ) : (maximal k).duracion = (k : ℝ) * Tausbpk := by
  simp [duracion, maximal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The limit is attained: the maximal process goes exactly at `c`. -/
theorem maximal_alcanza_c {k : ℕ} (hk : 1 ≤ k) : (maximal k).velocidadMedia = cSI := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have e1 : (k : ℝ) * Lsbpk / ((k : ℝ) * Tausbpk) = Lsbpk / Tausbpk := by
    rw [mul_comm (k : ℝ) Lsbpk, mul_comm (k : ℝ) Tausbpk]
    exact mul_div_mul_right _ _ hkR.ne'
  unfold velocidadMedia distanciaRecorrida
  rw [maximal_duracion, e1, cota_es_velocidad_maxima, velocidad_coincide]

end ProcesoTransporte

end VelocidadMaximaRegistrable

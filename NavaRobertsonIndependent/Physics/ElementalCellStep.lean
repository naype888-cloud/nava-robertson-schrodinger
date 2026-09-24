import NavaRobertsonIndependent.Physics.MaximumSpeed
import NavaRobertsonIndependent.Mathematics.D22_TransportPositionInstanceTdPd

/-!
# The elementary step of the path measures `Lsbpk`

Joins the algebraic chain `D3`–`D22` with the SBPK cell.

* `D3`: the elementary step `PasoMinimo i j` is the edge of `pathGraph d`, and the
  path is the only local and complete graph.
* `D22`: `(T_d, P_d)` realizes that graph, and its defect is `δ(d) = C_Nava(d) − 1`:
  zero at `d = 2, 3` (Robertson–Schrödinger saturates) and strictly positive from
  `d = 4`, with exact minimum at `d = 4` (`D9`).
* Laboratory anchors: `l_P` (CODATA), `Ω_b` (from `π`, `D26a`) and `c` (SI).

The physical length of the elementary step in dimension `d` is the defect times the
laboratory scale: `longitudPaso d = √Ω_b · l_P · δ(d)`. It is proved that at `d = 4`
it is exactly `Lsbpk` (`longitudPaso_cuatro`), that this is the minimum over all
open dimensions, and that it is positive exactly when the defect of `(T_d, P_d)` is.

Status: `longitudPaso d` is a **calibration** (the dimensional quantum `δ(d)` times
the laboratory scale `√Ω_b · l_P`), not a theorem. What is proved is its behaviour
in `d`: floor `Lsbpk` at `H_4`, ceiling `longitudPasoInf`, and the limit.
-/

noncomputable section

open LimiteSubPlanckiano ColapsoSchwarzschild CierreRegistroTiempoEnergiaSbpk
  TransportePosicion Gnomon DinamicaElemental Robertson1929
  NavaRobertsonSchrodingerEDUI

namespace PasoElementalCelda

/-- Laboratory anchor of length: metres per unit of defect. -/
def escalaLongitud : ℝ := Real.sqrt Omega_b * longitudPlanckCODATA

theorem escalaLongitud_pos : 0 < escalaLongitud :=
  mul_pos (Real.sqrt_pos.mpr Omega_b_pos) longitudPlanckCODATA_pos

/-- Physical length of the minimal step (edge of `pathGraph d`) in dimension `d`:
the laboratory scale times the geometric defect `δ(d) = C_Nava(d) − 1`. -/
def longitudPaso (d : ℕ) : ℝ := escalaLongitud * Gnomon.geometricGap d

/-- **The elementary step of `d = 4` is `Lsbpk`.** -/
theorem longitudPaso_cuatro : longitudPaso 4 = Lsbpk := by
  have hδ : 0 ≤ deltaD4 := deltaD4_pos.le
  have h : lsubCanal = Real.sqrt Omega_b * deltaD4 := by
    unfold lsubCanal channelSubQuantum
    rw [Real.sqrt_mul Omega_b_pos.le, Real.sqrt_sq hδ]
  unfold longitudPaso escalaLongitud Lsbpk
  rw [h]
  unfold deltaD4
  ring

/-- `Lsbpk` is the minimal step over all open dimensions. -/
theorem Lsbpk_le_longitudPaso {d : ℕ} (hd : 4 ≤ d) : Lsbpk ≤ longitudPaso d := by
  rw [← longitudPaso_cuatro]
  exact mul_le_mul_of_nonneg_left (Gnomon.geometricGap_four_le d hd)
    escalaLongitud_pos.le

/-- From `d = 5` on, the step is strictly larger than the cell. -/
theorem Lsbpk_lt_longitudPaso {d : ℕ} (hd : 5 ≤ d) : Lsbpk < longitudPaso d := by
  rw [← longitudPaso_cuatro]
  have h4 : (4 : ℕ) ∈ {d : ℕ | 4 ≤ d} := le_refl 4
  have hd' : d ∈ {d : ℕ | 4 ≤ d} := by
    change 4 ≤ d
    omega
  exact mul_lt_mul_of_pos_left
    (Gnomon.geometricGap_strictMonoOn_ge_four h4 hd' (by omega)) escalaLongitud_pos

/-- Asymptotic ceiling of the step: the laboratory scale times `δ_∞ = C_∞ − 1`
(Szegő, `D8`). No finite dimension reaches it. -/
def longitudPasoInf : ℝ := escalaLongitud * Gnomon.deltaInf

/-- Every step of an open dimension lies strictly below the asymptotic one. -/
theorem longitudPaso_lt_longitudPasoInf {d : ℕ} (hd : 4 ≤ d) :
    longitudPaso d < longitudPasoInf :=
  mul_lt_mul_of_pos_left (Gnomon.geometricGap_lt_deltaInf d hd) escalaLongitud_pos

/-- **Range of the step.** `Lsbpk` is the floor (`d = 4`) and `longitudPasoInf` the
ceiling (`d → ∞`). Higher dimensions live inside that range and do not exclude
`d = 4`: the cell is that of the first open dimension. -/
theorem paso_en_rango {d : ℕ} (hd : 4 ≤ d) :
    Lsbpk ≤ longitudPaso d ∧ longitudPaso d < longitudPasoInf :=
  ⟨Lsbpk_le_longitudPaso hd, longitudPaso_lt_longitudPasoInf hd⟩

/-- **Both ends are sharp.** The floor is attained (`longitudPaso_cuatro`) and the
ceiling is approached without being crossed: the step tends to `longitudPasoInf` as
`d → ∞` (Szegő limit, `D8`). Neither bound on `C_Nava` can be broken, and neither
is superfluous. -/
theorem longitudPaso_tendsto_longitudPasoInf :
    Filter.Tendsto longitudPaso Filter.atTop (nhds longitudPasoInf) := by
  have h : Filter.Tendsto (fun d : ℕ => Gnomon.geometricGap d) Filter.atTop
      (nhds Gnomon.deltaInf) := by
    unfold Gnomon.geometricGap Gnomon.deltaInf
    exact Gnomon.limite_szego_CoherenceConstant.sub_const 1
  exact h.const_mul escalaLongitud

/-- The geometric defect is positive exactly outside the seeds `d = 2, 3`. -/
theorem geometricGap_pos_iff {d : ℕ} (hd : 2 ≤ d) :
    0 < Gnomon.geometricGap d ↔ ¬ (d = 2 ∨ d = 3) := by
  have h := Gnomon.CoherenceConstant_eq_one_iff d hd
  rw [Gnomon.CoherenceConstant_eq_one_add_geometricGap] at h
  have hn := geometricGap_nonneg hd
  constructor
  · intro hp hc
    have h1 := h.mpr hc
    linarith
  · intro hnc
    by_contra hnp
    have hz : Gnomon.geometricGap d = 0 := le_antisymm (not_lt.mp hnp) hn
    exact hnc (h.mp (by rw [hz]; ring))

/-- **Bridge with `D22`.** The step measures something exactly when the elementary
pair `(T_d, P_d)` has positive defect: without defect (saturation at `d = 2, 3`)
there is no cell; with defect (from `d = 4`) the step is positive. -/
theorem longitudPaso_pos_iff_defect_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < longitudPaso d ↔ 0 < (posicionTransporteTdPd hd).defect := by
  have h1 : 0 < longitudPaso d ↔ 0 < Gnomon.geometricGap d := by
    unfold longitudPaso
    exact mul_pos_iff_of_pos_left escalaLongitud_pos
  have h2 : 0 < (posicionTransporteTdPd hd).defect ↔ ¬ (d = 2 ∨ d = 3) := by
    have h3 := defectIntrinseco_pos_iff (evaluacionTdPd hd)
    rw [saturada_TdPd_iff hd] at h3
    exact h3
  rw [h1, h2, geometricGap_pos_iff hd]

/-! ## Connection with the path graph of `D3` -/

/-- Path of `k` consecutive minimal steps in `pathGraph d`. -/
def CaminoMinimo {d k : ℕ} (γ : Fin (k + 1) → Fin d) : Prop :=
  ∀ i : Fin k, PasoMinimo (γ i.castSucc) (γ i.succ)

/-- A minimal path is a path of edges of `pathGraph d`. -/
theorem caminoMinimo_iff_aristas {d k : ℕ} (γ : Fin (k + 1) → Fin d) :
    CaminoMinimo γ ↔ ∀ i : Fin k, (GrafoTP d).Adj (γ i.castSucc) (γ i.succ) := by
  unfold CaminoMinimo
  exact forall_congr' fun _ => pasoMinimo_iff_adj

/-- Physical length of a path of `k` minimal steps in dimension `d`. -/
def longitudCamino (d k : ℕ) : ℝ := (k : ℝ) * longitudPaso d

/-- The distance of `MaximumSpeed` is the length of a path of `k` minimal steps in
`d = 4`. -/
theorem distanciaRecorrida_eq_longitudCamino (k : ℕ) :
    VelocidadMaximaRegistrable.distanciaRecorrida k = longitudCamino 4 k := by
  unfold VelocidadMaximaRegistrable.distanciaRecorrida longitudCamino
  rw [longitudPaso_cuatro]

/-- **Closure of the bridge.** Every admissible process of `k` minimal steps of the
path in `d = 4` has mean speed `≤ c`, with the length given by the defect of
`(T_d, P_d)` through the calibration `longitudPaso`. -/
theorem velocidad_camino_le_luz {k : ℕ} (hk : 1 ≤ k)
    (P : VelocidadMaximaRegistrable.ProcesoTransporte k) :
    longitudCamino 4 k / P.duracion ≤ cSI := by
  rw [← distanciaRecorrida_eq_longitudCamino]
  exact P.velocidadMedia_le_luz hk

/-! ## Step over tick is `c`: the definition of the tick read backwards -/

/-- The two floors carry the same factor `y = lsubCanal`: the spatial one is `y · l_P`
and the temporal one is `y · t_P`. On division, `y` cancels. -/
theorem razon_pisos_es_Planck :
    Lsbpk / Tausbpk = longitudPlanckCODATA / tiempoPlanckCODATA := by
  rw [Tausbpk_eq_lsub_tiempoPlanck]
  unfold Lsbpk
  exact mul_div_mul_left _ _ lsubCanal_pos.ne'

/-- The elementary step of `H_4` over the tick is `c`. It is the definition
`τ_sbpk := L_sbpk / c_lab` read backwards: `c` is the laboratory input and the tick
is what is obtained. -/
theorem paso_entre_tick_es_c : longitudPaso 4 / Tausbpk = cSI := by
  rw [longitudPaso_cuatro, VelocidadMaximaRegistrable.cota_es_velocidad_maxima]
  exact velocidad_coincide

end PasoElementalCelda

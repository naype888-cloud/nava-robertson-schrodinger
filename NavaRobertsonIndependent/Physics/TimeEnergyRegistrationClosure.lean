import NavaRobertsonIndependent.Physics.SchwarzschildCollapse

/-!
# SBPK closure: tick, three energy scales and operational reach (Mathlib-only port)

Self-contained port of `E10_Cierre_10_Registro_Tiempo_Energia_Sbpk.lean` from the
canonical corpus (`BACQM_constructor_canonical`), companion of
`PAPERS/PAPER_Cierre_Registro_Tiempo_Energia_SBPK.pdf`. The mathematics is the same;
here `ℏ`, `c`, `k_B` are the exact SI constants of this package (`hbarSI`, `cSI`,
`kBSI`) and `Ω_b` is the documented constant of `SubPlanckianLimit`. The Twin Eons
realization (`Par`, `GerminacionCapa5`), not ported, and the Physlib joint are
omitted.

## Status of each block

* **Definitions / calibration**: `tiempoFisico n = n * Tausbpk`; `energiaMarcha`,
  `energiaColapso`, `energiaResolucion` as multiples of `E_P` by powers of `y`. The
  hierarchy and the products are algebraic consequences of those definitions.
* **Visible physical hypothesis**: `RelacionPlanckNewton G lP` in the gravitational
  theorems; spectral ceiling `ΔH ≤ E_P / (2 y)` in the Mandelstam–Tamm bridge
  (`DispersionAdmisible`).
* **Operational reach**: the collapse boundary is algebraic. The Compton length of
  `energiaColapso` and the Schwarzschild radius of `energiaResolucion` coincide and
  exceed the cell by the factor `2 / q`.
-/

noncomputable section

open LimiteSubPlanckiano ColapsoSchwarzschild

namespace CierreRegistroTiempoEnergiaSbpk

/-- A single amplitude for the whole package. -/
abbrev y : ℝ := ySbpk

theorem amplitud_cuadratura : y ^ 2 = channelSubQuantum := ySbpk_sq

theorem amplitud_pos : 0 < y := ySbpk_pos

/-- Sufficient bound to order the three energies; it uses no tuned decimals. -/
theorem amplitud_lt_mitad : y < 1 / 2 := by
  have hd := deltaD4_lt
  have hd0 := deltaD4_pos
  have hb := Omega_b_lt_uno
  have hd2 : deltaD4 ^ 2 < (1 / 4 : ℝ) := by nlinarith
  have hq : channelSubQuantum < (1 / 4 : ℝ) := by
    unfold channelSubQuantum
    have hmul := mul_lt_mul_of_pos_right hb (sq_pos_of_pos hd0)
    nlinarith
  have hy := amplitud_pos
  have hsq := amplitud_cuadratura
  nlinarith

/-- Physical duration of `n` ticks, with one tick calibrated by the SBPK cell. -/
def tiempoFisico (n : ℕ) : ℝ := (n : ℝ) * Tausbpk

theorem tiempo_cero_iff (n : ℕ) : tiempoFisico n = 0 ↔ n = 0 := by
  simp [tiempoFisico, ne_of_gt Tausbpk_pos]

theorem primer_tick : tiempoFisico 1 = Tausbpk := by simp [tiempoFisico]

theorem tiempo_positivo_iff (n : ℕ) : 0 < tiempoFisico n ↔ 0 < n := by
  unfold tiempoFisico
  rw [mul_pos_iff_of_pos_right Tausbpk_pos]
  exact_mod_cast (Iff.rfl : 0 < n ↔ 0 < n)

theorem piso_temporal {n : ℕ} (hn : 1 ≤ n) : Tausbpk ≤ tiempoFisico n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa [tiempoFisico] using mul_le_mul_of_nonneg_right hnR Tausbpk_pos.le

/-- `k` jumps that cost at least `k` ticks cost at least `k` SBPK intervals. -/
theorem transporte_cuesta_tiempo {k n : ℕ} (h : k ≤ n) :
    (k : ℝ) * Tausbpk ≤ tiempoFisico n := by
  apply mul_le_mul_of_nonneg_right _ Tausbpk_pos.le
  exact_mod_cast h

/-- Exact SI `k_B`: `1.380649e-23 J/K`. -/
def kBSI : ℝ := (1380649 : ℝ) / 10 ^ 29

theorem kBSI_pos : 0 < kBSI := by norm_num [kBSI]

abbrev EP : ℝ := energiaPlanck longitudPlanckCODATA

theorem EP_pos : 0 < EP :=
  div_pos (mul_pos hbarSI_pos cSI_pos) longitudPlanckCODATA_pos

/-- Running energy threshold, in coherent Planck units. -/
def energiaMarcha : ℝ := y ^ 2 * EP

/-- Conjugate resolution energy. -/
def energiaResolucion : ℝ := EP / y

/-- Normalized gravitational boundary; its Schwarzschild bridge is proved below. -/
def energiaColapso : ℝ := y / 2 * EP

/-- Temperature coherent with `EP`; avoids equating independent roundings. -/
def temperaturaMarcha : ℝ := energiaMarcha / kBSI

theorem umbral_temperatura_positivo : 0 < temperaturaMarcha :=
  div_pos (mul_pos (sq_pos_of_pos amplitud_pos) EP_pos) kBSI_pos

theorem temperatura_desde_remanente :
    temperaturaMarcha = channelSubQuantum * (EP / kBSI) := by
  unfold temperaturaMarcha energiaMarcha
  rw [amplitud_cuadratura]
  ring

theorem conversion_termica : kBSI * temperaturaMarcha = energiaMarcha := by
  unfold temperaturaMarcha
  field_simp [ne_of_gt kBSI_pos]

/-- Speed joint between the sub-Planckian module and the collapse module. -/
theorem velocidad_coincide : velocidadMaximaRegistrada = cSI := rfl

theorem tau_eq_y_lP_div_c : Tausbpk = y * longitudPlanckCODATA / cSI := by
  unfold Tausbpk Lsbpk
  rw [velocidad_coincide]
  rfl

theorem resolucion_por_longitud : energiaResolucion = hbarSI * cSI / Lsbpk := by
  unfold energiaResolucion EP energiaPlanck Lsbpk
  change (hbarSI * cSI / longitudPlanckCODATA) / y =
    hbarSI * cSI / (y * longitudPlanckCODATA)
  field_simp

theorem resolucion_por_tiempo : energiaResolucion * Tausbpk = hbarSI := by
  rw [tau_eq_y_lP_div_c]
  unfold energiaResolucion EP energiaPlanck
  field_simp [ne_of_gt amplitud_pos, ne_of_gt longitudPlanckCODATA_pos,
    ne_of_gt cSI_pos]

/-- `G` and `lP` must satisfy the Planck identity: visible hypothesis of the bridge. -/
theorem colapso_es_schwarzschild {G : ℝ} (hG : 0 < G)
    (hP : RelacionPlanckNewton G longitudPlanckCODATA) :
    energiaColapsoSbpk G = energiaColapso := by
  rw [energiaColapsoCODATA_eq_half_lsub_EPlanck hG hP]
  unfold energiaColapso
  change (1 / 2) * y * EP = y / 2 * EP
  ring

theorem jerarquia_energetica :
    0 < energiaMarcha ∧ energiaMarcha < energiaColapso ∧
    energiaColapso < EP ∧ EP < energiaResolucion := by
  have hy := amplitud_pos
  have hy2 := amplitud_lt_mitad
  have he := EP_pos
  have hsmall : y ^ 2 < y / 2 := by nlinarith
  refine ⟨mul_pos (sq_pos_of_pos hy) he, ?_, ?_, ?_⟩
  · exact mul_lt_mul_of_pos_right hsmall he
  · change y / 2 * EP < EP
    nlinarith [mul_lt_mul_of_pos_right (show y / 2 < 1 by linarith) he]
  · unfold energiaResolucion
    apply (lt_div_iff₀ hy).2
    nlinarith [mul_lt_mul_of_pos_left (show y < 1 by linarith) he]

theorem producto_colapso_resolucion : energiaColapso * energiaResolucion = EP ^ 2 / 2 := by
  unfold energiaColapso energiaResolucion
  field_simp [ne_of_gt amplitud_pos]

theorem producto_marcha_resolucion : energiaMarcha * energiaResolucion ^ 2 = EP ^ 3 := by
  unfold energiaMarcha energiaResolucion
  field_simp [ne_of_gt amplitud_pos]

/-- Energy realized by a sector of density `rho` in the volume of the cell. -/
def energiaRealizada (rho : ℝ) : ℝ := rho * Vsbpk

def masaRealizada (rho : ℝ) : ℝ := energiaRealizada rho / cSI ^ 2

def densidadColapso : ℝ := energiaColapso / Vsbpk

def densidadMarcha : ℝ := energiaMarcha / Vsbpk

theorem energia_masa (rho : ℝ) :
    energiaRealizada rho = masaRealizada rho * cSI ^ 2 := by
  unfold masaRealizada
  field_simp [ne_of_gt cSI_pos]

theorem realizacion_subcolapso {rho : ℝ} (hr : 0 < rho)
    (hc : rho < densidadColapso) :
    0 < energiaRealizada rho ∧ energiaRealizada rho < energiaColapso ∧
    0 < masaRealizada rho := by
  have hE : 0 < energiaRealizada rho := mul_pos hr Vsbpk_pos
  refine ⟨hE, ?_, div_pos hE (sq_pos_of_pos cSI_pos)⟩
  exact (lt_div_iff₀ Vsbpk_pos).mp hc

theorem marcha_es_realizable_bajo_frontera :
    0 < densidadMarcha ∧ densidadMarcha < densidadColapso ∧
    energiaRealizada densidadMarcha = energiaMarcha := by
  refine ⟨div_pos jerarquia_energetica.1 Vsbpk_pos,
    div_lt_div_of_pos_right jerarquia_energetica.2.1 Vsbpk_pos, ?_⟩
  unfold energiaRealizada densidadMarcha
  exact div_mul_cancel₀ _ (ne_of_gt Vsbpk_pos)

theorem fraccion_densidad_marcha : densidadMarcha / densidadColapso = 2 * y := by
  unfold densidadMarcha densidadColapso energiaMarcha energiaColapso
  field_simp [ne_of_gt Vsbpk_pos, ne_of_gt amplitud_pos, ne_of_gt EP_pos]

/-! ## Bridge with Mandelstam–Tamm

With the quantum speed limit `ℏ / 2 ≤ τ ΔH` and a spectral ceiling `ΔH ≤ E_MT`,
every physical duration is at least `Tausbpk`. The ceiling is the physical
hypothesis of the sector and equals `E_P / (2 y)`. Since `E_MT` is defined from
`Tausbpk`, ceiling and floor are equivalent: the hypothesis states the floor as a
bound on the spectrum of the sector.
-/

/-- Energy conjugate to the minimal registrable time. -/
def energiaMandelstamTamm : ℝ := hbarSI / (2 * Tausbpk)

theorem energiaMandelstamTamm_pos : 0 < energiaMandelstamTamm :=
  div_pos hbarSI_pos (mul_pos (by norm_num) Tausbpk_pos)

theorem tausbpk_mul_energiaMandelstamTamm :
    Tausbpk * energiaMandelstamTamm = hbarSI / 2 := by
  unfold energiaMandelstamTamm
  field_simp [ne_of_gt Tausbpk_pos]

/-- Dimensional Mandelstam–Tamm form for a duration and a spread. -/
def MandelstamTammFisico (tau deltaH : ℝ) : Prop :=
  hbarSI / 2 ≤ tau * deltaH

/-- Spectral ceiling of the registrable sector. -/
def DispersionAdmisible (deltaH : ℝ) : Prop :=
  0 ≤ deltaH ∧ deltaH ≤ energiaMandelstamTamm

/-- Spectral ceiling of the sector, in Planck units. -/
theorem techo_espectral_en_planck : energiaMandelstamTamm = EP / (2 * y) := by
  unfold energiaMandelstamTamm
  rw [tau_eq_y_lP_div_c]
  unfold EP energiaPlanck
  field_simp [ne_of_gt amplitud_pos, ne_of_gt longitudPlanckCODATA_pos,
    ne_of_gt cSI_pos]

/-- One tick is the quantum speed limit of the spectral ceiling. -/
theorem tick_es_cota_mandelstam_tamm {tau deltaH : ℝ} (htau : 0 ≤ tau)
    (hMT : MandelstamTammFisico tau deltaH) (hE : DispersionAdmisible deltaH) :
    tiempoFisico 1 ≤ tau := by
  rw [primer_tick]
  have hscale : tau * deltaH ≤ tau * energiaMandelstamTamm :=
    mul_le_mul_of_nonneg_left hE.2 htau
  have hfloor : hbarSI / 2 ≤ tau * energiaMandelstamTamm := le_trans hMT hscale
  have hboundary := tausbpk_mul_energiaMandelstamTamm
  have hEpos := energiaMandelstamTamm_pos
  nlinarith

/-! ## Operational reach of the cell

`energiaColapso` is defined by the Schwarzschild relation with radius `Lsbpk`,
smaller than `lP`. In that regime the boundary is algebraic, not a
horizon-formation threshold: the Compton length of `energiaColapso` and the
Schwarzschild radius of `energiaResolucion` coincide and exceed the cell by the
factor `2 / q`. `energiaResolucion = ℏ c / Lsbpk` is the localization scale up to
order-one factors (minimal operational length, Mead 1964; Garay 1995).
-/

/-- Reduced Compton length of the collapse energy. -/
theorem compton_colapso :
    hbarSI * cSI / energiaColapso = 2 / y ^ 2 * Lsbpk := by
  have h1 := hbarSI_pos.ne'
  have h2 := cSI_pos.ne'
  have h3 := longitudPlanckCODATA_pos.ne'
  have h4 := amplitud_pos.ne'
  unfold energiaColapso EP energiaPlanck Lsbpk
  change hbarSI * cSI / (y / 2 * (hbarSI * cSI / longitudPlanckCODATA)) =
    2 / y ^ 2 * (y * longitudPlanckCODATA)
  field_simp

/-- Schwarzschild radius of the resolution energy, under the Planck relation. -/
theorem radio_schwarzschild_resolucion {G : ℝ}
    (hP : RelacionPlanckNewton G longitudPlanckCODATA) :
    2 * G * energiaResolucion / cSI ^ 4 = 2 / y ^ 2 * Lsbpk := by
  have h1 := hbarSI_pos.ne'
  have h2 := cSI_pos.ne'
  have h3 := longitudPlanckCODATA_pos.ne'
  have h4 := amplitud_pos.ne'
  have hG : G = longitudPlanckCODATA ^ 2 * cSI ^ 3 / hbarSI := by
    unfold RelacionPlanckNewton at hP
    field_simp at hP ⊢
    linarith
  subst hG
  unfold energiaResolucion EP energiaPlanck Lsbpk
  change 2 * (longitudPlanckCODATA ^ 2 * cSI ^ 3 / hbarSI) *
      (hbarSI * cSI / longitudPlanckCODATA / y) / cSI ^ 4 =
    2 / y ^ 2 * (y * longitudPlanckCODATA)
  field_simp

theorem factor_celda_gt : 8 < 2 / y ^ 2 := by
  have hy := amplitud_pos
  have hy2 := amplitud_lt_mitad
  rw [lt_div_iff₀ (sq_pos_of_pos hy)]
  nlinarith

/-- Compton(E_col) = r_s(E_res), and both strictly exceed the cell. -/
theorem alcance_operacional {G : ℝ}
    (hP : RelacionPlanckNewton G longitudPlanckCODATA) :
    hbarSI * cSI / energiaColapso = 2 * G * energiaResolucion / cSI ^ 4 ∧
      Lsbpk < 2 * G * energiaResolucion / cSI ^ 4 := by
  rw [compton_colapso, radio_schwarzschild_resolucion hP]
  exact ⟨rfl, lt_mul_of_one_lt_left Lsbpk_pos (by linarith [factor_celda_gt])⟩

/-! ## Link with cosmology: the cell as a Hubble patch

In flat general relativity, the Misner–Sharp mass inside the apparent horizon
`R = c / H` is `c² R / (2 G)`. With `R = Lsbpk` the rate is
`H = c / Lsbpk = 1 / Tausbpk` and the enclosed energy is exactly
`energiaColapsoSbpk`: the Schwarzschild collapse on the cell coincides with the
energy of a Hubble patch of that radius. The natural link of `E_col` with cosmology
is therefore a maximal expansion rate `1 / Tausbpk`, not an inflation or
unification scale.
-/

/-- Expansion rate whose Hubble radius is `Lsbpk`. -/
def hubbleCelda : ℝ := cSI / Lsbpk

theorem hubbleCelda_eq_inv_tau : hubbleCelda = 1 / Tausbpk := by
  unfold hubbleCelda Tausbpk
  rw [velocidad_coincide]
  field_simp [ne_of_gt Lsbpk_pos, ne_of_gt cSI_pos]

/-- `ℏ H_cell` is the resolution energy. -/
theorem hbar_hubbleCelda : hbarSI * hubbleCelda = energiaResolucion := by
  rw [resolucion_por_longitud]
  unfold hubbleCelda
  ring

/-- Flat Friedmann energy density: `ε = 3 H² c² / (8 π G)`. -/
def densidadFriedmann (G H : ℝ) : ℝ := 3 * H ^ 2 * cSI ^ 2 / (8 * Real.pi * G)

/-- The energy of the sphere of radius `Lsbpk` at Friedmann density with
`H = c / Lsbpk` is the Schwarzschild collapse energy. -/
theorem energia_esfera_horizonte {G : ℝ} (hG : 0 < G) :
    4 * Real.pi / 3 * Lsbpk ^ 3 * densidadFriedmann G hubbleCelda =
      energiaColapsoSbpk G := by
  unfold energiaColapsoSbpk
  rw [energiaSchwarzschild_eq_cuatro]
  unfold densidadFriedmann hubbleCelda
  field_simp [ne_of_gt hG, ne_of_gt Lsbpk_pos, ne_of_gt cSI_pos,
    Real.pi_pos.ne']
  ring

/-- Joint certificate (without the Twin Eons realization, not ported). -/
theorem cierre_sbpk_independiente :
    (∀ n : ℕ, tiempoFisico n = 0 ↔ n = 0) ∧
    (0 < energiaMarcha ∧ energiaMarcha < energiaColapso ∧
      energiaColapso < EP ∧ EP < energiaResolucion) ∧
    energiaResolucion * Tausbpk = hbarSI ∧
    energiaColapso * energiaResolucion = EP ^ 2 / 2 ∧
    energiaMarcha * energiaResolucion ^ 2 = EP ^ 3 ∧
    densidadMarcha / densidadColapso = 2 * y :=
  ⟨tiempo_cero_iff, jerarquia_energetica, resolucion_por_tiempo,
    producto_colapso_resolucion, producto_marcha_resolucion,
    fraccion_densidad_marcha⟩

end CierreRegistroTiempoEnergiaSbpk

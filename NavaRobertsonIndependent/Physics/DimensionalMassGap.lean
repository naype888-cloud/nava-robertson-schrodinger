import NavaRobertsonIndependent.Physics.SubPlanckianLimit
import NavaRobertsonIndependent.Physics.SchwarzschildCollapse
import NavaRobertsonIndependent.Mathematics.D7_Niven
import NavaRobertsonIndependent.Mathematics.D14_SzegoGapExcess

/-!
# Dimensional mass gap: the Robertson quantum in mass units

Mathlib-only port of the canonical constructor
`E10_Cierre_07_Constructor_Salto_Masa_YM_Puente.lean`. The gap used is that of the
Robertson obstruction in each `H_d`, `δ(d) = C_Nava(d) − 1` (`D8`, `D25`), packaged
in `GapDefectRobertson`; the identities are proved directly with Mathlib. This
module does not formalize a Yang–Mills theory: the "mass gap" reading is an
interpretation; the proved content is the Robertson gap and its translation into
mass.

## What is proved

With `masaPlanckSbpk = E_P / c²` (the Planck mass, `√(ℏc/G)`), define

```
sbpkMassGap = (1/2) · lsubCanal · masaPlanckSbpk
```

and three identities are certified:

1. `sbpkMassGap_eq_masaSchwarzschild_Lsbpk`: it equals the Schwarzschild collapse
   mass on `Lsbpk` (reuses `energiaColapsoCODATA_eq_half_lsub_EPlanck`).
2. `sbpkMassGap_eq_half_gap_sqrtOmega_MP`: for every witness
   `Y : GapDefectRobertson 4`,
   `sbpkMassGap = (1/2) · (Y.gap · √Ω_b) · masaPlanckSbpk`.
   That is: the mass gap **is** the Robertson gap `Y.gap = deltaD4`, dressed by
   the baryonic window `√Ω_b` and the Planck mass.
3. `sbpkMassGap_sq`: `sbpkMassGap² = (1/4) · channelSubQuantum · masaPlanckSbpk²`. The
   quadratic object of the framework (`channelSubQuantum`, which fixes area and running
   temperature) reappears in the **square** of the mass: the mass gap is the only
   rung **linear** in the gap `deltaD4`.

## The gap is uniform and does not close in any limit

The question all of this descends from is algebraic: **for which `d` does
Robertson's 1929 inequality saturate with equality?** For the path-graph pair,
saturation requires `cos²(π/(d+1)) = (d−1)/4`, which **has no solution** for any
`d ≥ 4` (`Gnomon.no_reposición_saturacion_camino`, D7). Hence
(`gap_no_colapsa_OK`):

* `geometricGap d > 0` for **every** physical dimension `d ≥ 4`;
* bounded below by `geometricGap 4 = deltaD4 > 0` (its global minimum);
* bounded above by `deltaInf = C_∞ − 1`, never reaching it;
* and `geometricGap d → deltaInf > 0` as `d → ∞`: **the gap does not close in the
  limit**, it converges to a strictly positive value.

Dressed with `√Ω_b` and `M_P`, this gives `saltoMasaDim d` (with
`saltoMasaDim 4 = sbpkMassGap`) and the certificate `salto_masa_no_colapsa_OK`:
the mass gap is positive, uniform over `d ≥ 4`, with floor `sbpkMassGap` and
upper bound `techoSaltoMasaDim > 0`, which is also its limit as `d → ∞`.

## SI values (inherit the CODATA uncertainty of `l_P` through `M_P`)

```text
deltaD4        = 8.4785516e-3            (Robertson gap in H_4, π-exact)
Omega_b        = 0.049543679             (√Ω_b = 0.2225841)
lsubCanal      = deltaD4·√Ω_b = 1.8871907e-3
masaPlanckSbpk = E_P/c² = √(ℏc/G) = 2.176434e-8 kg = 1.220890e19 GeV/c²

sbpkMassGap  = (1/2)·lsubCanal·M_P
               = M_P / 1059.776
               = 2.05367e-11 kg
               = 1.15203e16 GeV/c²
E_grav         = sbpkMassGap·c² = 1.84575e6 J
```
-/

noncomputable section

open LimiteSubPlanckiano
open ColapsoSchwarzschild
open Filter Topology

namespace SaltoMasaDimensional

/-! ## 0. The Robertson gap in `H_d`

`GapDefectRobertson d` carries the gap of the Robertson obstruction in `H_d`:
`δ(d) = C_Nava(d) − 1`, positive from `d = 4` (`D8`). The spectral infrastructure
(maximal-tension state `D5`, spectrum `D6`, impossibility of saturation `D7`/`D13`)
is certified in Layer 1; only the value of the gap is used here. -/
structure GapDefectRobertson (d : ℕ) where
  gap : ℝ
  gap_eq_delta : gap = Gnomon.geometricGap d
  gap_pos : 0 < gap

/-- The Robertson gap exists on the whole tail `d ≥ 4`: it is `geometricGap d`, positive
by the core (D8). -/
theorem gap_defect_robertson_d_ge_4 (d : ℕ) (hd : 4 ≤ d) :
    Nonempty (GapDefectRobertson d) :=
  ⟨{ gap := Gnomon.geometricGap d
     gap_eq_delta := rfl
     gap_pos := Gnomon.geometricGap_pos_of_four_le d hd }⟩

/-! ## 1. The Planck mass of the package and the mass gap -/

/-- Planck mass in the package convention: `M_P = E_P / c²` with `E_P = ℏ c / l_P`
and `l_P` the CODATA anchor. Equivalent to `√(ℏc/G)`. -/
def masaPlanckSbpk : ℝ :=
  energiaPlanck longitudPlanckCODATA / cSI ^ 2

/-- **Dimensional mass gap of the model.** The dimensionless gap `lsubCanal`
(linear in the Robertson gap `deltaD4`) times half the Planck mass. It is
`energiaColapsoSbpk G / c²` for any admissible `G`. -/
def sbpkMassGap : ℝ :=
  (1 / 2) * lsubCanal * masaPlanckSbpk

/-! ## 2. Positivity and sub-Planckian character -/

theorem energiaPlanck_longitudPlanckCODATA_pos :
    0 < energiaPlanck longitudPlanckCODATA := by
  unfold energiaPlanck
  exact div_pos (mul_pos hbarSI_pos cSI_pos) longitudPlanckCODATA_pos

theorem masaPlanckSbpk_pos : 0 < masaPlanckSbpk := by
  unfold masaPlanckSbpk
  exact div_pos energiaPlanck_longitudPlanckCODATA_pos
    (pow_pos cSI_pos 2)

theorem sbpkMassGap_pos : 0 < sbpkMassGap := by
  unfold sbpkMassGap
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  exact mul_pos (mul_pos h2 lsubCanal_pos) masaPlanckSbpk_pos

/-- The mass gap lies strictly below the Planck mass: it is a **sub-Planckian** gap,
by the same factor `< 1` that governs the whole cell. -/
theorem sbpkMassGap_lt_masaPlanckSbpk : sbpkMassGap < masaPlanckSbpk := by
  unfold sbpkMassGap
  have hfac : 1 / 2 * lsubCanal < 1 := by
    have h := lsubCanal_lt_uno
    have h0 := lsubCanal_nonneg
    nlinarith
  calc 1 / 2 * lsubCanal * masaPlanckSbpk
      < 1 * masaPlanckSbpk :=
        mul_lt_mul_of_pos_right hfac masaPlanckSbpk_pos
    _ = masaPlanckSbpk := one_mul _

/-! ## 3. Bridge with the Schwarzschild collapse mass -/

/-- The mass gap **is** the mass whose Schwarzschild radius is `Lsbpk`, for every
`G > 0` satisfying the accepted Planck–Newton relation. Reuses
`energiaColapsoCODATA_eq_half_lsub_EPlanck`, already certified. -/
theorem sbpkMassGap_eq_masaSchwarzschild_Lsbpk
    {G : ℝ} (hG : 0 < G)
    (hPlanck : RelacionPlanckNewton G longitudPlanckCODATA) :
    masaSchwarzschild G Lsbpk = sbpkMassGap := by
  have h := energiaColapsoCODATA_eq_half_lsub_EPlanck hG hPlanck
  unfold energiaColapsoSbpk energiaSchwarzschild at h
  have hc : (cSI : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt cSI_pos)
  have hgoal : masaSchwarzschild G Lsbpk
      = (1 / 2 * lsubCanal * energiaPlanck longitudPlanckCODATA)
          / cSI ^ 2 := by
    rw [eq_div_iff hc]
    linear_combination h
  rw [hgoal]
  unfold sbpkMassGap masaPlanckSbpk
  ring

/-- Corollary: the Schwarzschild radius of the mass gap is exactly the side of the
minimal registration cell. -/
theorem sbpkMassGap_radioSchwarzschild_eq_Lsbpk
    {G : ℝ} (hG : 0 < G)
    (hPlanck : RelacionPlanckNewton G longitudPlanckCODATA) :
    RadioSchwarzschild G sbpkMassGap Lsbpk := by
  rw [← sbpkMassGap_eq_masaSchwarzschild_Lsbpk hG hPlanck]
  exact masaSchwarzschild_certifica_radio hG

/-! ## 4. The mass gap is the Robertson gap, dressed -/

/-- The Robertson gap in the first open dimension is exactly `deltaD4`. -/
theorem gap_eq_deltaD4 (Y : GapDefectRobertson 4) : Y.gap = deltaD4 := by
  have h := Y.gap_eq_delta
  simpa [deltaD4] using h

/-- `lsubCanal` factored with the baryonic window as `√Ω_b`:
`√(Ω_b · deltaD4²) = deltaD4 · √Ω_b` because `deltaD4 ≥ 0`. -/
theorem lsubCanal_eq_deltaD4_mul_sqrt_Omega_b :
    lsubCanal = deltaD4 * Real.sqrt Omega_b := by
  have h : channelSubQuantum = deltaD4 ^ 2 * Omega_b := by
    unfold channelSubQuantum
    ring
  unfold lsubCanal
  rw [h, Real.sqrt_mul (sq_nonneg deltaD4), Real.sqrt_sq (le_of_lt deltaD4_pos)]

/-- Witness-free form (a pure number of the framework): the mass gap is
`(1/2) · deltaD4 · √Ω_b · M_P`. Linear in the gap. -/
theorem sbpkMassGap_eq_half_deltaD4_sqrtOmega_MP :
    sbpkMassGap
      = (1 / 2) * deltaD4 * Real.sqrt Omega_b * masaPlanckSbpk := by
  unfold sbpkMassGap
  rw [lsubCanal_eq_deltaD4_mul_sqrt_Omega_b]
  ring

/-- **Bridge theorem.** For every Robertson gap at `d = 4`, the dimensional mass gap
is its gap `Y.gap` (= `deltaD4`) carried by the baryonic window `√Ω_b` and the
Planck mass, with the Schwarzschild `1/2`. The mass gap **is** the Robertson gap,
dressed. -/
theorem sbpkMassGap_eq_half_gap_sqrtOmega_MP (Y : GapDefectRobertson 4) :
    sbpkMassGap
      = (1 / 2) * (Y.gap * Real.sqrt Omega_b) * masaPlanckSbpk := by
  rw [sbpkMassGap_eq_half_deltaD4_sqrtOmega_MP, gap_eq_deltaD4 Y]
  ring

/-- The square of the mass gap exhibits the quadratic seed `channelSubQuantum` — the same one
that fixes `Asbpk` and `ThetaMarchaSbpk` —: `M_gap² = (1/4) · q_sub · M_P²`. It shows
that the mass gap goes with the gap to the **first** power, while area and running
temperature go with the **second**. -/
theorem sbpkMassGap_sq :
    sbpkMassGap ^ 2 = (1 / 4) * channelSubQuantum * masaPlanckSbpk ^ 2 := by
  rw [← lsubCanal_sq]
  unfold sbpkMassGap
  ring

/-! ## 5. The gap at `d = 4` and joint certificate -/

/-- The Robertson gap exists in the first open dimension, `H_4`. -/
theorem gap_cuatro : Nonempty (GapDefectRobertson 4) :=
  gap_defect_robertson_d_ge_4 4 (le_refl 4)

structure CertificadoSaltoMasa where
  /-- The Robertson gap exists at `d = 4`. -/
  gap_d4 : Nonempty (GapDefectRobertson 4)
  /-- The dimensional mass gap is strictly positive. -/
  positivo : 0 < sbpkMassGap
  /-- And strictly sub-Planckian (below `M_P`). -/
  subplanckiano : sbpkMassGap < masaPlanckSbpk
  /-- It is the Robertson gap `Y.gap` dressed by `√Ω_b` and `M_P`. -/
  factor_lineal_en_gap : ∀ Y : GapDefectRobertson 4,
    sbpkMassGap
      = (1 / 2) * (Y.gap * Real.sqrt Omega_b) * masaPlanckSbpk
  /-- The square of the mass gap recovers the quadratic seed of the framework. -/
  cuadratura_en_qsub :
    sbpkMassGap ^ 2 = (1 / 4) * channelSubQuantum * masaPlanckSbpk ^ 2
  /-- Under the community bridges, its Schwarzschild radius is `Lsbpk`. -/
  colapso_schwarzschild : ∀ {G : ℝ}, 0 < G →
    RelacionPlanckNewton G longitudPlanckCODATA →
    RadioSchwarzschild G sbpkMassGap Lsbpk
  /-- And it coincides with the collapse mass of the Schwarzschild module. -/
  masa_es_colapso_sobre_c2 : ∀ {G : ℝ}, 0 < G →
    RelacionPlanckNewton G longitudPlanckCODATA →
    masaSchwarzschild G Lsbpk = sbpkMassGap

theorem certificado_salto_masa_OK : Nonempty CertificadoSaltoMasa :=
  ⟨{
    gap_d4 := gap_cuatro
    positivo := sbpkMassGap_pos
    subplanckiano := sbpkMassGap_lt_masaPlanckSbpk
    factor_lineal_en_gap := sbpkMassGap_eq_half_gap_sqrtOmega_MP
    cuadratura_en_qsub := sbpkMassGap_sq
    colapso_schwarzschild := fun hG hP =>
      sbpkMassGap_radioSchwarzschild_eq_Lsbpk hG hP
    masa_es_colapso_sobre_c2 := fun hG hP =>
      sbpkMassGap_eq_masaSchwarzschild_Lsbpk hG hP
  }⟩

/-! ## 6. The gap is uniform over `d ≥ 4` and does not close in any limit

Robertson's inequality and its saturation condition are algebra of inner-product
spaces: they do not distinguish the carrier (ℝ/ℂ, finite/infinite). The only thing
specific to the framework is the operator pair of the path graph. For that pair,
saturation requires `cos²(π/(d+1)) = (d−1)/4`, with no solution for `d ≥ 4` (Niven,
D7). The resulting defect `geometricGap d` is therefore a positive gap over the whole
physical tail, with floor `geometricGap 4`, not closing as `d → ∞`. -/

/-- `geometricGap d → deltaInf` as `d → ∞`, with `deltaInf = C_∞ − 1 > 0`: the gap
converges to a **strictly positive** value; it does not collapse in the limit.
Derived from `Gnomon.excesoGap_tendsto_zero` (`C_∞ − CoherenceConstant d → 0`). -/
theorem geometricGap_tendsto_deltaInf :
    Tendsto (fun d : ℕ => Gnomon.geometricGap d) atTop (𝓝 Gnomon.deltaInf) := by
  have h0 : Tendsto (fun d : ℕ => Gnomon.deltaInf - Gnomon.geometricGap d) atTop (𝓝 0) := by
    refine Gnomon.excesoGap_tendsto_zero.congr ?_
    intro d
    simp only [Gnomon.excesoGap, Gnomon.deltaInf, Gnomon.geometricGap]
    ring
  have h1 : Tendsto
      (fun d : ℕ => Gnomon.deltaInf - (Gnomon.deltaInf - Gnomon.geometricGap d))
      atTop (𝓝 (Gnomon.deltaInf - 0)) := h0.const_sub _
  simpa using h1

/-- **The gap does not collapse.** Dimensionless certificate: for every physical
dimension `d ≥ 4` the gap is positive, with floor `geometricGap 4 > 0` and ceiling
`deltaInf`, it converges to `deltaInf > 0` as `d → ∞`, and Niven saturation is
impossible at every `d`. -/
structure GapNoColapsa where
  positiva : ∀ d : ℕ, 4 ≤ d → 0 < Gnomon.geometricGap d
  piso : ∀ d : ℕ, 4 ≤ d → Gnomon.geometricGap 4 ≤ Gnomon.geometricGap d
  piso_pos : 0 < Gnomon.geometricGap 4
  techo : ∀ d : ℕ, 4 ≤ d → Gnomon.geometricGap d < Gnomon.deltaInf
  no_cierra_en_limite :
    Tendsto (fun d : ℕ => Gnomon.geometricGap d) atTop (𝓝 Gnomon.deltaInf)
  limite_pos : 0 < Gnomon.deltaInf
  saturacion_imposible : ∀ d : ℕ, 4 ≤ d →
    Real.cos (Real.pi / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4

theorem gap_no_colapsa_OK : Nonempty GapNoColapsa :=
  ⟨{
    positiva := fun d hd => Gnomon.geometricGap_pos_of_four_le d hd
    piso := fun d hd => Gnomon.geometricGap_four_le d hd
    piso_pos := Gnomon.geometricGap_pos_of_four_le 4 le_rfl
    techo := fun d hd => Gnomon.geometricGap_lt_deltaInf d hd
    no_cierra_en_limite := geometricGap_tendsto_deltaInf
    limite_pos := Gnomon.deltaInf_pos
    saturacion_imposible := fun d hd =>
      Gnomon.no_reposición_saturacion_camino d hd
  }⟩

/-! ## 7. Dimensional mass gap parametrized by `d` -/

/-- Dimensionless linear factor in dimension `d`: the gap `geometricGap d` times the
baryonic window `√Ω_b`. At `d = 4` it is `lsubCanal`. -/
def lsubCanalDim (d : ℕ) : ℝ :=
  Gnomon.geometricGap d * Real.sqrt Omega_b

/-- Dimensional mass gap in dimension `d`: `(1/2) · lsubCanalDim d · M_P`. -/
def saltoMasaDim (d : ℕ) : ℝ :=
  (1 / 2) * lsubCanalDim d * masaPlanckSbpk

/-- Upper bound (and limit as `d → ∞`) of the dimensional mass gap:
`(1/2) · √Ω_b · M_P · deltaInf`. -/
def techoSaltoMasaDim : ℝ :=
  (1 / 2) * Real.sqrt Omega_b * masaPlanckSbpk * Gnomon.deltaInf

theorem sqrt_Omega_b_pos : 0 < Real.sqrt Omega_b := by
  apply Real.sqrt_pos.mpr
  exact Omega_b_pos

/-- In the first open dimension the dimensional mass gap coincides with
`sbpkMassGap`. -/
theorem saltoMasaDim_four : saltoMasaDim 4 = sbpkMassGap := by
  have h : lsubCanalDim 4 = lsubCanal := by
    unfold lsubCanalDim
    rw [lsubCanal_eq_deltaD4_mul_sqrt_Omega_b]
    simp [deltaD4]
  unfold saltoMasaDim sbpkMassGap
  rw [h]

theorem saltoMasaDim_pos (d : ℕ) (hd : 4 ≤ d) : 0 < saltoMasaDim d := by
  unfold saltoMasaDim lsubCanalDim
  have hδ := Gnomon.geometricGap_pos_of_four_le d hd
  exact mul_pos (mul_pos (by norm_num) (mul_pos hδ sqrt_Omega_b_pos)) masaPlanckSbpk_pos

/-- **Uniform floor.** For every `d ≥ 4` the dimensional mass gap is at or above
`sbpkMassGap`: no physical regime lowers it. -/
theorem sbpkMassGap_le_saltoMasaDim (d : ℕ) (hd : 4 ≤ d) :
    sbpkMassGap ≤ saltoMasaDim d := by
  rw [← saltoMasaDim_four]
  unfold saltoMasaDim lsubCanalDim
  have hδ : Gnomon.geometricGap 4 ≤ Gnomon.geometricGap d := Gnomon.geometricGap_four_le d hd
  have hΩ : 0 ≤ Real.sqrt Omega_b := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt masaPlanckSbpk_pos)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact mul_le_mul_of_nonneg_right hδ hΩ

/-- **Uniform ceiling.** For every `d ≥ 4` the dimensional mass gap is strictly below
`techoSaltoMasaDim`: it never reaches the Szegő limit. -/
theorem saltoMasaDim_lt_techo (d : ℕ) (hd : 4 ≤ d) :
    saltoMasaDim d < techoSaltoMasaDim := by
  unfold saltoMasaDim lsubCanalDim techoSaltoMasaDim
  have hδ : Gnomon.geometricGap d < Gnomon.deltaInf := Gnomon.geometricGap_lt_deltaInf d hd
  have hpos : (0 : ℝ) < 1 / 2 * Real.sqrt Omega_b * masaPlanckSbpk :=
    mul_pos (mul_pos (by norm_num) sqrt_Omega_b_pos) masaPlanckSbpk_pos
  have key := mul_lt_mul_of_pos_left hδ hpos
  calc (1 / 2) * (Gnomon.geometricGap d * Real.sqrt Omega_b) * masaPlanckSbpk
      = (1 / 2 * Real.sqrt Omega_b * masaPlanckSbpk)
          * Gnomon.geometricGap d := by ring
    _ < (1 / 2 * Real.sqrt Omega_b * masaPlanckSbpk)
          * Gnomon.deltaInf := key
    _ = (1 / 2) * Real.sqrt Omega_b * masaPlanckSbpk
          * Gnomon.deltaInf := by ring

theorem techoSaltoMasaDim_pos : 0 < techoSaltoMasaDim := by
  unfold techoSaltoMasaDim
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) sqrt_Omega_b_pos) masaPlanckSbpk_pos)
    Gnomon.deltaInf_pos

/-- **No collapse in the limit.** `saltoMasaDim d → techoSaltoMasaDim > 0` as
`d → ∞`: the mass gap converges to a strictly positive value. -/
theorem saltoMasaDim_tendsto :
    Tendsto (fun d : ℕ => saltoMasaDim d) atTop (𝓝 techoSaltoMasaDim) := by
  have hC : techoSaltoMasaDim
      = ((1 / 2) * Real.sqrt Omega_b * masaPlanckSbpk)
          * Gnomon.deltaInf := by
    unfold techoSaltoMasaDim; ring
  rw [hC]
  have hbase := (geometricGap_tendsto_deltaInf).const_mul
    ((1 / 2) * Real.sqrt Omega_b * masaPlanckSbpk)
  refine hbase.congr ?_
  intro d
  simp only [saltoMasaDim, lsubCanalDim]
  ring

/-- **Dimensional no-collapse certificate.** The dimensional mass gap is positive and
uniform over the whole physical tail `d ≥ 4`: floor `sbpkMassGap`, ceiling
`techoSaltoMasaDim > 0`, and that ceiling is its limit as `d → ∞`. -/
structure SaltoMasaNoColapsa where
  positivo : ∀ d : ℕ, 4 ≤ d → 0 < saltoMasaDim d
  calibracion : saltoMasaDim 4 = sbpkMassGap
  piso : ∀ d : ℕ, 4 ≤ d → sbpkMassGap ≤ saltoMasaDim d
  techo : ∀ d : ℕ, 4 ≤ d → saltoMasaDim d < techoSaltoMasaDim
  no_cierra_en_limite :
    Tendsto (fun d : ℕ => saltoMasaDim d) atTop (𝓝 techoSaltoMasaDim)
  limite_pos : 0 < techoSaltoMasaDim

theorem salto_masa_no_colapsa_OK : Nonempty SaltoMasaNoColapsa :=
  ⟨{
    positivo := saltoMasaDim_pos
    calibracion := saltoMasaDim_four
    piso := sbpkMassGap_le_saltoMasaDim
    techo := saltoMasaDim_lt_techo
    no_cierra_en_limite := saltoMasaDim_tendsto
    limite_pos := techoSaltoMasaDim_pos
  }⟩

end SaltoMasaDimensional

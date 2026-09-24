import NavaRobertsonIndependent.Mathematics.D8_Szego
import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
import NavaRobertsonIndependent.Mathematics.D26a_OmegaFromPi

/-!
# Registrable sub-Planckian limit (Mathlib-only port)

Self-contained port of the canonical constructor
`E10_Cierre_04_Constructor_Limite_SubPlanckiano.lean` (corpus
`BACQM_constructor_canonical`, which depends on Physlib and on other corpus
modules) to Mathlib only. The mathematics is the same; the corpus chain
`pesoImagenReal = g_s · e^{-η_inf} = Ω_b` is replaced by the documented constant
of the framework, `Ω_b = 0.049543679` (proved to be that formula rounded, see
`Omega_b_desde_pi`), and the joints with unported modules (`AsubBekenstein`,
`Constructor_Vsub_Cubico`, Physlib constants) are removed.

## Dimensional convention: area is primary

The elementary unit is an *area*: `Asub scale = scale * Ω_b * geometricGap 4 ^ 2`;
length is its square root and volume is the cube of that length. This module
instantiates the convention with `scale = longitudPlanckCODATA ^ 2`:

* `Asbpk = channelSubQuantum * l_P^2`, with `channelSubQuantum = Ω_b * geometricGap(4)^2`;
* `Lsbpk = √(Asbpk) = l_sub * l_P`, with `l_sub = √channelSubQuantum`;
* `Vsbpk = Lsbpk^3 = l_sub^3 * l_P^3`;
* `Tausbpk = Lsbpk / c`, with `c = 299792458` exact SI;
* `ThetaMarchaSbpk = channelSubQuantum * T_P` (documentary thermal anchor);
* `ySbpk = lsubCanal` is the Yukawa-type linear amplitude of the package.

The identities `Asbpk_eq_Lsbpk_sq` and `Vsbpk_eq_Lsbpk_cube` prove `A = L^2` and
`V = L^3`: that is what makes the package a geometry and not three loose numbers.

## Central result

`Lsbpk_lt_longitudPlanckCODATA` and its bundle `paquete_subplanckiano` prove that
the four magnitudes lie strictly below the corresponding Planck magnitude. The
bound imports no new hypothesis: it follows from `Gnomon.geometricGap_lt_deltaInf`
(path-graph geometry via Robertson) and from `Ω_b < 1` (sub-unit baryonic window,
`norm_num` on the documented constant).

The Yukawa-type reading is only structural: `ySbpk` is not a Standard Model
coupling but the effective amplitude whose square generates the dimensionless
weight of the channel. Below the limit there is no smaller causal record, but
absence of record of the channel.
-/

noncomputable section

namespace LimiteSubPlanckiano

/-! ## Canonical constants used -/

/-- Minimal geometric rupture defect: first open dimension `d = 4`. -/
noncomputable def deltaD4 : ℝ :=
  Gnomon.geometricGap 4

theorem deltaD4_pos : 0 < deltaD4 := by
  unfold deltaD4
  exact Gnomon.geometricGap_pos_of_four_le 4 (by norm_num)

/-- Baryonic fraction of the framework, `Ω_b = 0.049543679`.

In the canonical corpus this constant is derived as `g_s · e^{-η_inf}` with
`η_inf = 1 / C∞` and exported to cosmology as `pesoImagenReal`; its documented
value is `0.049543679` (√Ω_b = 0.2225841). The decimal is used here, and
`Omega_b_desde_pi` proves it is that formula of `π` rounded to 9 digits. -/
def Omega_b : ℝ :=
  (49543679 : ℝ) / 10 ^ 9

theorem Omega_b_pos : 0 < Omega_b := by
  norm_num [Omega_b]

theorem Omega_b_lt_uno : Omega_b < 1 := by
  norm_num [Omega_b]

/-- **`Ω_b` comes from `π`.** The decimal used is `g_s·e^{−1/C∞}` rounded to 9 digits
(`D26a`): the difference lies in `(1.11, 1.12)×10⁻¹⁰`, `< 2.3×10⁻⁹` relative. In
`Lsbpk` and `Tausbpk` (which go with `√Ω_b`) that is `≈ 1.1×10⁻⁹` relative, about 10⁴
times below the CODATA uncertainty of `l_P` (`1.1×10⁻⁵`): using the decimal or the
exact formula changes no significant figure. The only laboratory inputs of the layer
are `l_P` and `c`. -/
theorem Omega_b_desde_pi :
    111 * 10 ^ (-12 : ℤ) < Omega_b - OmegaDesdePi.omegaPi ∧
      Omega_b - OmegaDesdePi.omegaPi < 112 * 10 ^ (-12 : ℤ) :=
  OmegaDesdePi.decimal_desde_pi

/-- CODATA 2022 Planck length used as the SI anchor: `1.616255(18)e-35 m`.

It is the only inexact input of the package. `velocidadMaximaRegistrada` is exact
by SI definition, and `deltaD4` is internal to the framework (it depends only on
`π`). All the uncertainty of `Lsbpk`, `Asbpk`, `Vsbpk` and `Tausbpk` enters here. -/
def longitudPlanckCODATA : ℝ :=
  (1616255 : ℝ) / 10 ^ 41

/-- Lower end of the CODATA band `1.616255(18)e-35`: `1.616237e-35 m`. -/
def longitudPlanckCODATA_lo : ℝ :=
  (1616237 : ℝ) / 10 ^ 41

/-- Upper end of the CODATA band `1.616255(18)e-35`: `1.616273e-35 m`. -/
def longitudPlanckCODATA_hi : ℝ :=
  (1616273 : ℝ) / 10 ^ 41

theorem longitudPlanckCODATA_pos : 0 < longitudPlanckCODATA := by
  norm_num [longitudPlanckCODATA]

theorem longitudPlanckCODATA_nonneg : 0 ≤ longitudPlanckCODATA :=
  le_of_lt longitudPlanckCODATA_pos

/-- The anchor used lies strictly inside the band reported by CODATA. -/
theorem longitudPlanckCODATA_en_banda :
    longitudPlanckCODATA_lo < longitudPlanckCODATA ∧
      longitudPlanckCODATA < longitudPlanckCODATA_hi := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [longitudPlanckCODATA, longitudPlanckCODATA_lo,
      longitudPlanckCODATA_hi]

/-- Maximal registered speed in SI: the exact speed of light (laboratory input). -/
def velocidadMaximaRegistrada : ℝ :=
  299792458

theorem velocidadMaximaRegistrada_pos : 0 < velocidadMaximaRegistrada := by
  norm_num [velocidadMaximaRegistrada]

/-- CODATA Planck temperature used as a documentary thermal anchor:
`1.416784e32 K`. -/
def temperaturaPlanckCODATA : ℝ :=
  (1416784 : ℝ) * 10 ^ 26

theorem temperaturaPlanckCODATA_pos : 0 < temperaturaPlanckCODATA := by
  norm_num [temperaturaPlanckCODATA]

/-! ## Bounds on the dimensionless factor

Both pieces are already certified in the core (D8/D9) or by `norm_num`.
-/

/-- The Szegő defect at infinity is below `0.15`: from
`δ∞ = √(π²/3 − 2) − 1` and `π < 3.1416` follows `√(π²/3 − 2) < 1.15`. -/
theorem deltaInf_lt_quince : Gnomon.deltaInf < 0.15 := by
  have hpi2 : Real.pi ^ 2 < (9.9675 : ℝ) := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hsub : Real.pi ^ 2 / 3 - 2 < (1.15 : ℝ) ^ 2 := by
    norm_num
    linarith
  have hsqrt : Real.sqrt (Real.pi ^ 2 / 3 - 2) < (1.15 : ℝ) := by
    rw [Real.sqrt_lt (by nlinarith [Real.pi_gt_three]) (by norm_num)]
    exact hsub
  have h6 : (6 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  unfold Gnomon.deltaInf Gnomon.CoherenceConstantInf
  linarith

/-- The geometric defect at `d = 4` is bounded by the asymptotic Szegő defect,
which is itself below `0.15`. -/
theorem deltaD4_lt : deltaD4 < 0.15 := by
  have h1 : Gnomon.geometricGap 4 < Gnomon.deltaInf :=
    Gnomon.geometricGap_lt_deltaInf 4 (by norm_num)
  have h2 := deltaInf_lt_quince
  unfold deltaD4
  linarith

theorem deltaD4_lt_uno : deltaD4 < 1 := by
  have := deltaD4_lt
  linarith

/-- Powers of the defect stay below one at every order. -/
theorem deltaD4_pow_lt_uno (n : ℕ) (hn : n ≠ 0) : deltaD4 ^ n < 1 :=
  pow_lt_one₀ (le_of_lt deltaD4_pos) deltaD4_lt_uno hn

/-- The dimensionless channel factor is below one at any order. -/
theorem factorCanal_lt_uno (n : ℕ) (hn : n ≠ 0) :
    deltaD4 ^ n * Omega_b < 1 := by
  have h1 : deltaD4 ^ n < 1 := deltaD4_pow_lt_uno n hn
  have h2 : (0 : ℝ) ≤ deltaD4 ^ n := le_of_lt (pow_pos deltaD4_pos n)
  calc deltaD4 ^ n * Omega_b
      < 1 * 1 :=
        mul_lt_mul'' h1 Omega_b_lt_uno h2 (le_of_lt Omega_b_pos)
    _ = 1 := by norm_num

/-! ## The dimensionless seed of the channel

The whole chain hangs from a single unitless number. `channelSubQuantum` is the seed;
`lsubCanal` is its square root, the linear factor. Once both are fixed, every
magnitude is `lsubCanal ^ n` times the Planck unit of the corresponding
dimension: `l_P` for length, `l_P^2` for area, `l_P^3` for volume, `t_P` for time.
-/

/-- Dimensionless seed of the channel: `q_sub = Ω_b * geometricGap(4)^2`. It is the only
quantity that enters the chain before units are fixed. -/
noncomputable def channelSubQuantum : ℝ :=
  Omega_b * deltaD4 ^ 2

theorem channelSubQuantum_pos : 0 < channelSubQuantum :=
  mul_pos Omega_b_pos (pow_pos deltaD4_pos 2)

theorem channelSubQuantum_nonneg : 0 ≤ channelSubQuantum :=
  le_of_lt channelSubQuantum_pos

theorem channelSubQuantum_lt_uno : channelSubQuantum < 1 := by
  have h := factorCanal_lt_uno 2 two_ne_zero
  unfold channelSubQuantum
  linarith [h, mul_comm (deltaD4 ^ 2) Omega_b]

/-- Dimensionless linear factor: `l_sub = √q_sub = geometricGap(4) * √Ω_b`. -/
noncomputable def lsubCanal : ℝ :=
  Real.sqrt channelSubQuantum

theorem lsubCanal_pos : 0 < lsubCanal :=
  Real.sqrt_pos.mpr channelSubQuantum_pos

theorem lsubCanal_nonneg : 0 ≤ lsubCanal :=
  Real.sqrt_nonneg _

/-- The square of the linear factor returns the seed. -/
theorem lsubCanal_sq : lsubCanal ^ 2 = channelSubQuantum :=
  Real.sq_sqrt channelSubQuantum_nonneg

theorem lsubCanal_lt_uno : lsubCanal < 1 := by
  have h : Real.sqrt channelSubQuantum < Real.sqrt 1 :=
    Real.sqrt_lt_sqrt channelSubQuantum_nonneg (by simpa using channelSubQuantum_lt_uno)
  simpa [lsubCanal, Real.sqrt_one] using h

theorem lsubCanal_pow_lt_uno (n : ℕ) (hn : n ≠ 0) : lsubCanal ^ n < 1 :=
  pow_lt_one₀ lsubCanal_nonneg lsubCanal_lt_uno hn

/-! ## Yukawa-type effective amplitude

The analogy with Yukawa is one of quadratic form: the linear amplitude is not the
rate but the square root of the seed, which then appears squared in the area and
in the running temperature.
-/

/-- Yukawa-type effective amplitude of the sub-Planckian package. It is not a
Standard Model Yukawa: it names the linear root whose square generates the
dimensionless seed of the channel. -/
noncomputable def ySbpk : ℝ :=
  lsubCanal

theorem ySbpk_eq_lsubCanal : ySbpk = lsubCanal := rfl

theorem ySbpk_pos : 0 < ySbpk := by
  unfold ySbpk
  exact lsubCanal_pos

theorem ySbpk_nonneg : 0 ≤ ySbpk :=
  le_of_lt ySbpk_pos

/-- Yukawa-type squaring: the linear amplitude recovers the channel seed. -/
theorem ySbpk_sq : ySbpk ^ 2 = channelSubQuantum := by
  unfold ySbpk
  exact lsubCanal_sq

theorem ySbpk_lt_uno : ySbpk < 1 := by
  unfold ySbpk
  exact lsubCanal_lt_uno

/-! ## The four magnitudes

Each one is `lsubCanal ^ n` times the Planck unit of its dimension.
-/

/-- `Lsbpk = l_sub * l_P`: side of the minimal cell. -/
noncomputable def Lsbpk : ℝ :=
  lsubCanal * longitudPlanckCODATA

/-- `Asbpk = q_sub * l_P^2`: minimal area cell. -/
noncomputable def Asbpk : ℝ :=
  channelSubQuantum * longitudPlanckCODATA ^ 2

/-- `Vsbpk = l_sub^3 * l_P^3`: minimal volume. -/
noncomputable def Vsbpk : ℝ :=
  lsubCanal ^ 3 * longitudPlanckCODATA ^ 3

/-- `Tausbpk`: minimal registered time. `c` is the laboratory datum (exact SI) and
`Lsbpk` is linear: `τ_sbpk := L_sbpk / c_lab` is the time `c` takes to cross the cell.
It is defined, not derived; that it is the **minimum** over all dimensions is a
theorem (`CuantoDimensionalFisico.Tausbpk_le_tickDim`, in `PhysicalDimensionalQuantum`). -/
noncomputable def Tausbpk : ℝ :=
  Lsbpk / velocidadMaximaRegistrada

/-- Minimal running temperature at `d = 4`: the baryogenized quadratic seed,
anchored at the Planck temperature. It is not a laboratory cryogenic bound; it is
the first positive thermal threshold of the open channel. -/
noncomputable def ThetaMarchaSbpk : ℝ :=
  channelSubQuantum * temperaturaPlanckCODATA

theorem Lsbpk_pos : 0 < Lsbpk :=
  mul_pos lsubCanal_pos longitudPlanckCODATA_pos

theorem Lsbpk_nonneg : 0 ≤ Lsbpk :=
  le_of_lt Lsbpk_pos

theorem Asbpk_pos : 0 < Asbpk :=
  mul_pos channelSubQuantum_pos (pow_pos longitudPlanckCODATA_pos 2)

theorem Asbpk_nonneg : 0 ≤ Asbpk :=
  le_of_lt Asbpk_pos

theorem Vsbpk_pos : 0 < Vsbpk :=
  mul_pos (pow_pos lsubCanal_pos 3) (pow_pos longitudPlanckCODATA_pos 3)

theorem Tausbpk_pos : 0 < Tausbpk :=
  div_pos Lsbpk_pos velocidadMaximaRegistrada_pos

theorem ThetaMarchaSbpk_pos : 0 < ThetaMarchaSbpk :=
  mul_pos channelSubQuantum_pos temperaturaPlanckCODATA_pos

/-- The side is still the square root of the area: the earlier characterization is
kept as a theorem. -/
theorem Lsbpk_eq_sqrt_Asbpk : Lsbpk = Real.sqrt Asbpk := by
  unfold Lsbpk Asbpk lsubCanal
  rw [Real.sqrt_mul channelSubQuantum_nonneg,
    Real.sqrt_sq longitudPlanckCODATA_nonneg]

/-- The minimal registrable area lies below the Planck area. -/
theorem Asbpk_lt_areaPlanck : Asbpk < longitudPlanckCODATA ^ 2 := by
  have hP : (0 : ℝ) < longitudPlanckCODATA ^ 2 :=
    pow_pos longitudPlanckCODATA_pos 2
  calc Asbpk = channelSubQuantum * longitudPlanckCODATA ^ 2 := rfl
    _ < 1 * longitudPlanckCODATA ^ 2 :=
        mul_lt_mul_of_pos_right channelSubQuantum_lt_uno hP
    _ = longitudPlanckCODATA ^ 2 := one_mul _

/-! ## Coherence of the cell

These two identities are the reason for the convention. Without them the package
would not describe a cell: it would be a triple of numbers with units that tiles
nothing.
-/

/-- The area is the square of the side. -/
theorem Asbpk_eq_Lsbpk_sq : Asbpk = Lsbpk ^ 2 := by
  unfold Asbpk Lsbpk
  rw [mul_pow, lsubCanal_sq]

/-- The volume is the cube of the side. -/
theorem Vsbpk_eq_Lsbpk_cube : Vsbpk = Lsbpk ^ 3 := by
  unfold Vsbpk Lsbpk
  rw [mul_pow]

/-! ## The scale is strictly sub-Planckian

The four bounds follow from the same fact: `lsubCanal < 1`, hence so is every power
of it. No order-of-magnitude argument is needed.
-/

/-- **Central theorem: the side of the minimal cell lies strictly below the Planck
length.** -/
theorem Lsbpk_lt_longitudPlanckCODATA : Lsbpk < longitudPlanckCODATA := by
  calc Lsbpk = lsubCanal * longitudPlanckCODATA := rfl
    _ < 1 * longitudPlanckCODATA :=
        mul_lt_mul_of_pos_right lsubCanal_lt_uno longitudPlanckCODATA_pos
    _ = longitudPlanckCODATA := one_mul _

/-- The minimal volume lies below the Planck volume. -/
theorem Vsbpk_lt_volumenPlanck : Vsbpk < longitudPlanckCODATA ^ 3 := by
  have hP : (0 : ℝ) < longitudPlanckCODATA ^ 3 :=
    pow_pos longitudPlanckCODATA_pos 3
  calc Vsbpk = lsubCanal ^ 3 * longitudPlanckCODATA ^ 3 := rfl
    _ < 1 * longitudPlanckCODATA ^ 3 :=
        mul_lt_mul_of_pos_right (lsubCanal_pow_lt_uno 3 three_ne_zero) hP
    _ = longitudPlanckCODATA ^ 3 := one_mul _

/-- Planck time derived from the same anchor: `l_P / c`. Numerically
`5.391247e-44 s`, the CODATA 2022 value `5.391247(60)e-44 s`. -/
noncomputable def tiempoPlanckCODATA : ℝ :=
  longitudPlanckCODATA / velocidadMaximaRegistrada

theorem tiempoPlanckCODATA_pos : 0 < tiempoPlanckCODATA :=
  div_pos longitudPlanckCODATA_pos velocidadMaximaRegistrada_pos

/-- The minimal time is the same linear factor applied to the Planck time. The two
routes — dividing the length by `c`, or scaling `t_P` by `lsubCanal` — agree. -/
theorem Tausbpk_eq_lsub_tiempoPlanck :
    Tausbpk = lsubCanal * tiempoPlanckCODATA := by
  unfold Tausbpk tiempoPlanckCODATA Lsbpk
  ring

/-- The minimal registrable interval lies below the Planck time. -/
theorem Tausbpk_lt_tiempoPlanckCODATA : Tausbpk < tiempoPlanckCODATA := by
  unfold Tausbpk tiempoPlanckCODATA
  exact div_lt_div_of_pos_right Lsbpk_lt_longitudPlanckCODATA
    velocidadMaximaRegistrada_pos

/-- The running temperature lies below the Planck temperature by the same quadratic
factor `channelSubQuantum`. -/
theorem ThetaMarchaSbpk_lt_temperaturaPlanckCODATA :
    ThetaMarchaSbpk < temperaturaPlanckCODATA := by
  calc ThetaMarchaSbpk = channelSubQuantum * temperaturaPlanckCODATA := rfl
    _ < 1 * temperaturaPlanckCODATA :=
        mul_lt_mul_of_pos_right channelSubQuantum_lt_uno temperaturaPlanckCODATA_pos
    _ = temperaturaPlanckCODATA := one_mul _

theorem ThetaMarchaSbpk_ratio :
    ThetaMarchaSbpk = channelSubQuantum * temperaturaPlanckCODATA := rfl

/-- Package of powers generated by the Yukawa-type effective amplitude. -/
theorem paquete_potencias_ySbpk :
    Lsbpk = ySbpk * longitudPlanckCODATA ∧
      Asbpk = ySbpk ^ 2 * longitudPlanckCODATA ^ 2 ∧
        Vsbpk = ySbpk ^ 3 * longitudPlanckCODATA ^ 3 ∧
          Tausbpk = ySbpk * tiempoPlanckCODATA ∧
            ThetaMarchaSbpk = ySbpk ^ 2 * temperaturaPlanckCODATA := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Lsbpk ySbpk
    rfl
  · calc
      Asbpk = channelSubQuantum * longitudPlanckCODATA ^ 2 := rfl
      _ = ySbpk ^ 2 * longitudPlanckCODATA ^ 2 := by rw [ySbpk_sq]
  · unfold Vsbpk ySbpk
    rfl
  · rw [Tausbpk_eq_lsub_tiempoPlanck]
    unfold ySbpk
    rfl
  · calc
      ThetaMarchaSbpk = channelSubQuantum * temperaturaPlanckCODATA := rfl
      _ = ySbpk ^ 2 * temperaturaPlanckCODATA := by rw [ySbpk_sq]

/-- Compact form: the whole package is sub-Planckian in all four magnitudes. -/
theorem paquete_subplanckiano :
    Lsbpk < longitudPlanckCODATA ∧
      Asbpk < longitudPlanckCODATA ^ 2 ∧
        Vsbpk < longitudPlanckCODATA ^ 3 ∧
          Tausbpk < tiempoPlanckCODATA :=
  ⟨Lsbpk_lt_longitudPlanckCODATA, Asbpk_lt_areaPlanck,
    Vsbpk_lt_volumenPlanck, Tausbpk_lt_tiempoPlanckCODATA⟩

/-- Compact form of coherence: a single cell generates the three spatial
magnitudes. -/
theorem celda_coherente :
    Asbpk = Lsbpk ^ 2 ∧ Vsbpk = Lsbpk ^ 3 :=
  ⟨Asbpk_eq_Lsbpk_sq, Vsbpk_eq_Lsbpk_cube⟩

/-! ## Registrability lock -/

/-- A registered linear value must be at or above `Lsbpk`. -/
def ValorLinealRegistrable (x : ℝ) : Prop :=
  Lsbpk ≤ x

/-- A registered time interval must be at or above `Tausbpk`. -/
def TiempoRegistrable (tau : ℝ) : Prop :=
  Tausbpk ≤ tau

theorem valor_bajo_Lsbpk_no_es_registrable {x : ℝ}
    (hx : x < Lsbpk) : ¬ ValorLinealRegistrable x := by
  intro hreg
  unfold ValorLinealRegistrable at hreg
  linarith

theorem tiempo_bajo_Tausbpk_no_es_registrable {tau : ℝ}
    (htau : tau < Tausbpk) : ¬ TiempoRegistrable tau := by
  intro hreg
  unfold TiempoRegistrable at hreg
  linarith

/-- Compact form: the first registered causal order is strictly positive. -/
theorem orden_causal_subplanckiano_positivo :
    0 < Lsbpk ∧ 0 < Asbpk ∧ 0 < Vsbpk ∧ 0 < Tausbpk :=
  ⟨Lsbpk_pos, Asbpk_pos, Vsbpk_pos, Tausbpk_pos⟩

/-!
## SI values at the precision supported by CODATA

The whole chain hangs from the dimensionless seed and its root:

```text
channelSubQuantum = Ω_b * geometricGap(4)^2 = 3.56148882979e-6
ySbpk = lsubCanal = sqrt channelSubQuantum   = 1.88719072427e-3

Lsbpk   = ySbpk     * l_P    = 3.050181e-38  m
Asbpk   = ySbpk ^ 2 * l_P^2  = 9.303607e-76  m^2      (= channelSubQuantum * l_P^2)
Vsbpk   = ySbpk ^ 3 * l_P^3  = 2.837769e-113 m^3
Tausbpk = ySbpk     * t_P    = 1.017431e-46  s        (= Lsbpk / c)
ThetaMarchaSbpk = ySbpk ^ 2 * T_P = 5.045860e26 K
```

The figures use the documented decimal `Ω_b = 0.049543679`, which is the one Lean
uses (with the exact `g_s·e^{−1/C∞}` they differ from the ninth digit on; see
`D26a`/`D26b`). The ratios to the Planck magnitude are dimensionless and exact
inside the framework (`l_P` cancels):

* `Lsbpk / longitudPlanckCODATA = ySbpk = lsubCanal = 1/529.8881492`
* `Asbpk / longitudPlanckCODATA ^ 2 = channelSubQuantum = 1/280781.4506`
* `Vsbpk / longitudPlanckCODATA ^ 3 = lsubCanal ^ 3 = 1/148782763.2`
* `Tausbpk / tiempoPlanckCODATA = ySbpk = lsubCanal = 1/529.8881492`
* `ThetaMarchaSbpk / temperaturaPlanckCODATA = ySbpk ^ 2 = channelSubQuantum`

CODATA 2022 reports `l_P = 1.616255(18)e-35 m`, i.e. `u_r = 1.1137e-5`. That
uncertainty propagates with the power of `l_P` in each magnitude, so only these
figures are significant:

* `Lsbpk   = 3.050181(34)e-38 m`      `u_r = 1.11e-5`
* `Asbpk   = 9.30361(21)e-76 m^2`     `u_r = 2.23e-5`
* `Vsbpk   = 2.837769(95)e-113 m^3`   `u_r = 3.34e-5`
* `Tausbpk = 1.017431(11)e-46 s`      `u_r = 1.11e-5`
* `ThetaMarchaSbpk = 5.045860e26 K`   (documentary thermal anchor)
-/

end LimiteSubPlanckiano

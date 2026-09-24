import NavaRobertsonIndependent.Mathematics
import NavaRobertsonIndependent.Physics.SubPlanckianLimit
import NavaRobertsonIndependent.Physics.SchwarzschildCollapse
import NavaRobertsonIndependent.Physics.TimeEnergyRegistrationClosure
import NavaRobertsonIndependent.Physics.MaximumSpeed
import NavaRobertsonIndependent.Physics.ArrowOfTime
import NavaRobertsonIndependent.Physics.ElementalCellStep
import NavaRobertsonIndependent.Physics.PhysicalDimensionalQuantum
import NavaRobertsonIndependent.Physics.DimensionalMassGap
import NavaRobertsonIndependent.Physics.HawkingTemperature
import NavaRobertsonIndependent.Physics.MoreCellsMoreTime
import NavaRobertsonIndependent.Physics.D32_WhyTimeGrows
import NavaRobertsonIndependent.Physics.PhysicalSupportR4
import NavaRobertsonIndependent.Physics.SuperluminalUnregistrable
import NavaRobertsonIndependent.Physics.CantorCompatibility

/-!
# Layer 2 — Physics: registration floors and dimensional quanta

This layer reads Layer 1 in SI units, anchored in the SI/CODATA constants. Everything here is a
theorem in Lean; the theorems are conditional on the inputs below, and the physical
reading of their conclusions is an interpretation. Layer 1 does not depend on this
layer.

## Frame

The spectral network (`pathGraph d`, `T_d:P_d`, `H₂, H₃, H₄, …`) is space itself: the
finest structure the algebra allows. `T_d:P_d` is the universal elementary step (`D22`),
so Robertson–Schrödinger speaks about this space in every quantum system above absolute
zero. Its graph in every dimension is the graph of Robertson's bound, an algebraic
obstruction of space itself. `d` is the Hilbert dimension, and the quantum is dimensional: each `H_d`
has its own `δ(d)` (`D25`). Physics reads that quantum in units.

## Anchors and stated hypotheses

* Laboratory anchors: the Planck length `l_P` (CODATA 2022, the only inexact input),
  and the exact SI values of `c`, `h` and `k_B`. `c` is an **input**: the minimal time
  is `τ_sbpk := L_sbpk / c_lab`, what `c` takes to cross the cell.
* `Ω_b = 0.049543679`, **proved** to be `g_s·e^{−1/C∞}` (a function of `π` only)
  rounded to 9 digits (`Omega_b_desde_pi`, from `D26a`). The rounding changes no
  significant figure: it is ~10⁴ times below the CODATA uncertainty of `l_P`.
* H1, the spectral ceiling `ΔH ≤ E_P/(2y)` (`DispersionAdmisible`). Because
  `energiaMandelstamTamm` is defined from `Tausbpk`, H1 restates the temporal floor
  as a bound on the spectrum.
* For the gravitational identities: `G > 0` and `RelacionPlanckNewton`, as hypotheses
  of those theorems only; satisfiable (`relacionPlanckNewton_satisfacible`, the `G` it
  forces is the CODATA value).
* The calibration of the elementary step: `longitudPaso d = √Ω_b · l_P · δ(d)`.
* For the curvature theorem: `HCurvaturaConteo` (curvature adds cells), declared and
  used.
* For the Hawking temperature: the area law (`entropiaBH`) and the first law with
  `E = Mc²` (`temperaturaPrimeraLey`), declared as definitions.

## Blocks

**2.1 Registration floors.** `LimiteSubPlanckiano` (cell `Lsbpk`, tick `Tausbpk`,
all four magnitudes sub-Planckian), `ColapsoSchwarzschild`, `CierreRegistroTiempoEnergia`
(energy scales, Mandelstam–Tamm floor, Hubble patch), `VelocidadMaxima` (every
admissible process: `k` steps cost at least `k` ticks, `v ≤ c`), `PasoElementalCelda`.

**2.2 Dimensional quanta.** `CuantoDimensionalFisico`: the step and the tick of `H_d`
(`tickDim d = longitudPaso d / c`); `τ_sbpk` is the minimum over every open dimension
(`Tausbpk_le_tickDim`); the traversal of `H_d` (`d − 1` edges) goes exactly at `c` in
every dimension. `SaltoMasaDimensional`: the Robertson gap `δ(d)` in mass units, with
floor at `H_4`, ceiling at `δ_∞` and a positive limit. `TemperaturaHawking`: from the
area law and the first law, `T = ħc³/(8πGk_B M)` (`temperaturaPrimeraLey_eq_hawking`);
`T > 0` for every finite mass and `T → 0` only as `M → ∞` (third law); since the
horizon is at least `L_sbpk`, `T ≤ T(sbpkMassGap) = T_P/(4π y)`
(`temperaturaHawking_le_celda`, `temperaturaHawking_celda`), which exceeds `T_P`
(`celda_supera_Planck`).

**2.3 Time and curvature.** The cell does not curve; curvature adds cells, and cells
are the measure of time. `MasCeldasMasTiempo`: `k` cells of `L_sbpk` — more cells,
longer and slower, same `c`. `D32_PorQueCreceElTiempo`: under `HCurvaturaConteo`,
every admissible process along the curve takes strictly longer than the straight
one (`curva_tarda_mas`), and the time ratio is exactly `k₁/k₀`. `ArrowOfTime`: the
tick is the defect of `H₄` (`tick_es_defect`), every step costs at least one tick, so
registered time is strictly increasing in the number of steps (`flecha`), never
returns (`no_retorno`), and going back in space adds time (`ida_y_vuelta`).

**2.4 Physical support.** `SoporteFisicoR4`: Cantor's ℝ is proved mathematics but is
not imported whole into physics. The support is a bounded, discrete, finite subset of
`ℝ⁴` (Hilbert and Banach alike); its theorems restrict to it, but the continuum does
not: every convergent sequence in the support is eventually constant, registered
times are countable (not the continuum), none lies in `(0, τ_sbpk)`, and an eon of
`N` ticks has exactly `N+1` of them. `SuperluminalNoRegistrable`: above `c` the cell
crossing time `L_sbpk / v` exists in ℝ (at `n·c` it is `τ_sbpk / n`, and it tends to
`0` as `v → ∞`), but it lies in `(0, τ_sbpk)`: it is no registered time and no
admissible step (`superluminal_en_R_no_en_fisica`, `superluminal_no_es_paso`).
`CompatibilidadCantor`: Cantor (ℝ uncountable), the countable registered times and
the arithmetic and order of ℝ hold together; inside the bounds ℝ is exactly ℝ
(`cantor_y_fisica_compatibles`).

## What this layer does not contain

Cosmology (Layer 3), ontology (Layer 4) and the annex (`Superseded`, superseded modules).
None is imported here; `Verification/Layer2_Physics.lean` checks it.
-/

# Experimental test of NRS in a photonic waveguide array

This note turns the theorems of the package into a concrete experiment. The mathematics is proved
in Lean; the experiment tests the declared physical bridge, namely that a physical system realizes
the pair `(T_N, P_N)`.

## 1. System

An array of `N` identical single-mode waveguides written in glass (for example by femtosecond-laser
writing), equally spaced so that each guide couples only to its nearest neighbours with the same
coupling constant `κ`. In the paraxial regime the field amplitudes `ψ_j(z)` obey

    i dψ/dz = κ A_N ψ,

with `A_N` the adjacency matrix of the path on `N` sites. The propagation length `z` plays the role
of time (`t = κ z`), and `T_N = A_N / ρ_N`, `ρ_N = 2 cos(π/(N+1))`. Position is the guide index,
relabelled to `P_N = diag(−1, …, 1)`.

**Wavelength.** Any wavelength with low loss in the glass. Standard choices are 633 nm (He–Ne) and
1550 nm (telecom C-band). Inside the glass light travels at `c/n`, about two thirds of `c`; this does
not enter the prediction, which depends only on the coupling pattern.

## 2. State

The maximal-tension state `ψ*` (`D5`, `D21`):

    ψ*_j ∝ (−i)^j sin((j+1)π/(N+1)),   j = 0, …, N−1.

It is prepared at the input with a spatial light modulator (amplitudes and phases per guide).
Its phase advances by `−90°` per guide: it is the beam launched at the angle of maximal transverse
group velocity. The **reference state** has the same amplitudes and all phases equal (`⟨K⟩ = 0`).

## 3. Measurement

The complex field `ψ_j` at the input plane is measured by off-axis digital holography (or by
interferometric phase retrieval between neighbouring guides). From it:

    σ_P² = ⟨P²⟩ − ⟨P⟩²,   σ_T² = ⟨T²⟩ − ⟨T⟩²,   ½|⟨[T, P]⟩|,

and the ratio

    R = σ_T σ_P / (½ |⟨[T, P]⟩|).

## 4. Predictions

| `N` | `R = C_Nava(N)` | excess | NRS angle |
|---|---|---|---|
| 2 | 1 | 0 (control) | 0° |
| 3 | 1 | 0 (control) | 0° |
| 4 | 1.008479 | 0.85 % | 7.43° |
| 5 | 1.018350 | 1.84 % | 10.89° |
| 6 | 1.027727 | 2.77 % | 13.34° |
| 8 | 1.043563 | 4.36 % | 16.61° |
| 10 | 1.055806 | 5.58 % | 18.71° |
| limit | 1.135724 | 13.57 % (never reached) | 28.30° |

What confirms the bridge: `R = 1` within error at `N = 2, 3`; `R > 1` from `N = 4`; `R` growing
with `N` along the table. What refutes it: a correctly built array with `R` outside the table
beyond the error bars.

**Further predictions on the same chip.**

* Light injected into a single guide spreads inside the cone `|i − j| ≲ κz`; outside it the
  amplitude falls as `(κz)^r / r!` (`D37f`, `D37g`, physlib `norm_inner_unitaryEvolution_le`).
  The intensity along `z` can be imaged by fluorescence microscopy of the waveguides.
* At `N = 4`, states that saturate Robertson–Schrödinger carry tension at most `1/φ ≈ 0.618`,
  against a maximum of `2/3` (`D23f`, `D23g`).

## 5. Error budget

Imperfections add uncertainty, so they **bias `R` upwards** and can imitate the excess. Simulation
of the prepared `ψ*` (2000 random samples per entry, mean ± standard deviation):

| `N` | ideal `R` | coupling disorder 1 % | 3 % | 5 % | phase error 2° | 5° | 10° |
|---|---|---|---|---|---|---|---|
| 2 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | 1.0000 |
| 3 | 1.0000 | 1.0001 ± 0.0001 | 1.0005 ± 0.0007 | 1.0012 ± 0.0017 | 1.0009 ± 0.0013 | 1.0060 ± 0.0088 | 1.024 ± 0.038 |
| 4 | 1.0085 | 1.0086 ± 0.0015 | 1.0092 ± 0.0043 | 1.0107 ± 0.0077 | 1.0099 ± 0.0015 | 1.018 ± 0.010 | 1.049 ± 0.044 |
| 6 | 1.0277 | 1.0279 ± 0.0019 | 1.0294 ± 0.0056 | 1.0319 ± 0.0096 | 1.0304 ± 0.0021 | 1.044 ± 0.013 | 1.093 ± 0.053 |
| 10 | 1.0558 | 1.0562 ± 0.0018 | 1.0595 ± 0.0058 | 1.0656 ± 0.0109 | 1.0614 ± 0.0034 | 1.089 ± 0.020 | 1.189 ± 0.078 |

Consequences for the design:

1. **Controls are essential.** `N = 3` is the sharpest control: with phase errors above a few
   degrees it already shows a spurious excess.
2. **Tolerances.** Input phases within about 2° and coupling uniformity within about 1–3 %.
3. **Calibrated prediction.** Measure the fabricated couplings and compute the predicted `R` for
   that array, not only for the ideal one; compare the measured `R` with the calibrated value.
4. **Use the curve, not one point.** The excess at `N = 4` (0.85 %) is small; measuring
   `N = 2, …, 10` on the same chip tests both the vanishing at the seeds and the growth.

## 6. Units: from the algebra to the laboratory

The theorems carry no unit: sites, steps and `R` are pure numbers. Units enter in one place.

**The cone fixes the speed.** `T_N` only connects neighbours, so after `k` steps an amplitude
has moved at most `k` sites, and the edge is reached (`D37f`: `cono_de_luz`, `borde_del_cono`).
The slope of the cone is exactly one site per step. In continuous time, `U(t) = exp(−i t T_N)`,
the edge is no longer sharp, but outside the cone the amplitude falls as `|t|^r / r! · e^{|t|}`
with `r` the distance (`D37g`, `lieb_robinson`): the front still advances one site per unit of
`t`, and what lies beyond it is a tail that vanishes faster than any exponential.

**The laboratory gives that slope a number.** The slope of the cone is identified with the
measured limiting speed of the platform:

| Platform | site | step | slope of the cone |
|---|---|---|---|
| motion in space | cell of length `L` | tick of duration `τ` | `L / τ = c` |
| waveguide array | one guide | propagation length `z` | set by the coupling `κ` (per mm) |

In the array, `i dψ/dz = κ A_N ψ = κ ρ_N T_N ψ`, so `t = κ ρ_N z`: light launched into a single
guide spreads inside a cone whose edge advances about `κ ρ_N` guides per unit length. Imaging
that cone measures `κ`.

**One scale is left.** Fixing the slope ties length to time; one scale remains, the size of a
cell (or of a step), and one more measurement of the platform sets it. The choice `L = l_P`,
`τ = t_P` is consistent: the ratio is `c`, and nothing falls below the Planck scale, because
the step is the floor of registrable duration and is not derived from a mass. (A
non-relativistic discretization with hopping `ħ²/(2ma²)` and `a = l_P` would give steps shorter
than `t_P`; that is a different model, not this one.)

**Ratios need nothing.** `R = C_Nava(N)`, the NRS angle and the excess are quotients of
quantities with the same units: any scale multiplies numerator and denominator alike. They are
compared with the measurement as they are, with no calibration. This is what makes the
prediction of §4 the same number on every platform.

## 7. Other platforms

* **Single photons in the same array** give the quantum version with identical mathematics.
* **Superconducting qubit chains** with uniform nearest-neighbour exchange, in the
  single-excitation sector (quantum state transfer), realize `T_N`; populations give `P_N`.
* **A single `N`-level system** (for `N = 4`, a ququart) driven only between consecutive levels.

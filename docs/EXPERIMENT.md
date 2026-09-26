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

and the Robertson–Schrödinger ratio

    R = σ_T σ_P / |⟨x, y⟩|,   x = (T − ⟨T⟩)ψ,   y = (P − ⟨P⟩)ψ,

where `|⟨x, y⟩|² = cov(T, P)² + (½ ⟨i[T, P]⟩)²`: the floor includes the covariance. This is
`ratioG` of `D39`. At the ideal `ψ*` the covariance vanishes and `R` equals the Robertson ratio
`σ_T σ_P / (½ |⟨[T, P]⟩|)`; with imperfections it does not, and only the Robertson–Schrödinger
ratio keeps the controls at `1` (section 5).

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

Imperfections add uncertainty and bias `R` upwards, which can imitate the excess. Monte Carlo
of 2000 realizations per entry (mean ± standard deviation), reproduced by
[`simulation/error_budget.py`](simulation/error_budget.py) (numpy only). Sources: disorder of
the fabricated couplings, phase and amplitude errors of the SLM, additive noise of the
holographic reconstruction at the given SNR, and finite photon counts (Poisson intensities,
phase jitter `0.5/√n`). *Realistic*: 1 % coupling, 2°, 2 % amplitude, 35 dB, 5 × 10⁴ photons.
*Stressed*: 3 %, 5°, 5 %, 25 dB, 10⁴ photons.

Robertson–Schrödinger ratio (the observable of section 3):

| `N` | ideal | coupling 1 % | coupling 3 % | phase 2° | phase 5° | amplitude 2 % | holography 30 dB | 10⁴ photons | realistic | stressed |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 1.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 |
| 3 | 1.0000 | 1.0000 ± 0.0001 | 1.0005 ± 0.0006 | 1.0000 ± 0.0000 | 1.0000 ± 0.0001 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0001 ± 0.0001 | 1.0006 ± 0.0008 |
| 4 | 1.0085 | 1.0086 ± 0.0014 | 1.0092 ± 0.0042 | 1.0093 ± 0.0012 | 1.0131 ± 0.0075 | 1.0087 ± 0.0005 | 1.0090 ± 0.0006 | 1.0086 ± 0.0002 | 1.0098 ± 0.0021 | 1.0174 ± 0.0105 |
| 5 | 1.0184 | 1.0184 ± 0.0017 | 1.0193 ± 0.0052 | 1.0198 ± 0.0015 | 1.0268 ± 0.0094 | 1.0188 ± 0.0044 | 1.0193 ± 0.0040 | 1.0187 ± 0.0020 | 1.0207 ± 0.0054 | 1.0352 ± 0.0190 |
| 6 | 1.0277 | 1.0278 ± 0.0018 | 1.0293 ± 0.0055 | 1.0298 ± 0.0019 | 1.0408 ± 0.0118 | 1.0285 ± 0.0055 | 1.0294 ± 0.0056 | 1.0282 ± 0.0031 | 1.0311 ± 0.0071 | 1.0531 ± 0.0240 |
| 8 | 1.0436 | 1.0439 ± 0.0019 | 1.0461 ± 0.0059 | 1.0470 ± 0.0025 | 1.0649 ± 0.0155 | 1.0448 ± 0.0062 | 1.0462 ± 0.0075 | 1.0447 ± 0.0047 | 1.0496 ± 0.0084 | 1.0843 ± 0.0298 |
| 10 | 1.0558 | 1.0562 ± 0.0018 | 1.0594 ± 0.0058 | 1.0608 ± 0.0032 | 1.0868 ± 0.0193 | 1.0574 ± 0.0062 | 1.0602 ± 0.0084 | 1.0580 ± 0.0059 | 1.0650 ± 0.0094 | 1.1155 ± 0.0347 |

For comparison, the Robertson ratio `σ_T σ_P / (½ |⟨[T, P]⟩|)` under the same noise:

| `N` | ideal | coupling 1 % | coupling 3 % | phase 2° | phase 5° | amplitude 2 % | holography 30 dB | 10⁴ photons | realistic | stressed |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 1.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0000 ± 0.0000 | 1.0001 ± 0.0002 |
| 3 | 1.0000 | 1.0000 ± 0.0001 | 1.0005 ± 0.0006 | 1.0009 ± 0.0013 | 1.0057 ± 0.0081 | 1.0000 ± 0.0000 | 1.0004 ± 0.0005 | 1.0001 ± 0.0001 | 1.0011 ± 0.0015 | 1.0075 ± 0.0098 |
| 4 | 1.0085 | 1.0086 ± 0.0014 | 1.0092 ± 0.0042 | 1.0100 ± 0.0015 | 1.0179 ± 0.0095 | 1.0087 ± 0.0005 | 1.0094 ± 0.0008 | 1.0087 ± 0.0002 | 1.0107 ± 0.0024 | 1.0235 ± 0.0135 |
| 5 | 1.0184 | 1.0184 ± 0.0017 | 1.0193 ± 0.0052 | 1.0204 ± 0.0017 | 1.0305 ± 0.0109 | 1.0188 ± 0.0044 | 1.0197 ± 0.0040 | 1.0188 ± 0.0020 | 1.0215 ± 0.0056 | 1.0407 ± 0.0208 |
| 6 | 1.0277 | 1.0278 ± 0.0018 | 1.0293 ± 0.0055 | 1.0303 ± 0.0021 | 1.0442 ± 0.0127 | 1.0285 ± 0.0055 | 1.0298 ± 0.0057 | 1.0283 ± 0.0031 | 1.0318 ± 0.0071 | 1.0576 ± 0.0248 |
| 8 | 1.0436 | 1.0439 ± 0.0019 | 1.0461 ± 0.0059 | 1.0474 ± 0.0026 | 1.0675 ± 0.0160 | 1.0448 ± 0.0062 | 1.0465 ± 0.0076 | 1.0448 ± 0.0047 | 1.0502 ± 0.0084 | 1.0882 ± 0.0304 |
| 10 | 1.0558 | 1.0562 ± 0.0018 | 1.0594 ± 0.0058 | 1.0612 ± 0.0033 | 1.0891 ± 0.0199 | 1.0574 ± 0.0062 | 1.0605 ± 0.0084 | 1.0582 ± 0.0059 | 1.0655 ± 0.0094 | 1.1189 ± 0.0352 |

Consequences for the design:

1. **Use the Robertson–Schrödinger ratio.** Phase and holographic errors create a spurious
   covariance. The Robertson ratio counts it as excess (at `N = 3` with 5° of phase error it
   reads `1.0057`); the Robertson–Schrödinger ratio does not (`1.0000`). The controls stay at
   `1` and `N = 3` against `N = 4` separates by more than four standard deviations in the
   realistic scenario.
2. **Controls are essential.** `N = 2, 3` must give `R = 1` within error; they test the
   instrument, not only the theory.
3. **Tolerances.** Coupling uniformity within about 1 % (coupling disorder is the one source
   that also moves the controls), input phases within about 2°.
4. **Calibrated prediction.** Measure the fabricated couplings and compute the predicted `R` for
   that array; compare the measured `R` with the calibrated value.
5. **Use the curve, not one point.** The excess at `N = 4` (0.85 %) is small; measuring
   `N = 2, …, 10` on the same chip tests both the vanishing at the seeds and the growth.

## 6. Units: from the algebra to the laboratory

The theorems carry no unit: sites, steps and `R` are pure numbers. Units enter in one place.

**The cone fixes the speed.** `T_N` only connects neighbours, so after `k` steps an amplitude
has moved at most `k` sites, and the edge is reached (`D37f`: `lightCone`, `lightCone_edge`).
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

A waveguide array is a lattice in the two transverse directions; the propagation direction plays
the role of time. It realizes one axis, or two, of NRS³, not the cube `d × d × d`, which needs a
three-dimensional platform (for example atoms in a cubic optical lattice).

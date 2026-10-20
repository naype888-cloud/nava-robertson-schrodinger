# NRS³·T³ — Nava–Robertson–Schrödinger uncertainty on the three-torus

**[▶ Try it: the three-torus `T³`, computed in the browser from Lean's matrices](https://naype888-cloud.github.io/nava-robertson-schrodinger/)** ·
[open-box explorer (previous page)](https://naype888-cloud.github.io/nava-robertson-schrodinger/box.html)

Independent Lean 4 verification prepared by Eduardo Nava Hernández. This repository has two
pillars.

## Pillar 1 — what Physlib has merged

The results that passed review in [Physlib](https://github.com/leanprover-community/physlib), the
Lean physics library of the community, are the main result:
[![merged](https://img.shields.io/github/issues-search?query=repo%3Aleanprover-community%2Fphyslib%20is%3Apr%20is%3Amerged%20author%3Anaype888-cloud&label=merged&color=blue)](https://github.com/leanprover-community/physlib/pulls?q=is%3Apr+is%3Amerged+author%3Anaype888-cloud)
[![in review](https://img.shields.io/github/issues-search?query=repo%3Aleanprover-community%2Fphyslib%20is%3Apr%20is%3Aopen%20author%3Anaype888-cloud&label=in%20review&color=lightgrey)](https://github.com/leanprover-community/physlib/pulls?q=is%3Apr+is%3Aopen+author%3Anaype888-cloud)
— the list of [merged pull requests](https://github.com/leanprover-community/physlib/pulls?q=is%3Apr+is%3Amerged+author%3Anaype888-cloud)
is the reference; the port notes are in [`docs/PHYSLIB_PORT.md`](docs/PHYSLIB_PORT.md).

## Pillar 2 — NRS³ on `T³`

`T³ = x × y × z`, each axis closed with three positions: finite and without boundary. Each axis
carries the pair `(T°, P₃)` of the closed axis. This is the framework that fits the observational
reading best, and the results below are stated on it.

| Statement | Lean ([`nrs3-tritoro`](https://github.com/naype888-cloud/nrs3-tritoro)) |
|---|---|
| Robertson 1934 on the torus, every state | `Torus.robertson_det_torus` |
| NRS³ on each axis: tension > 1 ⇒ defect > 0, every state, entangled or not | `Torus.gramDefect_pos` |
| at the maximal-current state `det Σ = (5/4)^k · \|det Ω\|`; `T³`: `125/64` | `Torus.det_covMatrix_maxState`, `Torus.three_torus` |
| **det\|NRS³\| is strict on `T³` for every state with the three axes in their band** | `TorusStrict.robertson_det_torus_lt` |
| distinct axes commute | `TorusCommute.torusPairs_comm` |
| every axis of every state lies in the closed future cone; in the band it is timelike, proper time > 0 | `TorusCone.axisVector_mem_futureCone`, `TorusCone.properTime_pos_of_band` |
| light + dark = 1 on each axis; in the band each axis keeps a dark part > 0 | `TorusDark.lightShare_add_darkShare`, `TorusDark.darkShare_pos_of_band` |
| at `c` each axis resolves `4/5` and keeps `1/5` dark (the open cube of 3 keeps `0`) | `TorusDark.lightShare_maxState`, `TorusDark.darkShare_maxState` |
| area law: `S = 2·dy·dz·log 2` on a cut | `TorusArea` |
| Mandelstam–Tamm on the ring and on `T³` | `TorusTime`, `TorusSharp` |
| field level, one and `n` excitations; the cut sees `2·dy·dz` steps per excitation | `TorusField`, `TorusFock.uncertainty_nExcitation`, `TorusFockCut.card_bracketNSteps` |
| **Szegő limit of the closed axis**: light and dark → `1/2`, angle → `45°`, `det Σ / \|det Ω\|` → `2` | `RingSzego.tendsto_angle`, `RingSzego.tendsto_det_ratio` |

The measured baryon fraction `Ω_b` is a datum, like `c`; the dark share is read against it
(`BaryonWindow`). All statements are theorems over Mathlib; the physical reading is a declared
bridge, stated and not proved.

*The Lean:* [`nrs3-tritoro`](https://github.com/naype888-cloud/nrs3-tritoro) (standard axioms only), built on
[`nrs3-hopf`](https://github.com/naype888-cloud/nrs3-hopf). Pages on `T³`:
[de Sitter](https://naype888-cloud.github.io/nrs3-de-sitter/t3.html) ·
[SL(2, ℂ) and the cone](https://naype888-cloud.github.io/nrs3-uncertainty-cone/lorentz-t3.html).

## The open cube, kept separate

NRS, NRS³ and det|NRS³| on the *open* cube (`D0`–`D49t`), with the Lean modules in this
repository and the Physlib port of that chain, are unchanged in
**[`NRS_OPEN_CUBE.md`](NRS_OPEN_CUBE.md)**. They are the case before closing the axes; the torus is
what the observational reading uses.

## The mosaic

Topics that grew out of NRS³ live in their own short repositories, each with one figure, one
table of Lean theorems and its own build (Mathlib only; `nrs3-defect-curvature`,
`nrs3-rovelli-lqg` and `nrs3-dark` build on this repository):

| Repository | In one line |
|---|---|
| [**Physlib: merged pull requests**](https://github.com/leanprover-community/physlib/pulls?q=is%3Apr+is%3Amerged+author%3Anaype888-cloud) | NRS, NRS³ and det\|NRS³ in Physlib, the Lean physics library of the community (open tight binding chain, cube, Robertson determinant, velocity band, Pauli and Dirac matrices, Planck) — [![merged](https://img.shields.io/github/issues-search?query=repo%3Aleanprover-community%2Fphyslib%20is%3Apr%20is%3Amerged%20author%3Anaype888-cloud&label=merged&color=blue)](https://github.com/leanprover-community/physlib/pulls?q=is%3Apr+is%3Amerged+author%3Anaype888-cloud) [![in review](https://img.shields.io/github/issues-search?query=repo%3Aleanprover-community%2Fphyslib%20is%3Apr%20is%3Aopen%20author%3Anaype888-cloud&label=in%20review&color=lightgrey)](https://github.com/leanprover-community/physlib/pulls?q=is%3Apr+is%3Aopen+author%3Anaype888-cloud) |
| [`nrs3-mandelstam-tamm-cramer-rao`](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao) | no orthogonality before `πħ/(2ΔE)`, sharp; Cramér–Rao `F_X ≤ 4 Var H`, efficiency `1/C_Nava(d)²` on NRS³ — [▶ interactive](https://naype888-cloud.github.io/nrs3-mandelstam-tamm-cramer-rao/) |
| [`nrs3-landauer-carnot`](https://github.com/naype888-cloud/nrs3-landauer-carnot) | erasing a bit costs `k_B T ln 2`; no engine beats `1 − T_c/T_h`; one bath gives no work (Physlib) — [▶ interactive](https://naype888-cloud.github.io/nrs3-landauer-carnot/) |
| [`nrs3-de-sitter`](https://github.com/naype888-cloud/nrs3-de-sitter) | the horizon entropy fixes the cosmological constant, `Λ = 3π/(ℓ_P² S)`, solving both Friedmann equations (Physlib) — [▶ interactive](https://naype888-cloud.github.io/nrs3-de-sitter/) |
| [`nrs3-penrose`](https://github.com/naype888-cloud/nrs3-penrose) | Penrose's `ħ/ΔE` is a bound, not a lifetime (proposal, outside NRS³) |
| [`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac) | exclusion, shells `2n²`, three spin matrices in `2 × 2`; with time, `4 × 4` (Dirac) |
| [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone) | the Gram matrix of a conjugate pair is a Minkowski four-vector; Robertson–Schrödinger is the light cone, the NRS³ quantum keeps it strictly inside — [▶ interactive](https://naype888-cloud.github.io/nrs3-uncertainty-cone/) |
| [`nrs3-poincare`](https://github.com/naype888-cloud/nrs3-poincare) | Planck's law forces discrete levels (Poincaré 1912) |
| [`nrs3-defect-curvature`](https://github.com/naype888-cloud/nrs3-defect-curvature) | each non-local link closes a cycle with one quantum `δ∞`; `2g` links fix the curvature of `Σ_g`; the entropy of a cut counts its quanta and its horizon hides them (`D16`–`D16i`) — [▶ interactive](https://naype888-cloud.github.io/nrs3-defect-curvature/) |
| [`nrs3-rovelli-lqg`](https://github.com/naype888-cloud/nrs3-rovelli-lqg) | LQG area quanta and puncture entropy; the NRS angle stays below its ceiling `arccos(1/C∞)`, a limit never attained (proposal, outside NRS³) — [▶ interactive](https://naype888-cloud.github.io/nrs3-rovelli-lqg/) |
| [`nrs3-dark`](https://github.com/naype888-cloud/nrs3-dark) | what light does not resolve, `1 − Ω_b`, is the interior of the volumetric quantum; `omegaPi = (δ∞/(1+δ∞)) e^{−1/(1+δ∞)}` from `π`, inside the measured `Ω_b` of Planck, LUNA and DESI — [▶ interactive](https://naype888-cloud.github.io/nrs3-dark/) |

## Timeline 1911–1945

NRS answers a question of the Solvay era with later tools. The series is placed in that window:
what falls inside it is the history the theorem belongs to; what falls after it is a proposal,
not part of NRS³.

| Year | Event | Repository |
|---|---|---|
| 1911 | First Solvay conference: radiation and the quanta | |
| 1911–12 | Poincaré: Planck's law forces discrete levels | [`nrs3-poincare`](https://github.com/naype888-cloud/nrs3-poincare) |
| 1915–20 | Szegő: limit theorems for Toeplitz matrices (the limit `C∞`, `D8`) | **[base repository (NRS, NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger)** (this one) |
| 1917–27 | Einstein and de Sitter: `Λ` and the empty universe; Friedmann and Lemaître: the expanding universe | [`nrs3-de-sitter`](https://github.com/naype888-cloud/nrs3-de-sitter) |
| 1925–27 | Pauli: exclusion, shells `2n²`, spin matrices | [`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac) |
| 1927 | Heisenberg's relation; fifth Solvay conference: electrons and photons | |
| 1928 | Dirac: the `4 × 4` gamma matrices | [`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac) |
| 1929 | van der Waerden: spinors, `SL(2, ℂ)` on Hermitian matrices; the uncertainty cone | [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone) |
| **1929–30** | **Robertson and Schrödinger: the uncertainty inequality** | **[base repository (NRS, NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger)** (this one) |
| **1934** | **Robertson: the indeterminacy relation for several observables, `det Σ ≥ |det Ω|`** | **[base repository (det\|NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger)** (this one) |
| 1945–46 | Mandelstam–Tamm: the time–energy bound; Rao (1945), Cramér (1946) | [`nrs3-mandelstam-tamm-cramer-rao`](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao) |

**Tools from after the window.** Niven (1956: rational values of the trigonometric functions),
Fiedler (1973: algebraic connectivity), Lean 4 and Mathlib (the verification). The question is
of 1929; the tools are later; the checking is of 2026.

**After the window: proposals, not NRS³.** [`nrs3-penrose`](https://github.com/naype888-cloud/nrs3-penrose) (Penrose 1996, gravity-related
collapse) and [`nrs3-rovelli-lqg`](https://github.com/naype888-cloud/nrs3-rovelli-lqg) (loop quantum gravity, area spectrum 1995). They use NRS³ results
but their physical readings belong to quantum information and quantum gravity.
[`nrs3-defect-curvature`](https://github.com/naype888-cloud/nrs3-defect-curvature) restates base theorems (`D16`–`D16i`); its Bekenstein–Hawking (1973–75) reading
is a declared bridge.


## License

[NRS Noncommercial License 1.0.0](LICENSE) — free for noncommercial, academic, humanitarian and
public-institution use, and free to reuse as a contribution to any open source formal-verification
project (Mathlib, Physlib, Lean 4, or any other). See [LICENSE](LICENSE) §4 for commercial use.

## Reproduce the verification

The package in this repository (the open cube) is verified as described in
[`NRS_OPEN_CUBE.md`](NRS_OPEN_CUBE.md#reproduce-the-verification).

# Conjugate pairs realized on `T_d : P_d`

Robertson (1929) and Schrödinger (1930) state their inequality for any two observables `A`, `B`
and a normalized state; the theorem carries no list of pairs (`D2`). In finite dimension no
commutator is a nonzero multiple of the identity (`D12`), so every pair on `d` levels enters
through `⟨[A, B]⟩` at a state. NRS evaluates it on `T_d : P_d` at the maximal-tension state `ψ*`.

A pair realized on `T_d : P_d` is `A = a T_d + b`, `B = c P_d + e` with `a, c ≠ 0`: `P_d` orders
the `d` values of the pair, `T_d` is the step between consecutive values, and `a, b, c, e` are
its units and origins. `D39` proves that none of them reaches NRS or NRS³:

* ratio `R = σ_A σ_B / |⟨Ã ψ*, B̃ ψ*⟩| = C_Nava(d)` for every pair (`razon_par`);
* `R = 1` exactly at `d = 2, 3` (`satura_par_iff`); from `d = 4` on the angle is positive
  (`angulo_par_pos`), grows strictly with `d` (`angulo_par_lt_of_lt`) and stays below
  `arccos (1 / C_∞)`, which no `d` attains (`angulo_par_lt_limite`);
* three pairs on the cube, each in its own units: the product of their excesses is the
  volumetric quantum `𝒱(dx, dy, dz)`; zero only at a seed axis, positive from `4 × 4 × 4`,
  below `δ_∞³` (`cuantoVolumetrico_pares`, `cuanto_volumetrico_pares`).

What a pair changes is only its floor, `|a c| · ½ |⟨[T_d, P_d]⟩| = |a c| / (d − 1)`, in its own
units. The column `C_Nava(d)` of the README table is the same for every row below.

| # | Pair | `P_d`: the ordered values | `T_d`: the step |
|---|---|---|---|
| 1 | position `x` – momentum `p_x` | cell along `x` | hop to the next cell |
| 2 | position `y` – momentum `p_y` | cell along `y` | hop to the next cell |
| 3 | position `z` – momentum `p_z` | cell along `z` | hop to the next cell |
| 4 | centre of mass – total momentum; relative coordinate – relative momentum | cell of the coordinate | hop |
| 5 | lattice site – lattice momentum (tight-binding chain, open ends) | site | hop |
| 6 | waveguide index – transverse momentum | guide | evanescent coupling |
| 7 | site of a spin chain, one-excitation sector – exchange | excited site | exchange with the neighbour |
| 8 | level `n` of a `d`-level system – drive between consecutive levels | level | drive `n ↔ n+1` |
| 9 | field `φ(x)` – conjugate momentum `π(x)`, site by site | field value | step of field value |
| 10 | vector potential `A` – electric field `E`, mode by mode | value of `A` | step of `A` |
| 11 | quadrature `X` – quadrature `Y` of a mode | value of `X` | step of `X` |
| 12 | photon number `n` – quadrature | photon number | `n ↔ n+1` |
| 13 | link electric field `E` – link variable `U` (lattice gauge theory) | value of `E` | `U`: `E ↔ E+1` |
| 14 | photon number `n` – phase `φ` | photon number | phase shift `n ↔ n+1` |
| 15 | Cooper-pair number `n` – Josephson phase `φ` | charge state | tunnelling `n ↔ n+1` |
| 16 | charge `Q` – flux `Φ` (LC circuit) | value of `Q` | step of `Q` |
| 17 | number difference – relative phase (two-mode condensate) | number difference | one particle between modes |
| 18 | angle `φ` – angular momentum `L_z` | value `m` of `L_z` | `m ↔ m+1` |
| 19 | angle – action (action–angle variables) | value of the action | step of the action |
| 20 | clock `Z` – shift `X` (Weyl pair, `d` levels) | clock value | shift by one |
| 21 | `σ_z` – `σ_x` of a qubit | `±1` | flip; exactly `(P_2, T_2)` |
| 22 | `J_z` – `J_x` (and cyclic: `J_x – J_y`, `J_y – J_z`), spin or angular momentum | value `m` of `J_z` | `m ↔ m+1` |
| 23 | isospin and colour generators | weight along one generator | step between weights |
| 24 | kinetic momenta `π_x` – `π_y` in a magnetic field (Landau levels) | Landau level | `n ↔ n+1` |
| 25 | guiding centre `X` – `Y` in a magnetic field | level of the guiding-centre oscillator | `n ↔ n+1` |
| 26 | time `t` – energy `E` | registered tick | step between ticks |
| 27 | time – frequency of a signal (Fourier, Gabor) | time bin | step between bins |

Rows 26 and 27: in the theorem of 1929–1930 time is not an operator, and the reading of time
as registered ticks belongs to the physical layer, which is outside this repository. Row 27
concerns classical signals with the same algebra as row 1.

Rows 1–3 are the three axes of the cube of `D37`; any three rows whose pairs commute with each
other can occupy the three axes, and `cuanto_volumetrico_pares` applies to them.

The table and this catalogue, explained, as a PDF: [`NRS_Pairs_Table.pdf`](NRS_Pairs_Table.pdf)
(source in `tex/`, built with `xelatex`).

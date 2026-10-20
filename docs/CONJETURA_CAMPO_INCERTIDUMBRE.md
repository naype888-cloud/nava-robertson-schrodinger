# Conjetura del campo de incertidumbre

*Borrador, 2026-10-11. Nota de trabajo: cada afirmación cita la declaración Lean que la prueba o
dice qué falta. Lo nuevo de (G) y del nivel del campo está en el mosaico, en local.*

**Alcance (§7).** La conjetura junta cinco piezas: el campo de incertidumbre, la gravedad
cuántica de bucles, el espacio-tiempo de Minkowski, QFT y ΛCDM. El espacio-tiempo entra por el
lado de la métrica.

## 0. En una línea

Un mismo objeto algebraico, el defecto de Gram del par energía–posición en dimensión `d`, se lee
como **espacio** (cuanto volumétrico, `det Σ / |det Ω|`), como **tiempo** (cociente de
Mandelstam–Tamm) y como **gravedad** (`Λ` contado en un corte). La conjetura dice que estas tres
lecturas son una sola función del estado, el **campo de incertidumbre** `𝒰_ω`, y que la tercera
no requiere ninguna premisa aparte de `𝒰_ω`.

## 1. El objeto: `𝒰_ω`

Sea `ω` un estado sobre una C⋆-álgebra `A`, y `a`, `b` observables. Defino

```
𝒰_ω(a, b) := Var_ω a · Var_ω b − ω⟨⁅a, b⁆⟩²
           = centeredGramDefect ω a b + Cov_ω(a, b)²   ≥ 0
```

- La identidad es `UnitalPositiveLinearMap.robertson_gap_decomposition`, y su positividad es
  `centeredGramDefect_nonneg` más `Cov² ≥ 0`
  (`PhyslibAlpha/ProbabilisticTheory/CStarAlgebra/Uncertainty.lean`, #1649 y #1650, fusionados).
- No hay partículas. Solo intervienen un álgebra y un estado, que es el marco de Haag–Kastler. Los
  estados vectoriales (#1660) y de densidad (#1676, `ofDensity_rankOne`) son casos particulares.
- Para varios observables: `robertson_det`, `|det Ω| ≤ det Σ`.

`𝒰_ω` tiene dos partes de naturaleza distinta:

| parte | qué es | carácter |
|---|---|---|
| corchete `ω⟨⁅H, X⁆⟩` | la corriente: `⁅H, X⁆ = −J/2` (`coe_bracket_openHamiltonian_position`, #1711); `J` solo mueve un paso (`inner_current_eq`, #1696) | **local**: `J` mueve un paso en cada posición, para todo `N` (`inner_current_eq`), acotado por el cono `mandelstam_tamm` |
| defecto + `Cov²` | `Var·Var − corchete²` | **correlación**: `Var` contiene `⟨X⟩²`, que es una función de dos puntos y no una suma de densidades |

En los estados estacionarios y en los localizados el corchete vale cero (`inner_current_self_of_eigen`,
`inner_current_localizedState`), pero `𝒰_ω` no: toda la incertidumbre queda en la parte de
correlación. El corchete del operador nunca se anula: `[H, X] ≠ 0` aunque `⟨J⟩ = 0`.

## 2. La dimensión `d`

Sobre la cadena abierta de `d` posiciones, en el estado de corriente máxima:

- `Var H · Var X = (a t cos(π/(d+1)))² + defecto`, con `Cov = 0`
  (`variance_mul_variance_maxCurrentState`, `covariance_maxCurrentState`, #1723).
- `C_Nava(d) = 1` si y solo si `d = 2, 3` (`CNava_eq_one_iff`), y `C_Nava(d) > 1` desde `d = 4`
  (`one_lt_CNava`). **El defecto es irreducible a partir de 4.**
- `C_Nava` crece estrictamente con `d` (`CNava_lt_CNava`, #1735) y queda acotado,
  `C_Nava(d) < C_∞ = √(π²/3 − 2)` (`CNava_lt_sqrt_pi_sq_div_three_sub_two`). `C_∞` es el límite
  de Szegő (`tendsto_CNava`, #1734) y nunca se alcanza.
- El cuanto dimensional es `δ(d) = C_Nava(d) − 1`.

## 3. Las tres lecturas

### (E) Espacio: probado, fusionado

`Cube.lean` (#1725, #1742). Ejes distintos conmutan (`bracket_alongX_alongY`, …), así que `Ω` es
diagonal por bloques en **todo** estado (`bracketMatrix_cubePairs`), y en el estado de corriente
máxima

```
det Σ = (C_Nava(x) · C_Nava(y) · C_Nava(z))² · |det Ω|     (det_covarianceMatrix_maxCurrentCubeState)
```

Desde `4 × 4 × 4` la desigualdad es estricta en los tres ejes a la vez
(`nava_robertson_schrodinger_cube`, `robertson_det_maxCurrentCubeState_strict`). Para todo estado
cuya velocidad cae en la banda de cada eje, la desigualdad sigue siendo estricta:
`robertson_det_band_strict` (D49t, en este repo, local).

### (T) Tiempo: probado, fusionado

`MandelstamTamm.lean` (#1711) y `MandelstamTammMaxCurrent.lean` (#1739):

```
|⟨J⟩| ≤ 2 ΔH ΔX                                    (mandelstam_tamm, todo estado)
⟨J⟩² / (4 Var H · Var X) = 1 / C_Nava²             (mandelstamTammRatio_maxCurrentState)
```

El cociente vale 1 solo con `d = 2, 3` y es `< 1` desde `4`
(`mandelstamTammRatio_maxCurrentState_eq_one_iff`, `…_lt_one`). Cada eje del cubo tiene su propio
cociente (`mandelstamTammRatio_alongX`, `Y`, `Z`).

**(E) y (T) son el mismo número.** No es una coincidencia que haya que explicar: `C_Nava` es la
razón `√(Var H · Var X) / |corchete|`. Robertson la lee como volumen y Mandelstam–Tamm como rapidez
de evolución.

### (G) Gravedad: el álgebra está escrita, pero en local

Ramas del fork, todavía no subidas:

- `horizon-count` (`HorizonCount.lean`): con `k` cuantos sobre los `M` eslabones que cruzan un
  corte, `W = M^k`, `cutEntropy = k log M`, `Λ = 3π/(ℓ² log W)`. Se cumplen las dos ecuaciones de
  Friedmann (`countCosmologicalConstant_firstOrderFriedmann`, `…_secondOrderFriedmann`).
- `nrs3-cosmological-constant` (`DefectCosmologicalConstant.lean`): cada cuanto lleva `δ`, y
  `Ω = k δ` (`quantumDefect`). `Ω = 0` con `d = 2, 3`, y `0 < Ω < k(C_∞ − 1)` desde `4`. Además
  `S = (log M / δ) Ω` (`cutEntropy_eq_mul_quantumDefect`) y `Λ = 3πδ/(ℓ² log M · Ω)`
  (`countCosmologicalConstant_eq_quantumDefect`). En el cubo, `Ω_x = 0` si y solo si la relación
  del eje `x` es una igualdad (`quantumDefect_alongX_eq_zero_iff`, `countCosmologicalConstant_cube`).
- `cosmological-constant-chain`: `Λ = 3π/(ℓ² log W) = 12π/A = 6π²/(ℓ² log M (4π − ∫K dA))`
  (`countCosmologicalConstant_chain`).

**La premisa.** En la cadena (`HorizonCount`), `S = k log M` es definición y `k` queda libre:
`deSitterEntropy_countCosmologicalConstant` da `k log M = 3π/(ℓ²Λ)`, una ecuación con dos
cantidades (fijas `k` y sale `Λ`, o mides `Λ` y sale `k`). Además ahí los `M` pares de
`cutBonds` son de alcance ≥ 2, donde `H` y `J` se anulan.

**En el cubo (`nrs3-defect-curvature/AreaLaw.lean`, local), `k` ya no es libre.** Los pasos que
cruzan el plano entre `x = c` y `x = c + 1` son exactamente los de transporte
`(c, y, z) → (c + 1, y, z)` (`T3_ne_zero_iff`); hay `dy · dz` (`card_crossSteps`), sin depender
de la profundidad ni del plano (`cutEntropy_eq_of_depth`). Cada uno abierto o cerrado: `W = 2^(dy·dz)`,
`S = dy·dz·log 2` (`cutEntropy_eq`), `S = (log 2 / δ) Ω` desde `dx ≥ 4`
(`cutEntropy_eq_mul_cutDefect`), y `S = A/(4ℓ_P²)` iff `a² = 4ℓ_P² log 2` (`bekensteinHawking_iff`).

**`k` es el área de la cara, y la cara es un pseudovector.** `A_x = (dy ŷ) × (dz ẑ) = dy·dz · x̂`:
la magnitud es `k = card_crossSteps`, la dirección es la normal, el sentido del cruce `c → c + 1`.
Las tres caras dan `A = (dy·dz, dz·dx, dx·dy)` (la permutación cíclica de `cutDefect dy dz dx`,
`cutDefect dz dx dy`) y `A_x A_y A_z = V²`, la `V²` de `prod_cutDefect`. Por Lagrange,
`|a|²|b|² − (a·b)² = |a × b|²`: el defecto de Gram `Var·Var − Cov²` es también un área al
cuadrado (`τ = σ_A σ_B sen θ`). Cuidado: `(⟨J_x⟩, ⟨J_y⟩, ⟨J_z⟩)` es velocidad (polar), no
pseudovector; la corriente cruza la cara. En Lean no hay nada aún; Physlib ya tiene `⨯ₑ₃` sobre `EuclideanSpace ℝ (Fin 3)`
(`Physlib/SpaceAndTime/Space/CrossProduct.lean`), sobre el `crossProduct` de Mathlib.

**El `log 2` por paso ya no es premisa (2026-10-11, `AreaLaw.lean` §8, local).** Un paso une dos
posiciones; sobre él el corchete vale `κ` hacia adelante y `−κ` hacia atrás, `κ = 2/(ρ(dx − 1))`
(`bracketX_crossStep`), y solo lee la coherencia `z = ψ̄_p ψ_q` de sus extremos, por `κ(z − z̄)`
(`bracketX_stepTerm`). Abierto = `z ≠ 0`, cerrado = `z = 0` (`openSteps`). Los pasos de distintos
`(y, z)` no comparten posición, así que todo subconjunto se abre con algún estado unitario
(`cutPatterns_eq`): `2^(dy·dz)` patrones (`card_cutPatterns`) y `S = log #patrones`
(`cutEntropy_eq_cutPatterns`). Todo en el teorema de una partícula; por `cutEntropy_eq_of_depth`
vale igual a toda escala.

## 4. La conjetura

> **Conjetura (campo de incertidumbre).** Sea `ω` un estado de la red local de C⋆-álgebras del
> cubo `Nx × Ny × Nz`, y sea `𝒰_ω` restringido a cada región `O` y a cada par `(H_i, X_i)` de un
> eje. Entonces una sola función, `𝒰_ω`, fija las tres lecturas:
>
> 1. **(E)** `det Σ / |det Ω| = ∏ᵢ C_Nava(Nᵢ)²`. *Probado.*
> 2. **(T)** el cociente de Mandelstam–Tamm del eje `i` es `1 / C_Nava(Nᵢ)²`. *Probado.*
> 3. **(G)** para un corte `∂O` transversal al eje `i`, la entropía del corte está determinada
>    por `𝒰_ω` restringido a los observables de los eslabones que cruzan `∂O`, y coincide con
>    `(log M / δᵢ) · Ωᵢ(∂O)`. Por tanto `Λ = 3πδᵢ / (ℓ² log M · Ωᵢ(∂O))` es una función de `𝒰_ω`.
>    *Cerrado en el cubo (2026-10-11, local, sin push).* Mosaico `AreaLaw.lean` §6–9:
>    la entropía del corte sale del corchete y `Λ = 3π/(ℓ² dy dz log 2)`; con `a² = 4ℓ² log 2`
>    por paso, el área del horizonte `12π/Λ` es el área de la cara (`horizonArea_cutCosmologicalConstant`).
>    Fork: `PhyslibAlpha/CondensedMatter/TightBindingChain/CubeCut.lean` (rama
>    `feat-physlibalpha-cube-cut-entropy`): `coe_bracket_alongX` (`⁅H_x, X_x⁆ = −J_x/2` en el cubo),
>    `card_crossSteps`, `currentX_stepTerm`, `cutPatterns_eq`, `cutEntropy_eq`, `faceArea_eq`
>    con `⨯ₑ₃`, `cutCosmologicalConstant_eq`, ambas ecuaciones de Friedmann y
>    `deSitterHorizonArea_cutCosmologicalConstant`.*
>
> **Forma fuerte.** (G) vale para todo estado `ω` en la banda `Ϙ` de cada eje, no solo para el
> estado de corriente máxima, como ya ocurre con (E) (D49t) y con la desigualdad de (T)
> (`mandelstam_tamm`).

### Espacio, tiempo y gravedad: qué es `𝒰_ω` y en qué dirección van las flechas

- **El espacio** son las posiciones `x, y, z` del cubo. `𝒰_ω` vive sobre ellas: para cada estado
  y cada par de observables que no conmutan, dice cuánto lleva el estado por encima del mínimo
  de Robertson. Estado, espacio y `𝒰_ω` son tres piezas distintas.
- **El tiempo** sale de la evolución. `𝒰_ω` marca su ritmo: el cono `mandelstam_tamm` acota la
  rapidez de cambio por la varianza de la energía, con cociente `1 / C_Nava²` (lectura (T)).
- **La gravedad**: en lo probado, la incertidumbre es la causa y la geometría el efecto.
  - El corchete fija la entropía del corte, y la entropía fija `Λ` (`cutCosmologicalConstant`,
    `AreaLaw.lean` §9).
  - El defecto fija la curvatura (`defect_fixes_curvature`, con Gauss–Bonnet declarado).
- **Abierto: la flecha de regreso.** Que la curvatura o `Λ` modifiquen `𝒰_ω` cerraría el ciclo
  de Einstein (la materia curva el espacio, la curvatura mueve la materia). Hoy no hay ningún
  teorema en esa dirección.

### El viaje: el evento, la luz, el camino de vuelta

En palabras del autor (2026-10-11): espacio-tiempo de Minkowski cuantizado con causalidad. El
evento inicia, sucede y termina; viaja por las posiciones que portan la luz, medimos su espectro
y por eso es real. El camino de regreso no es el camino inverso, en el sentido de que no te
regresa nada: la entropía del viaje no depende de la dirección del recorrido. El espacio existe,
la red puede existir según a dónde te muevas, pero siempre dentro del campo de incertidumbre, que
separa lo que medimos y vemos de lo que se nos escapa.

| Afirmación | Lean |
|---|---|
| el evento tiene inicio y frente: a `r` pasos no llega nada antes del paso `r`, y en el paso `r` sí | `event_window` (`nrs3-landauer-carnot/LightCone.lean`) |
| la luz resuelve todo menos el cuanto volumétrico `𝒱 > 0`; lo resuelto es lo medido, `Ω_b` | `nrs3_dark` (`nrs3-dark`) |
| la red de pasos abiertos la decide el movimiento (la coherencia del estado), no una medición | `openSteps`, `cutPatterns_eq` (`AreaLaw.lean` §8) |
| siempre dentro del cono: el cuadrivector de incertidumbre queda dentro del cono de Minkowski | `nrs3-uncertainty-cone` |
| un paso está abierto de vuelta si y solo si lo está de ida: la coherencia no tiene dirección | `openBackSteps_eq` (`AreaLaw.lean` §10) |
| la entropía del corte es la misma en las dos direcciones | `backEntropy_eq_cutEntropy` |
| ida y vuelta suman `2 dy dz log 2 > 0`: el regreso no deshace nada | `roundTripEntropy_eq`, `roundTripEntropy_pos` |

Mosaico `nrs3-defect-curvature`, commit `cdb47be`, local. Axiomas estándar.

## 5. Qué falta, en orden

1. **Observables hermitianos, conmutantes y no conmutantes: ya están en el teorema.**
   `robertson`, `robertson_schrodinger` y `robertson_det` viven sobre `Observable A` (autoadjuntos de
   una `CStarAlgebra A`, con producto y corchete `⁅a, b⁆`). Pares que no conmutan: `(H, X)` del
   mismo eje. Pares que conmutan: ejes distintos, `bracket_cubePairs_of_ne`
   (`bracket_alongX_alongY`, …), de donde `bracketMatrix_cubePairs`. No hace falta ninguna red
   externa. `LocalNet` (#1769, fusionado 10-10) deja los observables como espacio ordenado sin
   producto, así que ahí no hay corchete: NRS vive en la capa C⋆ de `Uncertainty.lean`.
2. **Regiones disjuntas de un eje: fuera del estudio.** Observables que conmutan (`AB = BA`) son
   el caso clásico; su corchete es cero y no aportan nada a `𝒰_ω`. NRS³ estudia solo los pares
   que no conmutan. Lo que importa son los pasos que cruzan el corte, donde vive `⁅H, X⁆ = −J/2` (en el cubo,
   `crossSteps`; en la cadena los `cutBonds` de alcance ≥ 2 son otra cosa);
   dentro de la banda el defecto es forzoso (`defectOf_pos_of_mem_velocityBand`), y con `d = 2, 3`
   la banda es vacía (`velocityBand_eq_empty`). Esto es entrada de (G), no un paso aparte.
3. **La corriente en cada posición, para todo `N`: ya está.** `inner_current_eq` (sobre
   `Fin T.N`), `current_maxCurrentState` y el cono `mandelstam_tamm` valen para todo `N` y todo
   estado, y `mandelstamTammRatio_alongX/Y/Z` en cada eje del cubo. El `d = 4` de
   `tension_currents` (D23g) es solo el andamio del certificado SOS de la cota `1/φ`, no un
   límite del teorema. `N → ∞` solo lleva `C_Nava → C_∞` (Szegő), nunca alcanzado.
4. **(G) desde `𝒰_ω`, sobre el cubo: el soporte del corchete está probado (local, 2026-10-11).**
   En `nrs3-defect-curvature/NRS3DefectCurvature/AreaLaw.lean` §6–7: `bracketX_apply`
   (`[T3, P_x] p q = T3 p q · (x_q − x_p)`), `bracketX_ne_zero_iff` (a través del plano, corchete
   ≠ 0 ⟺ transporte ≠ 0), `bracketCrossSteps_eq` (= `crossSteps`), `card_bracketCrossSteps`
   (`dy·dz`), `cutEntropy_eq_bracket` (la entropía del corte se lee en el corchete), `faceArea_eq`
   (`(dy ŷ) × (dz ẑ) = dy·dz·x̂`, con `crossProduct` de Mathlib) y `faceArea_zero` (la longitud de
   la cara es el número de pasos que ve el corchete). Axiomas estándar, sin warnings. El `log 2`
   por paso también sale del corchete (§8, ver §3(G)).
5. **El nivel del campo cuantizado: el sector de una excitación es el cubo (local, 2026-10-11).**
   En `nrs3-defect-curvature/NRS3DefectCurvature/FieldLevel.lean`, cada posición `p` del cubo es
   un modo de `LadderSystem` (Physlib) y `dΓ M = Σ M_pq a†_p a_q` es `toGlHomLinear` leído en las
   posiciones. Probado:
   - `secondQuant_lie`: `dΓ ⁅M, N⁆ = ⁅dΓ M, dΓ N⁆` en todo `V`, es decir, en todos los sectores
     `n`. En el cubo, `lie_secondQuant_cube`: `⁅dΓ T3, dΓ P_x⁆ = dΓ [T3, P_x]`.
   - `secondQuant_oneExcitation`: `dΓ M (Σ ψ_p a†_p Ω) = Σ (M ψ)_p a†_p Ω`.
   - `form_oneExcitation`, `uncertainty_oneExcitation`: con la estructura ⋆, `𝒰` del campo es
     `𝒰` del cubo.
   - `exists_field_pattern`: cada patrón de pasos abiertos es un estado del campo, unitario,
     y el corchete del campo lee el del cubo. Por eso `S = dy · dz · log 2` y `Λ` son los mismos
     al nivel del campo.

   La estructura ⋆ entra como hipótesis declarada, `IsStar`: una forma sesquilineal `β` con
   `β(a†x, y) = β(x, a y)` y `β(Ω, Ω) = 1`. Physlib tiene la adjunción de `a`, `a†` como TODO
   abierto en `HarmonicOscillator/LadderOperators.lean`, y ese oscilador vive en Schwartz, que no
   es `InnerProductSpace`; por eso se usa una forma y no un producto interior. Cuando Physlib
   cierre ese TODO, `IsStar` se instancia con el L². Axiomas estándar (43 en
   `Verification/Axioms.lean`). Commit a15f8b5.

   **Los sectores `n ≥ 2` están cerrados** en `nrs3-tritoro`: `TorusSectors` (dos excitaciones,
   afe6245) y `TorusFock` (`n` excitaciones, 0cb307a): `secondQuant_nExcitation`, `nBody_lie`,
   `form_nExcitation_symm` (`β = n! Ψ̄ · Φ`) y `uncertainty_nExcitation` (el `𝒰` del campo es el
   de las matrices de `n` cuerpos en `√(n!) Ψ`); el corte con `n − 1` espectadores en
   `TorusFockCut.form_bracket_n`. Sigue abierto el TODO de Physlib de `IsStar` sobre el L².

## 6. Forma en Lean (esquema, sin compilar)

```lean
/-- The uncertainty field of a state: the slack of Robertson's relation. -/
noncomputable def uncertaintyField (ω : 𝓢[ℂ, A]) (a b : Observable A) : ℝ :=
  variance ω a * variance ω b - ω⟨⁅a, b⁆⟩ ^ 2

lemma uncertaintyField_eq (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    uncertaintyField ω a b = centeredGramDefect ω a b + covariance ω a b ^ 2 :=
  robertson_gap_decomposition ω a b

-- (E) and (T) in terms of `C_Nava`: already `det_covarianceMatrix_maxCurrentCubeState`
-- and `mandelstamTammRatio_maxCurrentState`.

-- (G), the open step: for a cut `c` of the chain,
--   cutEntropy c = F (uncertaintyField ω (bondObservable c ·) (bondObservable c ·))
-- for an explicit `F`, with no counting premise.
```

## 7. El alcance: cinco piezas, una sola conjetura

La conjetura completa junta en un solo objeto, `𝒰_ω`, la gravedad cuántica de bucles, el
espacio-tiempo de Minkowski, QFT y ΛCDM. El espacio-tiempo entra **por el lado de la métrica**:
el intervalo de Minkowski es el defecto de Gram de la incertidumbre (van der Waerden 1929).

| Pieza | Lo que ya está en el git | Costura que falta |
|---|---|---|
| **Campo de incertidumbre** | `𝒰_ω = centeredGramDefect + Cov²` (`robertson_gap_decomposition`); (E) y (T) fusionados; (G) en el cubo (`AreaLaw.lean` §6–9) | flecha de regreso gravedad → `𝒰_ω` (§4) |
| **Minkowski (métrica)** | `nrs3-uncertainty-cone`: la incertidumbre del par es un cuadrivector; `interval_eq_gramDefectC` (intervalo = defecto de Gram), `interval_gram_boost` (cambio de unidades = boost), Robertson–Schrödinger = cono de luz, el cuanto de NRS³ deja el vector dentro del cono | escribir el `𝒰_ω` del cubo como intervalo, eje por eje, y ver `𝒰_ω` como la métrica |
| **Gravedad cuántica de bucles** | `nrs3-rovelli-lqg`: `areaSpectrum`, `cutEntropy_eq_punctureEntropy` (`k` cuantos en el corte = `k` punciones de espín `j`, con `M = 2j + 1`), `bekensteinHawking_iff_immirzi` (`γ = log 2 / (π√3)` para espín `1/2`) | en el cubo cada paso es abierto o cerrado, `M = 2`, o sea **espín `1/2`**: falta el teorema "los `dy·dz` pasos de la cara son `dy·dz` punciones de espín `1/2`", que conecta `AreaLaw` con el valor de Immirzi |
| **QFT** | `FieldLevel.lean` (mosaico, a15f8b5): `dΓ` respeta corchetes en todo sector; el sector de una excitación es el cubo; `𝒰` del campo = `𝒰` del cubo | estructura ⋆ (TODO de Physlib); los sectores `n ≥ 2` ya están en `nrs3-tritoro` (`TorusFock`) |
| **ΛCDM** | `nrs3-de-sitter` (`Λ = 3π/(ℓ² S)`, ambas Friedmann); Physlib FLRW (equipo de Joseph, Kevorkian); `nrs3-dark` (`1 − Ω_b`, el interior del cuanto volumétrico) | unir el `Λ` del corte del cubo con el sector oscuro `1 − Ω_b` y con la evolución FLRW |

Orden de cierre sugerido: (1) punciones de espín `1/2` en el cubo, que es lo más corto porque
ambas mitades ya están probadas; (2) `𝒰_ω` como intervalo de Minkowski en el cubo; (3) `Λ` del
corte con FLRW y `1 − Ω_b`; (4) la flecha de regreso.


## 8. Forma precisa: campo espectral y campo de incertidumbre (2026-10-18)

**Enunciado (del autor).** Todo campo se compone de un **campo espectral** y de su **campo de
incertidumbre** complementario. Sin importar la `c` del sistema, todo campo es analizable y siempre
da una relación de incertidumbre. Esa relación deja siempre un **cuanto de irresolubilidad**, la parte
del espectro que no se puede medir. La parte medible es conexa: es el **cono de Minkowski**, lo que
medimos de la luz.

| Pieza | Qué es | Lean |
|---|---|---|
| campo espectral | lo que el operador puede dar, fijo por el operador | espectro exacto `{2 cos (2πm/d)}` (`periodicChainGraph.hasEigenvalue_hopping_iff`) y `{E0 − 2t cos(ka)}` (`TightBindingChain.hasEigenvalue_hamiltonian_iff`), Physlib local 4b3ddfda, 50f0d5ca; medida espectral de Tom (`CStarAlgebra/SpectralMeasure`) |
| campo de incertidumbre | lo que el par no puede dar a la vez, fijo por el estado | `robertson`, `robertson_det` (toda C⋆-álgebra, todo estado, toda `c`) |
| complementariedad | concentrar el espectro de `A` manda la indeterminación a `B` | `variance_T_pos_of_P_eigenvector` (D47, #1778) |
| lo medible, conexo | el cono futuro cerrado: nada es espacial | `robertsonSchrodinger_future`, `mem_futureCone`; caja con fibra cerrada: `BoxCone.axisVector_mem_futureCone` (nrs3-hopf) |
| la luz | el borde del cono: defecto cero | `null_maxCurrentState_iff` (`d = 2, 3`) |
| el cuanto irresoluble | el tiempo propio hasta el borde | `properTime_eq_mul_sin`, `properTime_maxCurrentState_pos` (`d ≥ 4`); caja con fibra cerrada, los cuatro ejes en la banda: `BoxCone.properTime_box_pos_of_band` |
| invariancia | el cono no depende del observador | `posSemidef_conj`, `det_conj` (`SL(2, ℂ)`); doble cubrimiento, Physlib #1850 |

**Siguiente:** el nivel del campo cuantizado (§5, paso 5) sobre la caja de cuatro ejes con `w`
cerrada (los sectores `n ≥ 2` ya están en `TorusFock`); después el campo de norma `U(1)` en la fibra.

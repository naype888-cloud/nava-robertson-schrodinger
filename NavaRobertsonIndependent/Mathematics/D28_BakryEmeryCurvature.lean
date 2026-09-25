import NavaRobertsonIndependent.Mathematics.D3_PathGraph

/-!
# D28 — Curvatura de Bakry-Émery del camino discreto: `CD(0,2)`, ajustado

> **Lectura (v14).** La red es el espacio: la estructura más fina que permite el
> álgebra, y su gráfica es la de la obstrucción de Robertson. Que sea plana dice que la
> celda no se curva; la curvatura es efecto de conteo. `D27` (celda estirada, citado abajo) está en
`Superseded`; el mecanismo
> físico vigente es el conteo de celdas (`D32`).

Responde una pregunta concreta que quedó abierta al cerrar `D27`: ¿puede una
curvatura de Ricci discreta medida sobre la cadena de Markov `T_d:P_d` (D3)
alimentar el factor de estiramiento `HCurv` de `D27` con un valor distinto de
cero?

La respuesta, demostrada aquí por álgebra pura —identidad de
Bochner-Weitzenböck discreta, sin `sorry`—: **no, en el interior del camino
la curvatura de Bakry-Émery es exactamente cero, y la cota es ajustada**
(`CD(0,2)`: ni el `0` ni el `2` se pueden mejorar). Esto confirma, por una vía
completamente distinta (cálculo diferencial discreto vía el Laplaciano del
grafo, en vez de transporte óptimo de Ollivier), lo mismo que ya se sabía:
el camino —el único grafo compatible con localidad + completitud,
`D3.CanalPreFuerza`— es plano. No hay curvatura que extraer de `T_d:P_d` para
acoplar a `HCurv`; ese puente exigiría un objeto distinto del camino, y D3 ya
cierra el camino como el único posible.

## La identidad central

Con `Δf(x) = f(x−1) + f(x+1) − 2f(x)` (Laplaciano combinatorio) y las
definiciones estándar de Bakry-Émery
`Γ(f)(x) = ½[Δ(f²)(x) − 2f(x)·Δf(x)]`,
`Γ₂(f)(x) = ½[Δ(Γf)(x) − 2·Γ(f,Δf)(x)]`
—la versión discreta exacta de la fórmula de Bochner-Weitzenböck
`½Δ|∇f|² = ‖Hess f‖² + ⟨∇f,∇Δf⟩ + Ric(∇f,∇f)`—, se demuestra la identidad
polinómica exacta

`Γ₂(f)(x) = ½·(Δf(x))² + ¼·(f(x−2)−2f(x−1)+f(x))² + ¼·(f(x)−2f(x+1)+f(x+2))²`

de la que `CD(0,2)` sale gratis (`Γ₂ ≥ ½(Δf)²` siempre: suma de cuadrados), y
de la que salen también los dos hechos de ajuste: hay `f` con `Γ₂ = 0` y
`Γ > 0` (la curvatura no puede subir de `κ=0`), y hay `f` con `Δf ≠ 0` donde
`Γ₂ = ½(Δf)²` exactamente (la dimensión efectiva no puede bajar de `n=2`).

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib.
-/

noncomputable section

namespace CurvaturaBakryEmery

open TransportePosicion

/-! ## Capa algebraica: cinco valores consecutivos -/

/-- Laplaciano combinatorio en tres puntos consecutivos `(izq, centro, der)`:
`Δf(x) = f(x−1) + f(x+1) − 2f(x)`. -/
def deltaTres (izq centro der : ℝ) : ℝ := izq + der - 2 * centro

/-- Campo cuadrático de Bakry-Émery `Γ(f)(x)` dados los tres valores
`(izq, centro, der)` alrededor del punto. -/
def gammaTres (izq centro der : ℝ) : ℝ := ((izq - centro) ^ 2 + (der - centro) ^ 2) / 2

/-- `Γ₂(f)(x)` dados los cinco valores consecutivos
`(a,b,c₀,c,e) = (f(x−2), f(x−1), f(x), f(x+1), f(x+2))`. Es la expansión
directa de `½[Δ(Γf)(x) − 2·Γ(f,Δf)(x)]`. -/
def gamma2Cinco (a b c0 c e : ℝ) : ℝ :=
  a ^ 2 / 4 - a * b + a * c0 / 2 + 3 * b ^ 2 / 2 + b * c - 3 * b * c0
    + 3 * c ^ 2 / 2 - 3 * c * c0 - c * e + 5 * c0 ^ 2 / 2 + c0 * e / 2 + e ^ 2 / 4

/-- **Identidad de Bochner-Weitzenböck discreta** (puro álgebra, sin
hipótesis): `Γ₂` se descompone exactamente en el término de curvatura
`(Δf)²/2` más dos cuadrados que miden la falta de continuación afín de `f`
en cada extremo. -/
theorem gamma2_eq_bochner (a b c0 c e : ℝ) :
    gamma2Cinco a b c0 c e
      = (deltaTres b c0 c) ^ 2 / 2 + (a - 2 * b + c0) ^ 2 / 4 + (e - 2 * c + c0) ^ 2 / 4 := by
  unfold gamma2Cinco deltaTres
  ring

/-- **`CD(0,2)`**: `Γ₂ ≥ ½(Δf)²` siempre, en todo punto interior. Curvatura
`κ ≥ 0`, dimensión efectiva `n = 2`. -/
theorem cd_cero_dos (a b c0 c e : ℝ) :
    (deltaTres b c0 c) ^ 2 / 2 ≤ gamma2Cinco a b c0 c e := by
  rw [gamma2_eq_bochner]
  nlinarith [sq_nonneg (a - 2 * b + c0), sq_nonneg (e - 2 * c + c0)]

/-- Corolario inmediato: `Γ₂ ≥ 0` en todo el interior del camino. -/
theorem gamma2_nonneg (a b c0 c e : ℝ) : 0 ≤ gamma2Cinco a b c0 c e := by
  have h := cd_cero_dos a b c0 c e
  nlinarith [sq_nonneg (deltaTres b c0 c)]

/-- Cuando `f` se continúa afinamente más allá de los vecinos inmediatos
(`a = 2b−c₀`, `e = 2c−c₀`), `Γ₂` colapsa exactamente al término de
curvatura: no queda margen para una cota más fuerte. -/
theorem gamma2_eq_en_extension_afin (b c0 c : ℝ) :
    gamma2Cinco (2 * b - c0) b c0 c (2 * c - c0) = (deltaTres b c0 c) ^ 2 / 2 := by
  have h := gamma2_eq_bochner (2 * b - c0) b c0 c (2 * c - c0)
  have e1 : (2 * b - c0) - 2 * b + c0 = 0 := by ring
  have e2 : (2 * c - c0) - 2 * c + c0 = 0 := by ring
  rw [e1, e2] at h
  simpa using h

/-- **La dimensión `n = 2` es ajustada**: hay `f` con `Δf(x) ≠ 0` donde
`Γ₂ = ½(Δf)²` exactamente — ningún `n < 2` puede sostener `CD(0,n)` en el
camino. -/
theorem n_dos_no_mejorable :
    ∃ a b c0 c e : ℝ, deltaTres b c0 c ≠ 0 ∧
      gamma2Cinco a b c0 c e = (deltaTres b c0 c) ^ 2 / 2 := by
  refine ⟨2, 1, 0, 0, 0, ?_, ?_⟩
  · unfold deltaTres; norm_num
  · simpa using gamma2_eq_en_extension_afin 1 0 0

/-- **La curvatura `κ = 0` es ajustada**: hay `f` con `Δf(x) = 0`,
`Γ(f)(x) > 0` y sin embargo `Γ₂(f)(x) = 0` — ningún `κ > 0` puede sostenerse
en el camino. -/
theorem kappa_cero_no_mejorable :
    ∃ a b c0 c e : ℝ,
      deltaTres b c0 c = 0 ∧ 0 < gammaTres b c0 c ∧ gamma2Cinco a b c0 c e = 0 := by
  refine ⟨2, 1, 0, -1, -2, ?_, ?_, ?_⟩
  · unfold deltaTres; norm_num
  · unfold gammaTres; norm_num
  · unfold gamma2Cinco; norm_num

/-! ## Conexión con `GrafoTP d` (D3): el interior del camino -/

/-- Vecino a dos pasos a la izquierda de `i`, dado que hay margen. -/
def im2 {d : ℕ} (i : Fin d) (h : 2 ≤ i.val) : Fin d :=
  ⟨i.val - 2, by have := i.isLt; omega⟩

/-- Vecino inmediato a la izquierda de `i`, dado que hay margen. -/
def im1 {d : ℕ} (i : Fin d) (h : 1 ≤ i.val) : Fin d :=
  ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Vecino inmediato a la derecha de `i`, dado que hay margen. -/
def ip1 {d : ℕ} (i : Fin d) (h : i.val + 1 < d) : Fin d :=
  ⟨i.val + 1, h⟩

/-- Vecino a dos pasos a la derecha de `i`, dado que hay margen. -/
def ip2 {d : ℕ} (i : Fin d) (h : i.val + 2 < d) : Fin d :=
  ⟨i.val + 2, h⟩

/-- `im1 i` y `ip1 i` son, genuinamente, vecinos de `i` en `GrafoTP d`
(`D3.grafoTP_adj`): el Laplaciano que sigue se toma exactamente sobre las
aristas del camino, no sobre un objeto ajeno al corpus. -/
theorem adj_im1 {d : ℕ} (i : Fin d) (h : 1 ≤ i.val) :
    (GrafoTP d).Adj i (im1 i h) := by
  rw [grafoTP_adj]
  right
  show (im1 i h).val + 1 = i.val
  simp only [im1]
  omega

theorem adj_ip1 {d : ℕ} (i : Fin d) (h : i.val + 1 < d) :
    (GrafoTP d).Adj i (ip1 i h) := by
  rw [grafoTP_adj]
  left
  show i.val + 1 = (ip1 i h).val
  simp [ip1]

/-- Un índice interior con margen de dos pasos a cada lado: los cinco
puntos `i−2,…,i+2` existen todos en `Fin d`. -/
def EsInteriorProfundo (d : ℕ) (i : Fin d) : Prop := 2 ≤ i.val ∧ i.val + 2 < d

/-- El Laplaciano de `f : Fin d → ℝ` en un vértice interior de `GrafoTP d`,
tomado sobre sus dos vecinos reales `im1`, `ip1` (D3). -/
def DeltaCamino {d : ℕ} (f : Fin d → ℝ) (i : Fin d) (h : EsInteriorProfundo d i) : ℝ :=
  have h1 : 2 ≤ i.val := h.1
  have h2 : i.val + 2 < d := h.2
  deltaTres (f (im1 i (by omega))) (f i) (f (ip1 i (by omega)))

/-- `Γ(f)` sobre `GrafoTP d` en un vértice interior. -/
def GammaCamino {d : ℕ} (f : Fin d → ℝ) (i : Fin d) (h : EsInteriorProfundo d i) : ℝ :=
  have h1 : 2 ≤ i.val := h.1
  have h2 : i.val + 2 < d := h.2
  gammaTres (f (im1 i (by omega))) (f i) (f (ip1 i (by omega)))

/-- `Γ₂(f)` sobre `GrafoTP d` en un vértice interior, usando los cinco
valores reales de `f` en `i−2,…,i+2`. -/
def Gamma2Camino {d : ℕ} (f : Fin d → ℝ) (i : Fin d) (h : EsInteriorProfundo d i) : ℝ :=
  have h1 : 2 ≤ i.val := h.1
  have h2 : i.val + 2 < d := h.2
  gamma2Cinco (f (im2 i (by omega))) (f (im1 i (by omega))) (f i)
    (f (ip1 i (by omega))) (f (ip2 i (by omega)))

/-- **Teorema principal.** El interior de `GrafoTP d` —el único grafo
compatible con localidad + completitud, `D3.CanalPreFuerza`— satisface
`CD(0,2)`: la curvatura de Bakry-Émery es `κ ≥ 0` con dimensión efectiva
`n = 2`, para cualquier `d` y cualquier vértice interior. -/
theorem curvatura_camino_CD02 {d : ℕ} (f : Fin d → ℝ) (i : Fin d)
    (h : EsInteriorProfundo d i) :
    (DeltaCamino f i h) ^ 2 / 2 ≤ Gamma2Camino f i h := by
  unfold DeltaCamino Gamma2Camino
  exact cd_cero_dos _ _ _ _ _

/-- Corolario: `Γ₂ ≥ 0` en todo vértice interior de cualquier `GrafoTP d`. -/
theorem gamma2Camino_nonneg {d : ℕ} (f : Fin d → ℝ) (i : Fin d)
    (h : EsInteriorProfundo d i) : 0 ≤ Gamma2Camino f i h := by
  unfold Gamma2Camino
  exact gamma2_nonneg _ _ _ _ _

/-!
**Lectura para D27.** `curvatura_camino_CD02` es la cota universal
(`κ ≥ 0`, cualquier `f`, cualquier `d`, cualquier vértice interior); junto
con `kappa_cero_no_mejorable` —que exhibe un `f` donde esa cota se satura
exactamente, `Γ₂ = 0` con `Γ > 0`— fija la curvatura de Bakry-Émery sharp del
camino en `κ = 0`. Coincide con Ollivier-Ricci, formalizado por separado en
`D28b_CurvaturaOllivier.lean` (misma conclusión, por transporte óptimo vía
Kantorovich–Rubinstein en vez de Laplaciano). Si el factor de
estiramiento `s` de `HCurv` (D27) se acoplara a esta curvatura vía
`s = 1 + g(κ)`, el resultado sobre el interior del camino es `s = 1`
siempre: no hay curvatura ahí para mover la aguja. Ese puente exigiría un
grafo distinto del camino — y D3 ya prueba que el camino es el único
compatible con localidad + completitud.
-/

#print axioms gamma2_eq_bochner
#print axioms cd_cero_dos
#print axioms gamma2_nonneg
#print axioms gamma2_eq_en_extension_afin
#print axioms n_dos_no_mejorable
#print axioms kappa_cero_no_mejorable
#print axioms adj_im1
#print axioms adj_ip1
#print axioms curvatura_camino_CD02
#print axioms gamma2Camino_nonneg

end CurvaturaBakryEmery

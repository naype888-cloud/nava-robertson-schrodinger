import NavaRobertsonIndependent.Ontology.D29_ObserverSpectralMeasurement

/-!
# D30 — Cuenta de canales bajo distinción, y registro continuo como hipótesis

Port Mathlib-only de `E09_Penrose_08_Constructor_CuentaDistincionCuatroCanales.lean`
(y de las piezas mínimas de `E09_Penrose_06_Constructor_Par_Eones_Gemelos.lean` y
`E09_Penrose_01_Libro08_Penrose_Toroidal_Conforme.lean` que hacen falta — no
la maquinaria de conmutadores de `PathGraph3D`, que no se usa aquí, ni la
apertura/germinación de `ParEonesGemelos`).

Dos partes, deliberadamente separadas, para no disfrazar una de la otra.

## Parte 1 — Teorema (0 sorry, sin postulados nuevos)

Un par `(dx,dy,dz)` con margen de distinción (`≥2` cada uno) **existente**
son tres canales. En cuanto algo se **mide** genuinamente sobre él —una
mirada al hermano, `MiradaHermano`— el canal observador está forzado a ser
distinto del medido (`observador_del_hermano_distinto`) y ningún canal
puede medirse a sí mismo (`no_auto_medida`, `D29`). Un cubo medido es de
**cuatro** canales, no de tres. No se demuestra nada nuevo
matemáticamente; se demuestra que la cuenta "3 existiendo, 4 midiendo" es
consecuencia forzada, no una elección de presentación.

## Registro continuo

La hipótesis de registro continuo ya no vive aquí. En `D34_RegistroEonAbierto`
cada campo tiene contenido matemático (fase sin cero absoluto de `D33`,
ruptura de `D13`, lecturas espectrales reales de `D29`), en lugar de
proposiciones libres. Lo que sigue en este archivo es solo la cuenta de canales.

Alcance del argumento: `observadorDelHermano dx` se **elige** (`3` si `dx = 2`, si no
`2`) y "cuatro canales" significa que existe un canal distinto del medido. La cuenta
es consecuencia de `D29` (sin auto-medición) y de esa elección; no se deriva de otra
cosa.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib.
-/

noncomputable section

open ObservadorMedicionEspectral

namespace CuentaDistincionCuatroCanales

/-! ## Parte 1 — Teorema -/

/-- El canal observador de `dx`: distinto por construcción, no por
elección (`if dx=2 then 3 else 2`, así que nunca coincide con `dx`). -/
def observadorDelHermano (dx : ℕ) : ℕ :=
  if dx = 2 then 3 else 2

theorem observador_del_hermano_distinto (dx : ℕ) (_h : 2 ≤ dx) :
    observadorDelHermano dx ≠ dx := by
  unfold observadorDelHermano
  split_ifs with h2
  · subst h2; norm_num
  · exact Ne.symm h2

theorem observador_del_hermano_ge_dos (dx : ℕ) :
    2 ≤ observadorDelHermano dx := by
  unfold observadorDelHermano
  split_ifs <;> norm_num

/-- Par mínimo: tres canales con margen de distinción, `dx,dy,dz≥2`. -/
structure Par (dx dy dz : ℕ) where
  hx : 2 ≤ dx
  hy : 2 ≤ dy
  hz : 2 ≤ dz

/-- Mirada al hermano: `dx` es el canal medido, `observadorDelHermano dx`
aporta el observador. -/
abbrev MiradaHermano (dx : ℕ) := MedicionEspectral dx (observadorDelHermano dx)

/-- La mirada al hermano siempre existe sobre un par. -/
theorem par_admite_mirada {dx dy dz : ℕ} (P : Par dx dy dz) :
    Nonempty (MiradaHermano dx) :=
  medicionEspectral_canonica dx (observadorDelHermano dx)
    P.hx (observador_del_hermano_ge_dos dx)
    (observador_del_hermano_distinto dx P.hx)
    ⟨0, Nat.lt_of_lt_of_le (by norm_num) P.hx⟩

/-- **Un cubo medido es un objeto de cuatro canales, no de tres.** El canal
observador `d' = observadorDelHermano dx` es distinto del medido, tiene
resolución `≥2`, y la medición sobre ese par es habitable. Los tres
hechos vienen de teoremas ya probados; lo nuevo es juntarlos en un solo
enunciado que hace explícita la cuenta. -/
theorem cubo_medido_es_cuatro_canales
    {dx dy dz : ℕ} (P : Par dx dy dz) :
    ∃ d' : ℕ, d' = observadorDelHermano dx ∧ d' ≠ dx ∧ 2 ≤ d' ∧
      Nonempty (MiradaHermano dx) :=
  ⟨observadorDelHermano dx, rfl, observador_del_hermano_distinto dx P.hx,
    observador_del_hermano_ge_dos dx, par_admite_mirada P⟩

/-- **Forma de cierre.** Para cualquier cubo con margen de distinción:
existe como tres canales; en cuanto algo se mide sobre él, el canal
observador forzosamente distinto lo vuelve cuatro. -/
theorem tres_existiendo_cuatro_midiendo
    (dx dy dz : ℕ) (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    Nonempty (Par dx dy dz) ∧
      (∀ _ : Par dx dy dz,
        ∃ d', d' = observadorDelHermano dx ∧ d' ≠ dx ∧ Nonempty (MiradaHermano dx)) := by
  refine ⟨⟨{ hx := hx, hy := hy, hz := hz }⟩, ?_⟩
  intro Pcubo
  obtain ⟨d', hd', hne, _, hmirada⟩ := cubo_medido_es_cuatro_canales Pcubo
  exact ⟨d', hd', hne, hmirada⟩

#print axioms observador_del_hermano_distinto
#print axioms observador_del_hermano_ge_dos
#print axioms par_admite_mirada
#print axioms cubo_medido_es_cuatro_canales
#print axioms tres_existiendo_cuatro_midiendo

end CuentaDistincionCuatroCanales

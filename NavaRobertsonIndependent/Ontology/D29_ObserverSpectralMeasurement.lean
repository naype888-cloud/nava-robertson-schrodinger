import NavaRobertsonIndependent.Mathematics.D6_Fiedler

/-!
# D29 — Observador y medición espectral (postulado, port Mathlib-only)

Port del constructor canónico
`E02_Robertson_15_Constructor_Observador_Medicion_Espectral.lean`.

## Alcance (igual que el original — no se debilita al portar)

Este módulo **no** deriva la medición cuántica de nada anterior del corpus:
la declara como **postulado nuevo**, en la firma de `MedicionEspectral`, no
escondido en prosa. Lo único que reusa, ya demostrado: el espectro real de
`A_d` (`D6_Fiedler`: `anguloModo`, `modoSeno`, `Ad_modoSeno`). No hay
"problema de la medición" resuelto aquí.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib.
-/

noncomputable section

open TransportePosicion

namespace ObservadorMedicionEspectral

/-- Un observador es un canal 1D independiente del canal medido, con su
propia resolución `d' ≥ 2`. Un solo estado (`d'=1`) no distingue nada. -/
structure Observador (d' : ℕ) where
  distincion_minima : 2 ≤ d'

theorem observador_posible (d' : ℕ) (hd' : 2 ≤ d') : Nonempty (Observador d') :=
  ⟨{ distincion_minima := hd' }⟩

/-- Medición espectral (**postulado**): un observador (`d'≥2`, distinto del
canal medido) registra un modo `k` del espectro real de `A_d`. El valor
registrado es el ángulo modal `anguloModo d k`; el autovalor de `A_d` es
`2 cos(anguloModo d k)`, ya demostrado (`Ad_modoSeno`). Lo nuevo aquí es
declarar que un canal externo lo registra — nada matemático es nuevo. -/
structure MedicionEspectral (d d' : ℕ) where
  hd : 2 ≤ d
  obs : Observador d'
  /-- El observador es un canal distinto del medido: no hay auto-medición. -/
  distinto_del_medido : d' ≠ d
  resultado : Fin d
  valorReal : ℝ
  valorReal_eq_angulo : valorReal = anguloModo d resultado
  autovalor_Ad :
    (Ad d).mulVec (modoSeno d resultado) =
      fun i => (2 * Real.cos valorReal : ℂ) * modoSeno d resultado i

theorem medicionEspectral_canonica
    (d d' : ℕ) (hd : 2 ≤ d) (hd' : 2 ≤ d') (hdist : d' ≠ d) (k : Fin d) :
    Nonempty (MedicionEspectral d d') := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  refine ⟨{
    hd := hd
    obs := { distincion_minima := hd' }
    distinto_del_medido := hdist
    resultado := k
    valorReal := anguloModo d k
    valorReal_eq_angulo := rfl
    autovalor_Ad := Ad_modoSeno hd1 k
  }⟩

/-- **No hay auto-medición.** Un canal no puede medirse a sí mismo: la
firma misma de `MedicionEspectral` (`distinto_del_medido : d'≠d`) lo
excluye cuando `d'=d`. -/
theorem no_auto_medida {d : ℕ} (M : MedicionEspectral d d) : False :=
  M.distinto_del_medido rfl

#print axioms observador_posible
#print axioms medicionEspectral_canonica
#print axioms no_auto_medida

end ObservadorMedicionEspectral

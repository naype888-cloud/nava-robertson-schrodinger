import NavaRobertsonIndependent.Mathematics.D16_ClosedSurfaceTransport

/-!
# D16b — Puente Gauss–Bonnet: el defect transportado fija la curvatura total

`D16` transporta el defect por el primer número de Betti: `Ω(Σ_g) = b₁ · δ_∞` con
`b₁ = 2g`. La característica de Euler de la misma superficie es
`χ = b₀ − b₁ + b₂ = 2 − 2g`, y Gauss–Bonnet da la curvatura total `∫K dA = 2πχ`.
Las dos magnitudes dependen solo de `b₁`; al eliminarlo:

* `∫K dA = 4π − (2π/δ_∞) · Ω(Σ_g)` (`curvaturaTotal_desde_defect`);
* en 2D la integral de la curvatura escalar es `∫R dA = 2∫K dA` (convención `R = 2K`),
  así que `∫R dA = 8π − (4π/δ_∞) · Ω(Σ_g)` (`integralEscalar_desde_defect`).

Es una **relación afín global**, no una suma: el defect y la curvatura miden la misma
topología (`b₁`) en unidades distintas. Sumarlos contaría `b₁` dos veces. Tampoco es
local: `D28` y `D28b` prueban que el interior del camino tiene curvatura `0`; la
curvatura vive en los ciclos no contraíbles.

## Hipótesis declarada

* `HGaussBonnet`: la curvatura total de `Σ_g` es `2πχ(Σ_g)`. Mathlib no tiene
  Gauss–Bonnet (ni la versión suave ni la discreta de Descartes); se declara y se
  prueba satisfacible.
* Se heredan las entradas de `D16`: cada ciclo esencial carga `δ_∞`, y `b₁(Σ_g) = 2g`.

## Casos

* Esfera (`g = 0`): curvatura total `4π`, defect `0` (no hay ciclos).
* Toro (`g = 1`): curvatura total `0` y defect `2δ_∞ > 0` (`toro`): plano en
  promedio y con defect positivo.
* Más género, más defect y menos curvatura (`mas_genero`); el defect determina el
  género (`defect_determina_genero`).

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

open Real

namespace Gnomon

/-- Característica de Euler de la superficie orientable cerrada de género `g`,
`χ = b₀ − b₁ + b₂` con `b₀ = b₂ = 1` y `b₁ = 2g`. -/
def caracteristicaEuler (g : ℕ) : ℝ := 1 - ((2 * g : ℕ) : ℝ) + 1

theorem caracteristicaEuler_eq (g : ℕ) : caracteristicaEuler g = 2 - 2 * g := by
  unfold caracteristicaEuler; push_cast; ring

/-- **H-GAUSS-BONNET (hipótesis declarada).** La curvatura total de `Σ_g` es `2πχ`. -/
structure HGaussBonnet where
  curvaturaTotal : ℕ → ℝ
  gauss_bonnet : ∀ g, curvaturaTotal g = 2 * π * caracteristicaEuler g

theorem hGaussBonnet_satisfacible : Nonempty HGaussBonnet :=
  ⟨⟨fun g => 2 * π * caracteristicaEuler g, fun _ => rfl⟩⟩

namespace HGaussBonnet

variable (H : HGaussBonnet)

/-- Integral de la curvatura escalar en 2D: `∫R dA = 2∫K dA`. -/
def integralEscalar (g : ℕ) : ℝ := 2 * H.curvaturaTotal g

/-- **Puente**: la curvatura total es función afín del defect transportado. -/
theorem curvaturaTotal_desde_defect (g : ℕ) :
    H.curvaturaTotal g = 4 * π - (2 * π / deltaInf) * closedSurfaceDefect g := by
  rw [H.gauss_bonnet, caracteristicaEuler_eq, closedSurfaceDefect_eq_two_mul_genus_mul]
  field_simp [deltaInf_pos.ne']
  ring

/-- **Puente, forma escalar**: `∫R dA = 8π − (4π/δ_∞) · Ω(Σ_g)`. -/
theorem integralEscalar_desde_defect (g : ℕ) :
    H.integralEscalar g = 8 * π - (4 * π / deltaInf) * closedSurfaceDefect g := by
  unfold integralEscalar
  rw [H.curvaturaTotal_desde_defect]
  ring

/-- Esfera: curvatura `4π`, defect `0`. -/
theorem esfera : H.curvaturaTotal 0 = 4 * π ∧ closedSurfaceDefect 0 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [H.gauss_bonnet, caracteristicaEuler_eq]; ring
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul]; simp

/-- Toro: curvatura total `0` con defect `2δ_∞ > 0`. -/
theorem toro :
    H.curvaturaTotal 1 = 0 ∧ closedSurfaceDefect 1 = 2 * deltaInf ∧
      0 < closedSurfaceDefect 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [H.gauss_bonnet, caracteristicaEuler_eq]; ring
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul]; ring
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul]; push_cast; linarith [deltaInf_pos]

/-- Más género: más defect y menos curvatura total. -/
theorem mas_genero {g₁ g₂ : ℕ} (h : g₁ < g₂) :
    closedSurfaceDefect g₁ < closedSurfaceDefect g₂ ∧
      H.curvaturaTotal g₂ < H.curvaturaTotal g₁ := by
  have hg : (g₁ : ℝ) < g₂ := by exact_mod_cast h
  have hd := deltaInf_pos
  have hp := pi_pos
  refine ⟨?_, ?_⟩
  · rw [closedSurfaceDefect_eq_two_mul_genus_mul, closedSurfaceDefect_eq_two_mul_genus_mul]
    nlinarith
  · rw [H.gauss_bonnet, H.gauss_bonnet, caracteristicaEuler_eq, caracteristicaEuler_eq]
    nlinarith

end HGaussBonnet

/-- El defect transportado determina el género (y por tanto `b₁` y `χ`). -/
theorem defect_determina_genero {g₁ g₂ : ℕ}
    (h : closedSurfaceDefect g₁ = closedSurfaceDefect g₂) : g₁ = g₂ := by
  rw [closedSurfaceDefect_eq_two_mul_genus_mul, closedSurfaceDefect_eq_two_mul_genus_mul] at h
  have hd := deltaInf_pos.ne'
  have : (g₁ : ℝ) = g₂ := by
    have h2 : 2 * deltaInf * ((g₁ : ℝ) - g₂) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso; exact hd (by linarith)
    · linarith
  exact_mod_cast this

#print axioms HGaussBonnet.integralEscalar_desde_defect
#print axioms defect_determina_genero

end Gnomon

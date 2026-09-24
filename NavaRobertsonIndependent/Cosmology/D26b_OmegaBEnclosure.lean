import NavaRobertsonIndependent.Cosmology.D26_MirrorBaryogenesis
import NavaRobertsonIndependent.Physics.SubPlanckianLimit

/-!
# D26b — Encierro racional de `Ω_b` (lectura cosmológica)

Cierra el hueco que `D26_BaryogenesisEspejo.lean` dejó como trabajo futuro: el
acuerdo decimal de `g_s·e^{-1/C∞}` (`omegaBar`) con el `Ω_b` documentado
(`0.049543679`). La matemática vive en la Capa 1 (`D26a_OmegaDesdePi`, solo `π`);
aquí se identifica `omegaBar` de `D26` con `omegaPi` de `D26a` y se transporta el
encierro.

## Margen logrado

La distancia queda **encerrada por los dos lados**, certificado en Lean:

    1.11×10⁻¹⁰ < Ω_b − omegaBar < 1.12×10⁻¹⁰

(`omegaBar_distancia_gt`, `omegaBar_encierro`): `omegaBar` está *por debajo* del
decimal documentado, a `≈ 2.26×10⁻⁹` relativo. El decimal `0.049543679` es el
redondeo a 9 cifras de `omegaBar = 0.04954367888809…`.

Qué certifica y qué no: prueba que el decimal documentado **es** la fórmula de `π`
redondeada (coherencia interna del marco). La comparación con un `Ω_b` observado no
está en este paquete.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

open BaryogenesisEspejo

namespace EncierroOmegaB

/-- `omegaBar` (`D26`) es `omegaPi` (`D26a`): la misma función de `π`. -/
theorem omegaBar_eq_omegaPi : omegaBar = OmegaDesdePi.omegaPi := rfl

/-- **Encierro racional de `Ω_b`**: margen `< 1.12×10⁻¹⁰` absoluto
(`< 2.3×10⁻⁹` relativo). -/
theorem omegaBar_encierro :
    |LimiteSubPlanckiano.Omega_b - omegaBar| < 112 * 10 ^ (-12 : ℤ) := by
  obtain ⟨h1, h2⟩ := LimiteSubPlanckiano.Omega_b_desde_pi
  rw [omegaBar_eq_omegaPi, abs_lt]
  constructor
  · have : (0 : ℝ) < 111 * 10 ^ (-12 : ℤ) := by positivity
    linarith
  · exact h2

/-- Cota inferior: `omegaBar` queda por debajo de `Ω_b` en más de `1.11×10⁻¹⁰`, así
que el margen no se puede bajar sin cambiar el decimal documentado. -/
theorem omegaBar_distancia_gt :
    111 * 10 ^ (-12 : ℤ) < LimiteSubPlanckiano.Omega_b - omegaBar := by
  rw [omegaBar_eq_omegaPi]; exact LimiteSubPlanckiano.Omega_b_desde_pi.1

#print axioms omegaBar_encierro
#print axioms omegaBar_distancia_gt

end EncierroOmegaB

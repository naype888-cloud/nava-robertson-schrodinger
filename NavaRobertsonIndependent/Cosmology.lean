import NavaRobertsonIndependent.Cosmology.D26_MirrorBaryogenesis
import NavaRobertsonIndependent.Cosmology.D26b_OmegaBEnclosure

/-!
# Layer 3 — Cosmology

A cosmological reading built on Layers 1 and 2. It is kept in its own layer so
that it never enters the import closure of the mathematics (Layer 1) or of the
physics (Layer 2); both boundaries are checked in `Verification/`.

* `D26_BaryogenesisEspejo`: over Mathlib only. The mirror symmetry of the
  path-graph spectrum (`espejo_espectral`), the Szegő constant
  `C∞ = √(π²/3 − 2)`, `g_s = 1 − 1/C∞`, the factor `e^{−1/C∞}`, and the strict
  inequalities `0 < g_s·e^{−1/C∞} < g_s` (`cadena_baryogenesis`). The
  baryogenesis vocabulary is the reading; the theorems are these inequalities.
* `D26b_EncierroOmegaB`: a certified rational enclosure,
  `1.11×10⁻¹⁰ < Ω_b − g_s·e^{−1/C∞} < 1.12×10⁻¹⁰` (`omegaBar_distancia_gt`,
  `omegaBar_encierro`), where `Ω_b` is the
  documented decimal of Layer 2. The mathematics is in Layer 1 (`D26a_OmegaDesdePi`,
  π only); `omegaBar = omegaPi` holds by definition (`omegaBar_eq_omegaPi`). It
  certifies internal coherence (the decimal is the formula rounded); a comparison
  with an observed `Ω_b` is not in this package. It proves the numerical coincidence; that
  `Ω_b` *is* `g_s·e^{−1/C∞}` physically is the claim of this layer, not a
  consequence of Layers 1–2.
-/

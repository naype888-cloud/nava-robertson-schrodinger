import NavaRobertsonIndependent.Physics.SubPlanckianLimit

/-!
# Schwarzschild collapse anchored to SI constants

Mathlib-only port of the canonical constructor
`E10_Cierre_06_Constructor_Colapso_Schwarzschild_Physlib.lean`. The canonical file
took `c` and `ℏ` from Physlib (`DimSpeed.speedOfLight`, `Constants.ℏ`); here they
are fixed as self-contained SI constants:

* `c = 299792458` exact by SI definition;
* `h = 6.62607015e-34 J·s` exact by SI definition (post-2019), and `ℏ = h / (2π)`
  in the community convention of the corpus.

The gravitational constant `G` is not fixed: it enters as a positive parameter of
the certificate. The Planck length is not redefined: the accepted community
hypothesis `l_P² = ℏ·G/c³` (`RelacionPlanckNewton`) is required.

Under those external conditions the framework supplies its own factor `lsubCanal`
and the result is exactly

```
E_grav = (1 / 2) * lsubCanal * E_P,    with E_P = ℏ * c / l_P.
```

No additional dynamical mechanism is postulated: the Schwarzschild identity
`r = 2GM/c²` is used as an algebraic predicate.
-/

noncomputable section

open LimiteSubPlanckiano

namespace ColapsoSchwarzschild

/-- Speed of light in SI. -/
def cSI : ℝ :=
  299792458

theorem cSI_pos : 0 < cSI := by
  norm_num [cSI]

/-- Planck constant `h` in SI, exact by definition (post-2019):
`6.62607015e-34 J·s`. -/
def hSI : ℝ :=
  (662607015 : ℝ) / 10 ^ 42

theorem hSI_pos : 0 < hSI := by
  norm_num [hSI]

/-- Reduced Planck constant in the community convention used by the corpus:
`ℏ = h / (2π)`. -/
noncomputable def hbarSI : ℝ :=
  hSI / (2 * Real.pi)

theorem hbarSI_pos : 0 < hbarSI := by
  unfold hbarSI
  exact div_pos hSI_pos (mul_pos (by norm_num) Real.pi_pos)

/-- Planck energy in the community convention used here: `E_P = ℏ c / l_P`. -/
def energiaPlanck (lP : ℝ) : ℝ :=
  hbarSI * cSI / lP

/-- Externally accepted Planck relation for the pair `(G, lP)`. Equivalent to
`l_P = √(ℏ G / c³)`, but avoids introducing a new square root. -/
def RelacionPlanckNewton (G lP : ℝ) : Prop :=
  lP ^ 2 = hbarSI * G / cSI ^ 3

/-- Mass whose Schwarzschild radius is `r`. -/
def masaSchwarzschild (G r : ℝ) : ℝ :=
  r * cSI ^ 2 / (2 * G)

/-- Community predicate: `r = 2GM/c²`. -/
def RadioSchwarzschild (G M r : ℝ) : Prop :=
  r = 2 * G * M / cSI ^ 2

/-- The mass defined by inversion really satisfies the Schwarzschild relation,
under `G > 0`. -/
theorem masaSchwarzschild_certifica_radio {G r : ℝ} (hG : 0 < G) :
    RadioSchwarzschild G (masaSchwarzschild G r) r := by
  unfold RadioSchwarzschild masaSchwarzschild
  field_simp [ne_of_gt hG, ne_of_gt cSI_pos]

/-- Energy associated with the mass of Schwarzschild radius `r`. -/
def energiaSchwarzschild (G r : ℝ) : ℝ :=
  masaSchwarzschild G r * cSI ^ 2

/-- Gravitational datum of the paper: radius fixed by the sub-Planckian side. -/
def energiaColapsoSbpk (G : ℝ) : ℝ :=
  energiaSchwarzschild G Lsbpk

/-- The usual form `c⁴ r/(2G)` is recovered from the definition by mass. -/
theorem energiaSchwarzschild_eq_cuatro {G r : ℝ} :
    energiaSchwarzschild G r = cSI ^ 4 * r / (2 * G) := by
  unfold energiaSchwarzschild masaSchwarzschild
  ring

/-- **Central theorem**: if `lP` and `G` satisfy the accepted Planck relation, the
gravitational energy associated with `Lsbpk = lsubCanal * lP` is exactly
`(1/2) * lsubCanal * E_P`. -/
theorem energiaColapsoSbpk_eq_half_lsub_EPlanck
    {G lP : ℝ} (hG : 0 < G) (hlP : 0 < lP)
    (hPlanck : RelacionPlanckNewton G lP)
    (hL : Lsbpk = lsubCanal * lP) :
    energiaSchwarzschild G Lsbpk =
      (1 / 2) * lsubCanal * energiaPlanck lP := by
  unfold RelacionPlanckNewton at hPlanck
  rw [energiaSchwarzschild_eq_cuatro, hL]
  have hGnz : G ≠ 0 := ne_of_gt hG
  have hlPnz : lP ≠ 0 := ne_of_gt hlP
  have hcnz : cSI ≠ 0 := ne_of_gt cSI_pos
  have hPlanck_mul : lP ^ 2 * cSI ^ 3 = hbarSI * G := by
    field_simp [hcnz] at hPlanck
    exact hPlanck
  have hEPlanck : energiaPlanck lP = lP * cSI ^ 4 / G := by
    unfold energiaPlanck
    have hhbar : hbarSI = lP ^ 2 * cSI ^ 3 / G := by
      field_simp [hGnz]
      linarith [hPlanck_mul]
    rw [hhbar]
    field_simp [hGnz, hlPnz]
  rw [hEPlanck]
  field_simp [hGnz]

/-- Specialization to the CODATA anchor used by the sub-Planckian module. The
hypothesis `RelacionPlanckNewton` stays visible because `G` is not fixed in the
framework. -/
theorem energiaColapsoCODATA_eq_half_lsub_EPlanck
    {G : ℝ} (hG : 0 < G)
    (hPlanck : RelacionPlanckNewton G longitudPlanckCODATA) :
    energiaColapsoSbpk G =
      (1 / 2) * lsubCanal * energiaPlanck longitudPlanckCODATA := by
  unfold energiaColapsoSbpk
  exact energiaColapsoSbpk_eq_half_lsub_EPlanck hG longitudPlanckCODATA_pos
    hPlanck rfl

/-- The hypothesis `RelacionPlanckNewton` is satisfiable with the CODATA anchor: the
`G` that satisfies it is `l_P²·c³/ℏ` (numerically `6.67430e-11 m³ kg⁻¹ s⁻²`, the
CODATA value). The gravitational theorems are not vacuous. -/
theorem relacionPlanckNewton_satisfacible :
    ∃ G : ℝ, 0 < G ∧ RelacionPlanckNewton G longitudPlanckCODATA := by
  refine ⟨longitudPlanckCODATA ^ 2 * cSI ^ 3 / hbarSI,
    div_pos (mul_pos (pow_pos longitudPlanckCODATA_pos 2) (pow_pos cSI_pos 3)) hbarSI_pos, ?_⟩
  unfold RelacionPlanckNewton
  field_simp [hbarSI_pos.ne', cSI_pos.ne']

structure CertificadoColapsoSchwarzschild where
  c_exacta_SI : cSI = 299792458
  hbar_positivo : 0 < hbarSI
  radio_por_masa : ∀ {G r : ℝ}, 0 < G →
    RadioSchwarzschild G (masaSchwarzschild G r) r
  energia_forma_cuatro : ∀ {G r : ℝ},
    energiaSchwarzschild G r = cSI ^ 4 * r / (2 * G)
  colapso_subplanckiano : ∀ {G : ℝ}, 0 < G →
    RelacionPlanckNewton G longitudPlanckCODATA →
    energiaColapsoSbpk G =
      (1 / 2) * lsubCanal * energiaPlanck longitudPlanckCODATA

theorem certificado_colapso_schwarzschild_OK :
    Nonempty CertificadoColapsoSchwarzschild :=
  ⟨{
    c_exacta_SI := rfl
    hbar_positivo := hbarSI_pos
    radio_por_masa := fun hG => masaSchwarzschild_certifica_radio hG
    energia_forma_cuatro := fun {_ _} => energiaSchwarzschild_eq_cuatro
    colapso_subplanckiano := fun hG hPlanck =>
      energiaColapsoCODATA_eq_half_lsub_EPlanck hG hPlanck
  }⟩

end ColapsoSchwarzschild

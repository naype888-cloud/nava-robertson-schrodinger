/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonCertificados.Poincare1911_QuantumNecessity
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Poincaré 1912 — Planck's law forces discrete energy levels

Poincaré's theorem in its full strength. Let `μ` be any weight on energies (a density of
states, possibly infinite, possibly continuous) whose Boltzmann factors `e^{−βE}` are
integrable for every `β > 0`. If the Gibbs mean energy of `μ` is Planck's
`ε / (e^{βε} − 1)` at every temperature, then `μ` is a multiple of the level measure
`∑ₙ δ_{nε}`. No continuous component survives: the quantum is necessary.

The mean-energy law makes `Z(β) (1 − e^{−βε})` constant, so the partition function of `μ` is
that of the levels. Laplace transforms on `β > 0` separate such weights: after tilting by
`e^{−E}` both measures are finite, their complex moment generating functions agree on the
half-plane `Re z < 1` by analytic continuation, hence so do their characteristic functions.

## Main results

- `Poincare1912.eq_of_laplace` : the Laplace transform on `β > 0` determines the weight.
- `Poincare1912.partition_eq_of_planck` : the Planck mean energy fixes `Z(β)` up to a scalar.
- `Poincare1912.planck_forces_levels` : Planck's law forces `μ = c • ∑ₙ δ_{nε}`.
- `Poincare1912.no_density_planck` : no weight `w(E) dE` reproduces Planck's law.
-/

@[expose] public noncomputable section

namespace Poincare1912

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal

variable {μ ν : Measure ℝ} {ε : ℝ}

/-- The weight `μ` has a Laplace transform on `β > 0`. -/
def HasLaplace (μ : Measure ℝ) : Prop := ∀ β > 0, Integrable (fun E => exp (-β * E)) μ

/-- The quantized levels: unit mass at every `nε`. -/
def levels (ε : ℝ) : Measure ℝ := Measure.sum fun n : ℕ => Measure.dirac ((n : ℝ) * ε)

/-- The tilt `e^{−E} · μ`. -/
def tilt (μ : Measure ℝ) : Measure ℝ := μ.withDensity fun E => ((exp (-E)).toNNReal : ℝ≥0∞)

/-! ## 1. Tilting -/

theorem measurable_tilt_density : Measurable fun E : ℝ => (exp (-E)).toNNReal := by
  fun_prop

theorem tilt_smul (t E : ℝ) : (exp (-E)).toNNReal • exp (t * E) = exp (-(1 - t) * E) := by
  rw [NNReal.smul_def, Real.coe_toNNReal _ (exp_pos _).le, smul_eq_mul, ← exp_add]
  ring_nf

theorem integrable_tilt (hμ : HasLaplace μ) {t : ℝ} (ht : t < 1) :
    Integrable (fun E => exp (t * id E)) (tilt μ) := by
  rw [tilt, integrable_withDensity_iff_integrable_smul measurable_tilt_density]
  simpa only [id, tilt_smul] using hμ _ (by linarith)

theorem mgf_tilt (t : ℝ) : mgf id (tilt μ) t = ∫ E, exp (-(1 - t) * E) ∂μ := by
  rw [mgf, tilt, integral_withDensity_eq_integral_smul measurable_tilt_density]
  simp only [id, tilt_smul]

theorem isFiniteMeasure_tilt (hμ : HasLaplace μ) : IsFiniteMeasure (tilt μ) := by
  have h := (hμ 1 one_pos).hasFiniteIntegral
  simp only [neg_mul, one_mul] at h
  exact isFiniteMeasure_withDensity_ofReal h

theorem withDensity_tilt (μ : Measure ℝ) :
    (tilt μ).withDensity (fun E => ((exp E).toNNReal : ℝ≥0∞)) = μ := by
  have h : ((fun E : ℝ => ((exp (-E)).toNNReal : ℝ≥0∞)) * fun E => ((exp E).toNNReal : ℝ≥0∞))
      = 1 := by
    funext E
    simp [← ENNReal.coe_mul, ← Real.toNNReal_mul (exp_pos _).le, ← exp_add]
  rw [tilt, ← withDensity_mul _ (by fun_prop) (by fun_prop), h, withDensity_one]

/-! ## 2. The Laplace transform on `β > 0` determines the weight -/

theorem half_plane_subset (hμ : HasLaplace μ) :
    {z : ℂ | z.re < 1} ⊆ {z | z.re ∈ interior (integrableExpSet id (tilt μ))} :=
  fun _ hz => interior_maximal (fun _ ht => integrable_tilt hμ ht) isOpen_Iio hz

theorem tendsto_neg_inv : Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop
    (𝓝[≠] 0) := by
  have h : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
  · simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h
  · simpa using Nat.cast_add_one_ne_zero (R := ℂ) n

/-- **Uniqueness of the Laplace transform.** Two weights with the same Laplace transform on
`β > 0` coincide. -/
theorem eq_of_laplace (hμ : HasLaplace μ) (hν : HasLaplace ν)
    (h : ∀ β > 0, ∫ E, exp (-β * E) ∂μ = ∫ E, exp (-β * E) ∂ν) : μ = ν := by
  have := isFiniteMeasure_tilt hμ
  have := isFiniteMeasure_tilt hν
  have hreal (t : ℝ) (ht : t < 1) : complexMGF id (tilt μ) t = complexMGF id (tilt ν) t := by
    rw [complexMGF_ofReal, complexMGF_ofReal, mgf_tilt, mgf_tilt, h _ (by linarith)]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id (tilt μ) z = complexMGF id (tilt ν) z :=
    tendsto_neg_inv.frequently <| Frequently.of_forall fun n => hreal _ <| by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_complexMGF.mono (half_plane_subset hμ))
    (analyticOnNhd_complexMGF.mono (half_plane_subset hν))
    (convex_halfSpace_re_lt 1).isPreconnected (by simp) hfreq
  have ht : tilt μ = tilt ν := Measure.ext_of_charFun <| funext fun t => by
    rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
    exact heq (by simp)
  rw [← withDensity_tilt μ, ← withDensity_tilt ν, ht]

/-! ## 3. The quantized levels -/

theorem one_sub_exp_pos {β : ℝ} (hβ : 0 < β) (hε : 0 < ε) : 0 < 1 - exp (-(β * ε)) :=
  sub_pos.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hβ hε)))

theorem lintegral_levels (hε : 0 < ε) {β : ℝ} (hβ : 0 < β) :
    ∫⁻ E, ENNReal.ofReal (exp (-β * E)) ∂levels ε = ENNReal.ofReal (1 - exp (-(β * ε)))⁻¹ := by
  have hs : Summable fun n : ℕ => exp (-β * (n * ε)) := by
    refine (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr (mul_pos hβ hε))).congr fun n => ?_
    ring_nf
  rw [levels, lintegral_sum_measure]
  simp only [lintegral_dirac]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (exp_pos _).le) hs,
    ← Poincare1911.quantum_partition hβ hε]
  simp only [mul_assoc]

theorem hasLaplace_levels (hε : 0 < ε) : HasLaplace (levels ε) := fun β hβ =>
  ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (exp_pos _).le)).mpr
    (by rw [lintegral_levels hε hβ]; exact ENNReal.ofReal_lt_top)⟩

theorem integral_levels (hε : 0 < ε) {β : ℝ} (hβ : 0 < β) :
    ∫ E, exp (-β * E) ∂levels ε = (1 - exp (-(β * ε)))⁻¹ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (exp_pos _).le)
    (by fun_prop), lintegral_levels hε hβ,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (one_sub_exp_pos hβ hε).le)]

/-! ## 4. Planck's mean energy fixes the partition function -/

theorem hasDerivAt_partition (hμ : HasLaplace μ) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun b => ∫ E, exp (-b * E) ∂μ) (-∫ E, E * exp (-β * E) ∂μ) β := by
  have hsub : Set.Iio (0 : ℝ) ⊆ integrableExpSet id μ := fun t (ht : t < 0) => by
    simpa [integrableExpSet] using hμ (-t) (by linarith)
  have hint := interior_maximal hsub isOpen_Iio (neg_lt_zero.mpr hβ)
  simpa [mgf, Function.comp_def] using (hasDerivAt_mgf hint).comp β (hasDerivAt_neg β)

/-- **Planck's mean energy fixes `Z(β)`**: `Z(β) (1 − e^{−βε})` is constant on `β > 0`. -/
theorem partition_eq_of_planck (hε : 0 < ε) (hμ : HasLaplace μ)
    (hU : ∀ β > 0, (∫ E, E * exp (-β * E) ∂μ) / (∫ E, exp (-β * E) ∂μ)
      = ε / (exp (β * ε) - 1)) :
    ∃ c, ∀ β > 0, ∫ E, exp (-β * E) ∂μ = c * (1 - exp (-(β * ε)))⁻¹ := by
  have hd {β : ℝ} (hβ : 0 < β) : exp (β * ε) - 1 ≠ 0 :=
    (sub_pos.mpr (one_lt_exp_iff.mpr (mul_pos hβ hε))).ne'
  have hZ {β : ℝ} (hβ : 0 < β) : ∫ E, exp (-β * E) ∂μ ≠ 0 := fun h0 => by
    have := hU β hβ
    rw [h0, div_zero] at this
    exact (div_pos hε (sub_pos.mpr (one_lt_exp_iff.mpr (mul_pos hβ hε)))).ne this
  have hf {β : ℝ} (hβ : 0 < β) :
      HasDerivAt (fun b => (∫ E, exp (-b * E) ∂μ) * (1 - exp (-(b * ε)))) 0 β := by
    convert (hasDerivAt_partition hμ hβ).mul
      (((hasDerivAt_id β).mul_const ε).neg.exp.const_sub 1) using 1
    · rfl
    rw [← div_mul_cancel₀ (∫ E, E * exp (-β * E) ∂μ) (hZ hβ), hU β hβ]
    simp only [Pi.neg_apply, id, exp_neg]
    have hx := hd hβ
    have hx0 := (exp_pos (β * ε)).ne'
    generalize exp (β * ε) = x at hx hx0 ⊢
    field_simp
    ring
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun b hb => (hf hb).differentiableAt.differentiableWithinAt) (fun b hb => (hf hb).deriv)
  exact ⟨c, fun β hβ => by
    rw [← hc β hβ, mul_inv_cancel_right₀ (one_sub_exp_pos hβ hε).ne']⟩

/-! ## 5. The theorem -/

/-- **Poincaré (1912): Planck's law forces the quantum.** A weight whose Gibbs mean energy is
Planck's `ε / (e^{βε} − 1)` at every `β > 0` is a positive multiple of `∑ₙ δ_{nε}`. -/
theorem planck_forces_levels (hε : 0 < ε) (hμ : HasLaplace μ)
    (hU : ∀ β > 0, (∫ E, E * exp (-β * E) ∂μ) / (∫ E, exp (-β * E) ∂μ)
      = ε / (exp (β * ε) - 1)) :
    ∃ c : ℝ≥0, 0 < c ∧ μ = (c : ℝ≥0∞) • levels ε := by
  obtain ⟨c, hc⟩ := partition_eq_of_planck hε hμ hU
  have hq := one_sub_exp_pos one_pos hε
  have hZ1 : 0 ≤ ∫ E, exp (-1 * E) ∂μ := integral_nonneg fun _ => (exp_pos _).le
  have hc0 : 0 ≤ c := by
    have := hc 1 one_pos
    rw [this] at hZ1
    exact nonneg_of_mul_nonneg_left hZ1 (inv_pos.mpr hq)
  refine ⟨c.toNNReal, ?_, eq_of_laplace hμ
    (fun β hβ => (hasLaplace_levels hε β hβ).smul_measure ENNReal.coe_ne_top) fun β hβ => ?_⟩
  · refine Real.toNNReal_pos.mpr (lt_of_le_of_ne hc0 fun h => ?_)
    have := hU 1 one_pos
    rw [hc 1 one_pos, ← h, zero_mul, div_zero] at this
    exact (div_pos hε (sub_pos.mpr (one_lt_exp_iff.mpr (by simpa using hε)))).ne this
  · rw [integral_smul_measure, integral_levels hε hβ, hc β hβ]
    simp [Real.coe_toNNReal _ hc0]

/-- **No continuous weight reproduces Planck's law**: a density `w(E) dE` has no atoms, while
Planck's law forces an atom at `E = 0`. -/
theorem no_density_planck (hε : 0 < ε) (w : ℝ → ℝ≥0∞) (hμ : HasLaplace (volume.withDensity w)) :
    ¬ ∀ β > 0, (∫ E, E * exp (-β * E) ∂volume.withDensity w)
        / (∫ E, exp (-β * E) ∂volume.withDensity w) = ε / (exp (β * ε) - 1) := fun hU => by
  obtain ⟨c, hc0, hc⟩ := planck_forces_levels hε hμ hU
  have h0 : volume.withDensity w {0} = 0 :=
    withDensity_absolutelyContinuous _ _ Real.volume_singleton
  have h1 : 1 ≤ levels ε {0} := by
    rw [levels, Measure.sum_apply _ (measurableSet_singleton 0)]
    exact le_trans (by simp) (ENNReal.le_tsum 0)
  rw [hc, Measure.smul_apply, smul_eq_mul] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hc0.ne' (by exact_mod_cast h)
  · simp [h] at h1

end Poincare1912

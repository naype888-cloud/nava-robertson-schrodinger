import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# D37b — The NRS angle: the algebraic quantum as an angle

Robertson–Schrödinger is Cauchy–Schwarz for the two fluctuation vectors
`x = (T − ⟨T⟩)ψ` and `y = (P − ⟨P⟩)ψ` (`D1`, `D23`): it saturates exactly when they are
parallel, and the Gram defect is what their angle leaves over. This file measures that angle
at the maximal-tension state `ψ*`:

  `cos θ_NRS(d) = |⟨x, y⟩| / (‖x‖ ‖y‖) = 1 / C_Nava(d)`   (`cos_anguloNRS`).

* `θ_NRS(d) = 0` exactly for `d = 2, 3` (`anguloNRS_eq_zero_iff`);
* `θ_NRS(d) > 0` for every `d ≥ 4` (`anguloNRS_pos`): the algebraic quantum is an opening
  between "where" and "how it moves" that no axis with `4` or more sites can close;
* it grows strictly with `d` from `4` on (`anguloNRS_strictMonoOn`) and stays strictly below
  `arccos (1 / C_∞)`, `C_∞ = √(π²/3 − 2)` (`anguloNRS_lt_limite`), a bound no `d` attains.

On the cube of `D37` each axis carries its own angle, `θ_NRS(dx)`, `θ_NRS(dy)`, `θ_NRS(dz)`
(`anguloG_eje_x/y/z`).

**Universal angular floor** (`piso_angular`): for every `d ≥ 4`,
`θ_NRS(4) ≤ θ_NRS(d) < arccos (1 / C_∞)`, with the exact value
`θ_NRS(4) = arccos (1 / √((99 − 42√5)/5)) ≈ 7.43°` (`anguloNRS_cuatro`) and `θ_NRS(4) > 0`.
No axis with `4` or more sites, however many, brings its two fluctuation vectors closer than
`θ_NRS(4)`; on the cube this holds on all three axes at once (`piso_angular_cubo`).

**Finite isotropy** (`anguloNRS_isotropia`, `isotropia_finita_cubo`): two rows, or two axes
of the cube, with at least `D ≥ 4` sites each have angles differing by less than
`arccos (1 / C_∞) − θ_NRS(D)`. No infinite lattice is involved: only finite rows and the
unattained ceiling.
-/

noncomputable section

open Real TransportePosicion NavaRobertsonSchrodingerEDUI ConstructorEspectralTP Gnomon
open PathGraph3DNRS SaturacionAutovectores

namespace AnguloNRS

/-! ## 1. The angle between two fluctuation vectors -/

/-- Angle between the fluctuation vectors of `L` and `M` at `Ψ`, on any finite site set. -/
def anguloG {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  arccos (‖inner ℂ (centradoG L Ψ) (centradoG M Ψ)‖ / (‖centradoG L Ψ‖ * ‖centradoG M Ψ‖))

/-- The NRS angle of `(T_d, P_d)` at `ψ*`. -/
def anguloNRS (d : ℕ) : ℝ := anguloG (TdOp d) (PdOp d) (psiStar d)

theorem CoherenceConstant_ge_one {d : ℕ} (hd : 2 ≤ d) : 1 ≤ CoherenceConstant d := by
  rw [CoherenceConstant_eq_one_add_geometricGap]
  linarith [geometricGap_nonneg hd]

/-- **The NRS angle.** `cos θ_NRS(d) = 1 / C_Nava(d)`. -/
theorem cos_anguloNRS {d : ℕ} (hd : 2 ≤ d) :
    ‖inner ℂ (centrado (TdOp d) (psiStar d)) (centrado (PdOp d) (psiStar d))‖ /
        (‖centrado (TdOp d) (psiStar d)‖ * ‖centrado (PdOp d) (psiStar d)‖) =
      1 / CoherenceConstant d := by
  set a := ‖inner ℂ (centrado (TdOp d) (psiStar d)) (centrado (PdOp d) (psiStar d))‖
  set b := ‖centrado (TdOp d) (psiStar d)‖ * ‖centrado (PdOp d) (psiStar d)‖
  set k := (commutatorConstant d / 2) ^ 2
  have hC := CoherenceConstant_ge_one hd
  have hk : 0 < k := commutatorConstant_half_sq_pos hd
  -- `a² = k`: the Gram defect with `cov = 0` and tension `2/(d−1)`.
  have ha : a ^ 2 = k := by
    have h := SobranteIntermedio.sobrante_eq d (psiStar d)
    rw [SobranteIntermedio.sobrante, defectGramEn, covarianza_cero hd,
      SobranteIntermedio.tension_psiStar hd] at h
    have hk' : k = 1 / ((d : ℝ) - 1) ^ 2 := commutatorConstant_half_sq hd
    have hd1 : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [hk']
    field_simp at h ⊢
    linarith
  -- `b² = k · C²`: `producto_varianzas`.
  have hb : b ^ 2 = (a * CoherenceConstant d) ^ 2 := by
    have h := producto_varianzas hd
    rw [varianza, varianza, ← CoherenceConstant_eq_one_add_geometricGap] at h
    rw [mul_pow, h, mul_pow, ha]
  have ha0 : 0 < a := by
    have : a = Real.sqrt k := by rw [← ha, Real.sqrt_sq (norm_nonneg _)]
    rw [this]; exact Real.sqrt_pos.mpr hk
  have hbeq : b = a * CoherenceConstant d :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hb
  rw [hbeq]
  field_simp

theorem anguloNRS_eq {d : ℕ} (hd : 2 ≤ d) : anguloNRS d = arccos (1 / CoherenceConstant d) := by
  rw [anguloNRS, anguloG]
  exact congrArg arccos (cos_anguloNRS hd)

/-! ## 2. Where the angle opens -/

/-- The angle is zero exactly at the seeds `d = 2, 3`. -/
theorem anguloNRS_eq_zero_iff {d : ℕ} (hd : 2 ≤ d) : anguloNRS d = 0 ↔ d = 2 ∨ d = 3 := by
  have hC := CoherenceConstant_ge_one hd
  rw [anguloNRS_eq hd, arccos_eq_zero, le_div_iff₀ (by linarith), one_mul,
    ← CoherenceConstant_eq_one_iff d hd]
  constructor <;> intro h <;> linarith

/-- **The algebraic quantum as an angle.** On every axis with `4` or more sites the two
fluctuation vectors are never parallel. -/
theorem anguloNRS_pos {d : ℕ} (hd : 4 ≤ d) : 0 < anguloNRS d := by
  have hC : 1 < CoherenceConstant d := by
    rw [CoherenceConstant_eq_one_add_geometricGap]
    linarith [geometricGap_pos_of_four_le d hd]
  rw [anguloNRS_eq (by omega), arccos_pos, div_lt_one (by linarith)]
  exact hC

theorem CoherenceConstantInf_pos : 0 < CoherenceConstantInf := by
  have := deltaInf_pos
  unfold deltaInf at this
  linarith

/-- The angle opens strictly with `d` from `4` on. -/
theorem anguloNRS_strictMonoOn : StrictMonoOn anguloNRS {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  have ha' : (4 : ℕ) ≤ a := ha
  have hb' : (4 : ℕ) ≤ b := hb
  have hCa := CoherenceConstant_ge_one (by omega : 2 ≤ a)
  have hCb := CoherenceConstant_ge_one (by omega : 2 ≤ b)
  have hlt : CoherenceConstant a < CoherenceConstant b := by
    have := geometricGap_strictMonoOn_ge_four ha hb hab
    simpa [geometricGap] using this
  rw [anguloNRS_eq (by omega), anguloNRS_eq (by omega)]
  have hb0 : 0 < 1 / CoherenceConstant b := one_div_pos.mpr (by linarith)
  apply arccos_lt_arccos (by linarith)
  · exact one_div_lt_one_div_of_lt (by linarith) hlt
  · rw [div_le_one (by linarith)]; exact hCa

/-- The angle stays strictly below `arccos (1 / C_∞)`, which no `d` attains. -/
theorem anguloNRS_lt_limite {d : ℕ} (hd : 4 ≤ d) :
    anguloNRS d < arccos (1 / CoherenceConstantInf) := by
  have hCd := CoherenceConstant_ge_one (by omega : 2 ≤ d)
  have hlt : CoherenceConstant d < CoherenceConstantInf := by
    have := geometricGap_lt_deltaInf d hd
    simpa [geometricGap, deltaInf] using this
  rw [anguloNRS_eq (by omega)]
  apply arccos_lt_arccos (by have := one_div_pos.mpr CoherenceConstantInf_pos; linarith)
  · exact one_div_lt_one_div_of_lt (by linarith) hlt
  · rw [div_le_one (by linarith)]; exact hCd

/-- The first opening, in closed form: `θ_NRS(4) = arccos (1 / √((99 − 42√5)/5))`. -/
theorem anguloNRS_cuatro :
    anguloNRS 4 = arccos (1 / Real.sqrt ((99 - 42 * Real.sqrt 5) / 5)) := by
  rw [anguloNRS_eq (by norm_num), CoherenceConstant, CoherenceConstantSq_four_eq]

/-- **Universal angular floor.** Every axis with `4` or more sites opens at least `θ_NRS(4)`,
and never reaches `arccos (1 / C_∞)`. -/
theorem piso_angular {d : ℕ} (hd : 4 ≤ d) :
    0 < anguloNRS 4 ∧ anguloNRS 4 ≤ anguloNRS d ∧
      anguloNRS d < arccos (1 / CoherenceConstantInf) :=
  ⟨anguloNRS_pos le_rfl,
    anguloNRS_strictMonoOn.monotoneOn (show (4 : ℕ) ≤ 4 from le_rfl) hd hd,
    anguloNRS_lt_limite hd⟩

/-- **Finite isotropy for two rows.** If both rows have at least `D ≥ 4` sites, their angles
differ by less than `arccos (1 / C_∞) − θ_NRS(D)`: a statement about finite rows only, with the
unattained ceiling `arccos (1 / C_∞)` as the sole reference. -/
theorem anguloNRS_isotropia {D a b : ℕ} (hD : 4 ≤ D) (ha : D ≤ a) (hb : D ≤ b) :
    |anguloNRS a - anguloNRS b| < arccos (1 / CoherenceConstantInf) - anguloNRS D := by
  have mono := anguloNRS_strictMonoOn.monotoneOn
  have hDa : anguloNRS D ≤ anguloNRS a := mono (show 4 ≤ D from hD) (show 4 ≤ a by omega) ha
  have hDb : anguloNRS D ≤ anguloNRS b := mono (show 4 ≤ D from hD) (show 4 ≤ b by omega) hb
  have la := anguloNRS_lt_limite (show 4 ≤ a by omega)
  have lb := anguloNRS_lt_limite (show 4 ≤ b by omega)
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ## 3. One angle per axis of the cube -/

section Cubo

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
  [DecidableEq ι] [DecidableEq α] [DecidableEq β]

theorem anguloG_lift (e : ι ≃ α × β) {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1)
    (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    anguloG (Matrix.toEuclideanLin (liftAlong e A)) (Matrix.toEuclideanLin (liftAlong e B))
        (prodAlong e ψ φ) =
      anguloG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  have hn : ∀ v : EuclideanSpace ℂ α, ‖prodAlong e v φ‖ = ‖v‖ := fun v =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (norm_sq_prodAlong e v φ hφ)
  rw [anguloG, anguloG, centradoG_lift e hφ, centradoG_lift e hφ, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one, hn, hn]

variable {dx dy dz : ℕ}

theorem anguloG_eje_x (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    anguloG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) = anguloNRS dx := by
  rw [PsiStar3D_eq_eX]
  exact anguloG_lift _ (norm_resto hy hz) _ _ _

theorem anguloG_eje_y (hx : 2 ≤ dx) (hz : 2 ≤ dz) :
    anguloG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) = anguloNRS dy := by
  rw [PsiStar3D_eq_eY]
  exact anguloG_lift _ (norm_resto hx hz) _ _ _

theorem anguloG_eje_z (hx : 2 ≤ dx) (hy : 2 ≤ dy) :
    anguloG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) = anguloNRS dz := by
  rw [PsiStar3D_eq_eZ]
  exact anguloG_lift _ (norm_resto hx hy) _ _ _

/-- **On the `4 × 4 × 4` cube and beyond**, all three axes carry a strictly positive angle,
each below the same unattained bound `arccos (1 / C_∞)`. -/
theorem angulos_cubo (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    (0 < anguloG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) ∧
        anguloG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) <
          arccos (1 / CoherenceConstantInf)) ∧
      (0 < anguloG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) ∧
        anguloG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) <
          arccos (1 / CoherenceConstantInf)) ∧
      (0 < anguloG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) ∧
        anguloG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) <
          arccos (1 / CoherenceConstantInf)) := by
  rw [anguloG_eje_x (by omega) (by omega), anguloG_eje_y (by omega) (by omega),
    anguloG_eje_z (by omega) (by omega)]
  exact ⟨⟨anguloNRS_pos hx, anguloNRS_lt_limite hx⟩, ⟨anguloNRS_pos hy, anguloNRS_lt_limite hy⟩,
    ⟨anguloNRS_pos hz, anguloNRS_lt_limite hz⟩⟩

/-- **The angular floor on the cube.** With `4` or more sites on every axis, each of the three
axes opens at least `θ_NRS(4)`. -/
theorem piso_angular_cubo (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    anguloNRS 4 ≤ anguloG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) ∧
      anguloNRS 4 ≤ anguloG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) ∧
      anguloNRS 4 ≤ anguloG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz) := by
  rw [anguloG_eje_x (by omega) (by omega), anguloG_eje_y (by omega) (by omega),
    anguloG_eje_z (by omega) (by omega)]
  exact ⟨(piso_angular hx).2.1, (piso_angular hy).2.1, (piso_angular hz).2.1⟩

/-- **Finite isotropy of the cube.** In any cube with at least `D ≥ 4` sites on every axis, the
angles of any two axes differ by less than `arccos (1 / C_∞) − θ_NRS(D)`. With `D = 100` this is
about `1.05°`: the three axes agree more closely the more sites each has, with no appeal
to an infinite lattice. -/
theorem isotropia_finita_cubo {D : ℕ} (hD : 4 ≤ D) (hx : D ≤ dx) (hy : D ≤ dy) (hz : D ≤ dz) :
    |anguloG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) -
        anguloG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz)| <
        arccos (1 / CoherenceConstantInf) - anguloNRS D ∧
      |anguloG (TX dx dy dz) (PX dx dy dz) (PsiStar3D dx dy dz) -
        anguloG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz)| <
        arccos (1 / CoherenceConstantInf) - anguloNRS D ∧
      |anguloG (TY dx dy dz) (PY dx dy dz) (PsiStar3D dx dy dz) -
        anguloG (TZ dx dy dz) (PZ dx dy dz) (PsiStar3D dx dy dz)| <
        arccos (1 / CoherenceConstantInf) - anguloNRS D := by
  rw [anguloG_eje_x (by omega) (by omega), anguloG_eje_y (by omega) (by omega),
    anguloG_eje_z (by omega) (by omega)]
  exact ⟨anguloNRS_isotropia hD hx hy, anguloNRS_isotropia hD hx hz,
    anguloNRS_isotropia hD hy hz⟩

end Cubo

end AnguloNRS

end

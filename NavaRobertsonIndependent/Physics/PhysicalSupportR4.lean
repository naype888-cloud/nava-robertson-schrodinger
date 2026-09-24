import NavaRobertsonIndependent.Physics.TimeEnergyRegistrationClosure
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Soporte físico: ℝ⁴ capado, discreto y finito

**Principio de instanciación.** El ℝ de Cantor es matemática demostrada, un teorema
como Pitágoras, pero no se importa al 100% al mundo físico. Como los límites ya
están demostrados (piso `L_sbpk`, `τ_sbpk`; techo `δ_∞`; eones finitos), el soporte
físico se instancia como un subconjunto **acotado, discreto y finito** de `ℝ⁴` y se
deriva sobre él.

* **Lo que se importa de ℝ⁴:** sus teoremas, que valen en todo subconjunto
  (`teoremas_de_R4_se_restringen`). `ℝ⁴` euclídeo es a la vez espacio de Hilbert y
  de Banach (`R4_es_Hilbert_y_Banach`): da igual trabajar en uno u otro.
* **Lo que no se importa: el continuo.** En el soporte toda sucesión convergente
  termina siendo constante (`convergente_es_eventualmente_constante`): no hay
  límites no triviales, ni derivadas, ni divisibilidad sin fin.

Espacio: `soporte N = {k·L_sbpk : |k| ≤ N}⁴ ⊂ ℝ⁴`. Tiempo: conteos `n·τ_sbpk`;
son numerables y por tanto no son el continuo de Cantor (`registrados_ne_continuo`),
ninguno cae en `(0, τ_sbpk)`, se separan al menos un tick, y un eón de `N` ticks
tiene exactamente `N+1` tiempos.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas estándar.
-/

noncomputable section

namespace SoporteFisicoR4

open LimiteSubPlanckiano CierreRegistroTiempoEnergiaSbpk

/-- `ℝ⁴` euclídeo. -/
abbrev R4 := EuclideanSpace ℝ (Fin 4)

/-- `ℝ⁴` euclídeo es espacio de Hilbert (producto interno, completo) y de Banach
(normado, completo). -/
theorem R4_es_Hilbert_y_Banach :
    Nonempty (InnerProductSpace ℝ R4) ∧ Nonempty (NormedSpace ℝ R4) ∧ CompleteSpace R4 :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, inferInstance⟩

/-! ## Espacio -/

/-- Índices de la red: `-N ≤ k ≤ N` en cada coordenada. -/
abbrev Indice (N : ℕ) := Fin 4 → Finset.Icc (-(N : ℤ)) N

/-- Punto de `ℝ⁴` con coordenadas múltiplos enteros de `L_sbpk`. -/
def punto {N : ℕ} (k : Indice N) : R4 :=
  WithLp.toLp 2 (fun i => ((k i : ℤ) : ℝ) * Lsbpk)

/-- **Soporte físico**: la red acotada `{k·L_sbpk : |k| ≤ N}⁴ ⊂ ℝ⁴`. -/
def soporte (N : ℕ) : Set R4 := Set.range (punto (N := N))

theorem soporte_finito (N : ℕ) : (soporte N).Finite := Set.finite_range _

theorem soporte_acotado {N : ℕ} {x : R4} (hx : x ∈ soporte N) (i : Fin 4) :
    |x i| ≤ N * Lsbpk := by
  obtain ⟨k, rfl⟩ := hx
  have hk := Finset.mem_Icc.mp (k i).2
  simp only [punto, PiLp.toLp_apply]
  rw [abs_mul, abs_of_pos Lsbpk_pos]
  apply mul_le_mul_of_nonneg_right _ Lsbpk_pos.le
  have : |((k i : ℤ))| ≤ (N : ℤ) := abs_le.mpr ⟨hk.1, hk.2⟩
  exact_mod_cast this

/-- Dos puntos distintos del soporte distan al menos `L_sbpk`. -/
theorem separacion_minima {N : ℕ} {x y : R4} (hx : x ∈ soporte N) (hy : y ∈ soporte N)
    (hxy : x ≠ y) : Lsbpk ≤ dist x y := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  have : ∃ i, (k i : ℤ) ≠ (l i : ℤ) := by
    by_contra h
    push Not at h
    apply hxy
    have hkl : k = l := funext fun i => Subtype.ext (h i)
    rw [hkl]
  obtain ⟨i, hi⟩ := this
  have hc : (1 : ℝ) ≤ |((k i : ℤ) : ℝ) - ((l i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |(k i : ℤ) - (l i : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hi)
    exact_mod_cast this
  calc Lsbpk ≤ |((k i : ℤ) : ℝ) - ((l i : ℤ) : ℝ)| * Lsbpk := by nlinarith [Lsbpk_pos]
    _ = dist ((punto k) i) ((punto l) i) := by
        simp only [punto, PiLp.toLp_apply, Real.dist_eq]
        rw [← sub_mul, abs_mul, abs_of_pos Lsbpk_pos]
    _ ≤ dist (punto k) (punto l) := PiLp.dist_apply_le _ _ _

/-- **Lo que no se importa de Cantor: el continuo.** En el soporte, toda sucesión
convergente termina siendo constante. -/
theorem convergente_es_eventualmente_constante {N : ℕ} {u : ℕ → R4}
    (hu : ∀ n, u n ∈ soporte N) {a : R4} (h : Filter.Tendsto u Filter.atTop (nhds a)) :
    ∃ M, ∀ n ≥ M, u n = u M := by
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.mp h.cauchySeq Lsbpk Lsbpk_pos
  refine ⟨M, fun n hn => ?_⟩
  by_contra hne
  exact absurd (separacion_minima (hu n) (hu M) hne) (not_le.mpr (hM n hn))

/-- **Lo que sí se importa de ℝ⁴:** sus teoremas valen sobre el soporte (aquí, la
desigualdad triangular). -/
theorem teoremas_de_R4_se_restringen {N : ℕ} {x y z : R4}
    (_ : x ∈ soporte N) (_ : y ∈ soporte N) (_ : z ∈ soporte N) :
    dist x z ≤ dist x y + dist y z := dist_triangle x y z

/-! ## Tiempo -/

/-- Tiempos registrables: conteos de ticks. -/
def tiemposRegistrados : Set ℝ := Set.range tiempoFisico

/-- El ℝ de Cantor no es numerable. -/
theorem cantor_no_numerable : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real

theorem registrados_numerables : tiemposRegistrados.Countable :=
  Set.countable_range _

/-- Los tiempos registrados no son el continuo de Cantor. -/
theorem registrados_ne_continuo : tiemposRegistrados ≠ Set.univ := fun h =>
  cantor_no_numerable (h ▸ registrados_numerables)

/-- Ningún tiempo registrado cae en `(0, τ_sbpk)`. -/
theorem nada_bajo_el_tick (n : ℕ) : tiempoFisico n ∉ Set.Ioo 0 Tausbpk := by
  rintro ⟨h0, h1⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tiempoFisico] at h0
  · linarith [piso_temporal (n := n) hn]

/-- Dos tiempos registrados distintos se separan al menos un tick. -/
theorem separacion_un_tick {m n : ℕ} (h : m ≠ n) :
    Tausbpk ≤ |tiempoFisico m - tiempoFisico n| := by
  unfold tiempoFisico
  rw [← sub_mul, abs_mul, abs_of_pos Tausbpk_pos]
  have h1 : (1:ℝ) ≤ |(m:ℝ) - n| := by
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt
    · have : (m:ℝ) + 1 ≤ n := by exact_mod_cast hlt
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (n:ℝ) + 1 ≤ m := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]; linarith
  nlinarith [Tausbpk_pos]

/-- Un eón de `N` ticks tiene exactamente `N+1` tiempos, todos en `[0, N·τ_sbpk]`. -/
theorem eon_capado_finito (N : ℕ) :
    ((Finset.range (N + 1)).image tiempoFisico).card = N + 1 ∧
    ∀ t ∈ (Finset.range (N + 1)).image tiempoFisico, 0 ≤ t ∧ t ≤ N * Tausbpk := by
  constructor
  · rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro a b hab
    unfold tiempoFisico at hab
    have := mul_right_cancel₀ Tausbpk_pos.ne' hab
    exact_mod_cast this
  · intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have hn' : (n:ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    unfold tiempoFisico
    exact ⟨mul_nonneg (Nat.cast_nonneg _) Tausbpk_pos.le,
      mul_le_mul_of_nonneg_right hn' Tausbpk_pos.le⟩

end SoporteFisicoR4

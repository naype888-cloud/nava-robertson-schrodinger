/-
Formalización del modelo de Ferrer i Cancho y Solé,
"Least effort and the origins of scaling in human language",
PNAS 100 (3), 788–791 (2003), Ecs. [1]–[14] y Fig. 1.
Solo Mathlib. Entropías en nats; la normalización por log n / log m del artículo
(H_n, H_m con base n y m) se aplica al final.
-/
import Mathlib

open Finset Real

namespace Zipf

noncomputable section

variable {n m : ℕ}

/-- `a_ij ∈ {0,1}` como real. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by unfold ind; split_ifs <;> norm_num

/-- Matriz binaria señal–objeto `A = {a_ij}` (n señales, m objetos). -/
abbrev Mat (n m : ℕ) := Fin n → Fin m → Bool

/-- `ω_j = ∑_i a_ij`: número de sinónimos del objeto `j` (tras la Ec. [4]). -/
def omega (A : Mat n m) (j : Fin m) : ℝ := ∑ i, ind (A i j)

/-- Configuraciones válidas: todo objeto tiene al menos una señal (Métodos). -/
def Valid (A : Mat n m) : Prop := ∀ j, 0 < omega A j

/-- `p(r_j, s_i) = p(r_j) p(s_i | r_j) = (1/m) · a_ij/ω_j` (Ecs. [3]–[5]). -/
def joint (A : Mat n m) (i : Fin n) (j : Fin m) : ℝ :=
  (1 / m) * (ind (A i j) / omega A j)

/-- `p(s_i) = ∑_j p(s_i, r_j)` (Ecs. [1]–[2]). -/
def sigProb (A : Mat n m) (i : Fin n) : ℝ := ∑ j, joint A i j

/-- `p(r_j | s_i)` (Teorema de Bayes, Ec. [5] dividida entre `p(s_i)`). -/
def condRS (A : Mat n m) (i : Fin n) (j : Fin m) : ℝ := joint A i j / sigProb A i

/-- Entropía de Shannon (nats) de un vector. -/
def Hn {k : ℕ} (p : Fin k → ℝ) : ℝ := ∑ i, negMulLog (p i)

/-- `H(S)` (Ec. [6], sin normalizar). -/
def HS (A : Mat n m) : ℝ := Hn (sigProb A)

/-- `H(R | S) = ∑_i p(s_i) H(R | s_i)` (Ecs. [7]–[8], sin normalizar). -/
def HRgS (A : Mat n m) : ℝ := ∑ i, sigProb A i * Hn (condRS A i)

/-- `H(S | R) = ∑_j p(r_j) H(S | r_j)` con `p(s_i | r_j) = a_ij/ω_j` (Ec. [4]). -/
def HSgR (A : Mat n m) : ℝ := ∑ j, (1 / (m : ℝ)) * Hn (fun i => ind (A i j) / omega A j)

/-- `H(R)` con `p(r) = 1/m`. -/
def HR (m : ℕ) : ℝ := Hn (fun _ : Fin m => (1 : ℝ) / m)

/-- Entropía conjunta `H(S, R)`. -/
def Hjoint (A : Mat n m) : ℝ := ∑ i, ∑ j, negMulLog (joint A i j)

/-- Información mutua `I(S,R) = H(S) − H(S|R)` (Ec. [10]). -/
def MI (A : Mat n m) : ℝ := HS A - HSgR A

/-- Costo `Ω(λ) = λ H_m(R|S) + (1−λ) H_n(S)` (Ec. [9]), con `H_m`, `H_n` normalizadas. -/
def Omega (A : Mat n m) (lam : ℝ) : ℝ :=
  lam * (HRgS A / Real.log m) + (1 - lam) * (HS A / Real.log n)

/-! ### Consistencia del modelo -/

lemma joint_nonneg (A : Mat n m) (hA : Valid A) (i : Fin n) (j : Fin m) :
    0 ≤ joint A i j := by
  unfold joint
  have := hA j
  positivity [ind_nonneg (A i j)]

lemma sum_ind_div (A : Mat n m) (hA : Valid A) (j : Fin m) :
    ∑ i, ind (A i j) / omega A j = 1 := by
  rw [← Finset.sum_div]
  exact div_self (hA j).ne'

/-- Marginal sobre objetos: `∑_i p(s_i, r_j) = 1/m`. -/
lemma sum_joint_fst (A : Mat n m) (hA : Valid A) (j : Fin m) :
    ∑ i, joint A i j = 1 / m := by
  unfold joint
  rw [← Finset.mul_sum, sum_ind_div A hA j, mul_one]

/-- `∑_i p(s_i) = 1` (consistencia de las Ecs. [1]–[2]). -/
theorem sigProb_sum (A : Mat n m) (hA : Valid A) (hm : 0 < m) :
    ∑ i, sigProb A i = 1 := by
  unfold sigProb
  rw [Finset.sum_comm]
  simp_rw [sum_joint_fst A hA]
  simp
  field_simp

lemma sigProb_nonneg (A : Mat n m) (hA : Valid A) (i : Fin n) : 0 ≤ sigProb A i :=
  Finset.sum_nonneg fun j _ => joint_nonneg A hA i j

/-! ### Regla de la cadena: `H(S,R) = H(S) + H(R|S) = H(R) + H(S|R)` -/

lemma sum_condRS (A : Mat n m) (i : Fin n) (h : sigProb A i ≠ 0) :
    ∑ j, condRS A i j = 1 := by
  unfold condRS
  rw [← Finset.sum_div]
  exact div_self h

theorem chain_S (A : Mat n m) (hA : Valid A) : Hjoint A = HS A + HRgS A := by
  unfold Hjoint HS HRgS Hn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : sigProb A i = 0
  · have hz : ∀ j, joint A i j = 0 := fun j => by
      have hs : ∑ j, joint A i j = 0 := h
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => joint_nonneg A hA i j).1 hs j
        (Finset.mem_univ j)
    simp [hz, h]
  · have hj : ∀ j, joint A i j = sigProb A i * condRS A i j := fun j => by
      unfold condRS; field_simp
    simp_rw [hj, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, sum_condRS A i h]
    ring

theorem chain_R (A : Mat n m) (hA : Valid A) : Hjoint A = HR m + HSgR A := by
  unfold Hjoint HR HSgR Hn
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ∀ i, joint A i j = (1 / (m : ℝ)) * (ind (A i j) / omega A j) := fun i => rfl
  simp_rw [hj, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, sum_ind_div A hA j]
  ring

/-- `I(S,R) = H(S) + H(R) − H(S,R)` (simetría de la información mutua, Ec. [10]). -/
theorem MI_eq (A : Mat n m) (hA : Valid A) :
    MI A = HS A + HR m - Hjoint A := by
  have := chain_R A hA
  unfold MI; linarith

/-- `H(R|S) = H(R) − I(S,R)`. -/
theorem HRgS_eq (A : Mat n m) (hA : Valid A) :
    HRgS A = HR m - MI A := by
  have h1 := chain_S A hA
  have h2 := MI_eq A hA
  linarith

lemma HR_eq (hm : 2 ≤ m) : HR m = Real.log m := by
  unfold HR Hn
  have : (m : ℝ) ≠ 0 := by positivity
  simp [Real.negMulLog, Real.log_inv, this]

/-- Ec. [12]: con `p(r) = 1/m`, `Ω(λ) = λ (1 − I/log m) + (1−λ) H(S)/log n`;
equivale a minimizar `−λ I + (1−λ) H(S)`. -/
theorem Omega_eq_MI (A : Mat n m) (hA : Valid A) (hm : 2 ≤ m) (lam : ℝ) :
    Omega A lam = lam * (1 - MI A / Real.log m) + (1 - lam) * (HS A / Real.log n) := by
  have hl : Real.log m ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast hm
    exact (Real.log_pos this).ne'
  unfold Omega
  rw [HRgS_eq A hA, HR_eq hm]
  field_simp

/-! ### Los dos extremos en conflicto (Discusión del artículo)

Una sola señal para todos los objetos minimiza `H(S)` (esfuerzo del hablante) y
maximiza `H(R|S)`; el mapa uno a uno hace lo contrario. -/

/-- Una sola señal `i₀` para todos los objetos. -/
def single (i₀ : Fin n) : Mat n m := fun i _ => decide (i = i₀)

/-- Mapa uno a uno entre `n = m` señales y objetos. -/
def identity : Mat m m := fun i j => decide (i = j)

lemma single_omega (i₀ : Fin n) (j : Fin m) : omega (single i₀) j = 1 := by
  simp [omega, single, ind]

lemma single_valid (i₀ : Fin n) : Valid (single (m := m) i₀) := fun j => by
  rw [single_omega]; norm_num

lemma single_sigProb (hm : 0 < m) (i₀ i : Fin n) :
    sigProb (single (m := m) i₀) i = if i = i₀ then 1 else 0 := by
  have : (m : ℝ) ≠ 0 := by positivity
  by_cases h : i = i₀ <;> simp [sigProb, joint, single_omega, single, ind, h, this]

theorem HS_single (hm : 0 < m) (i₀ : Fin n) : HS (single (m := m) i₀) = 0 := by
  unfold HS Hn
  simp_rw [single_sigProb hm]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs <;> simp

theorem HRgS_single (hm : 0 < m) (i₀ : Fin n) :
    HRgS (single (m := m) i₀) = Real.log m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold HRgS
  rw [Finset.sum_eq_single i₀]
  · have hs : sigProb (single (m := m) i₀) i₀ = 1 := by simp [single_sigProb hm]
    have hc : ∀ j, condRS (single (m := m) i₀) i₀ j = 1 / m := fun j => by
      simp [condRS, hs, joint, single_omega, single, ind]
    simp only [hs, one_mul, Hn, hc]
    simp [Real.negMulLog, Real.log_inv, hm0]
  · intro i _ hi
    simp [single_sigProb hm, hi]
  · simp

lemma identity_omega (j : Fin m) : omega (identity (m := m)) j = 1 := by
  simp [omega, identity, ind]

lemma identity_valid : Valid (identity (m := m)) := fun j => by
  rw [identity_omega]; norm_num

lemma identity_sigProb (hm : 0 < m) (i : Fin m) :
    sigProb (identity (m := m)) i = 1 / m := by
  have : (m : ℝ) ≠ 0 := by positivity
  simp [sigProb, joint, identity_omega, identity, ind]

theorem HS_identity (hm : 2 ≤ m) : HS (identity (m := m)) = Real.log m := by
  have hm0 : 0 < m := by omega
  have : (m : ℝ) ≠ 0 := by positivity
  unfold HS Hn
  simp_rw [identity_sigProb hm0]
  simp [Real.negMulLog, Real.log_inv, this]

theorem HRgS_identity (hm : 0 < m) : HRgS (identity (m := m)) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold HRgS
  apply Finset.sum_eq_zero
  intro i _
  have hc : ∀ j, condRS (identity (m := m)) i j = if i = j then 1 else 0 := fun j => by
    by_cases h : i = j <;>
      simp [condRS, identity_sigProb hm, joint, identity_omega, identity, ind, h, hm0]
  simp only [Hn, hc]
  have : ∑ j, negMulLog (if i = j then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs <;> simp
  rw [this, mul_zero]

/-- Costo normalizado de los extremos: una sola señal cuesta `λ`. -/
theorem Omega_single (hm : 2 ≤ m) (i₀ : Fin n) (lam : ℝ) :
    Omega (single (m := m) i₀) lam = lam := by
  have hm0 : 0 < m := by omega
  have hl : Real.log m ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hm : (1 : ℝ) < m)).ne'
  unfold Omega
  rw [HRgS_single hm0, HS_single hm0]
  field_simp
  simp

/-- El mapa uno a uno cuesta `1 − λ` (con `n = m`). -/
theorem Omega_identity (hm : 2 ≤ m) (lam : ℝ) :
    Omega (identity (m := m)) lam = 1 - lam := by
  have hm0 : 0 < m := by omega
  have hl : Real.log m ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hm : (1 : ℝ) < m)).ne'
  unfold Omega
  rw [HRgS_identity hm0, HS_identity hm]
  field_simp
  simp

/-- Entre los dos extremos, el uno a uno es estrictamente más barato justo cuando `λ > 1/2`.
(El umbral numérico `λ* ≈ 0.41` del artículo es de simulación, no se deriva aquí.) -/
theorem identity_cheaper_iff (hm : 2 ≤ m) (i₀ : Fin m) (lam : ℝ) :
    Omega (identity (m := m)) lam < Omega (single (m := m) i₀) lam ↔ 1 / 2 < lam := by
  rw [Omega_identity hm, Omega_single hm]
  constructor <;> intro h <;> linarith

end

end Zipf

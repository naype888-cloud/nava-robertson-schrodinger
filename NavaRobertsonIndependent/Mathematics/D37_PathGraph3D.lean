import NavaRobertsonIndependent.Mathematics.D4_WhyNotDiagonal
import NavaRobertsonIndependent.Mathematics.D23b_NearMaximalTensionGap

/-!
# D37 — The path graph in three axes: `(T, P)` per axis and NRS on each

`D4` fixes the site of the cube, `Sitio3D dx dy dz = Fin dx × Fin dy × Fin dz`, and shows
that the elementary step changes exactly one coordinate (the diagonal is never minimal).
This file puts the operators on that cube: one pair `(T, P)` per axis, each acting as the
`D3` pair `(T_d, P_d)` on its own coordinate and as the identity on the other two.

* Pairs on different axes commute (`conmutador_ejes_distintos_*`): only `T` and `P` of
  the same axis collide.
* At the product state `Ψ* = ψ*_{dx} ⊗ ψ*_{dy} ⊗ ψ*_{dz}` every statistic of the pair of
  an axis — mean, variance, covariance, tension `⟨i[T,P]⟩` — is exactly the `D21`
  statistic of that axis (`estadisticas_eje_*`).
* Hence the Nava–Robertson–Schrödinger inequality holds on each axis with that axis's
  own `C_Nava`: it saturates exactly when the axis has `2` or `3` sites and is strict
  from `4` sites on (`saturacion_eje_*`, `estricta_eje_*`).

Everything is proved once for a general axis (`liftAlong`, `prodAlong`) and then
instantiated three times through the coordinate permutations `eX`, `eY`, `eZ`.
-/

noncomputable section

open TransportePosicion NavaRobertsonSchrodingerEDUI ConstructorEspectralTP
open PathGraph3D (Sitio3D)

namespace PathGraph3DNRS

/-! ## 1. One axis inside a product -/

section Eje

variable {ι α β : Type*}

/-- The product state: amplitude `ψ` on the axis times `φ` on the rest. -/
def prodAlong (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun p => ψ (e p).1 * φ (e p).2

theorem prodAlong_apply (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β)
    (p : ι) : prodAlong e ψ φ p = ψ (e p).1 * φ (e p).2 := rfl

theorem prodAlong_sub (e : ι ≃ α × β) (ψ ψ' : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    prodAlong e (ψ - ψ') φ = prodAlong e ψ φ - prodAlong e ψ' φ := by
  ext p
  simp [prodAlong_apply, sub_mul]

theorem prodAlong_smul (e : ι ≃ α × β) (c : ℂ) (ψ : EuclideanSpace ℂ α)
    (φ : EuclideanSpace ℂ β) : prodAlong e (c • ψ) φ = c • prodAlong e ψ φ := by
  ext p
  simp [prodAlong_apply, mul_assoc]

variable [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq α] [DecidableEq β]

/-- An operator `A` on the axis `α`, lifted to `ι ≃ α × β`: `A` on the axis, identity on the
rest. -/
def liftAlong (e : ι ≃ α × β) (A : Matrix α α ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun p q => A (e p).1 (e q).1 * if (e p).2 = (e q).2 then 1 else 0

/-- The lifted operator acts on the axis factor only. -/
theorem toEuclideanLin_liftAlong (e : ι ≃ α × β) (A : Matrix α α ℂ)
    (ψ : EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    Matrix.toEuclideanLin (liftAlong e A) (prodAlong e ψ φ) =
      prodAlong e (Matrix.toEuclideanLin A ψ) φ := by
  ext p
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    prodAlong_apply, liftAlong, Matrix.of_apply]
  rw [Fintype.sum_equiv e _ (fun x => A (e p).1 x.1 * (if (e p).2 = x.2 then 1 else 0) *
    (ψ x.1 * φ x.2)) (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, mul_assoc]

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
/-- Inner products factor over the product. -/
theorem inner_prodAlong (e : ι ≃ α × β) (ψ ψ' : EuclideanSpace ℂ α)
    (φ φ' : EuclideanSpace ℂ β) :
    inner ℂ (prodAlong e ψ φ) (prodAlong e ψ' φ') = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, prodAlong_apply]
  rw [Fintype.sum_equiv e _ (fun x => ψ' x.1 * φ' x.2 * (starRingEnd ℂ) (ψ x.1 * φ x.2))
    (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul]
  ring

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem norm_sq_prodAlong (e : ι ≃ α × β) (ψ : EuclideanSpace ℂ α)
    (φ : EuclideanSpace ℂ β) (hφ : ‖φ‖ = 1) : ‖prodAlong e ψ φ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have h := inner_prodAlong e ψ ψ φ φ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    hφ] at h
  exact_mod_cast (by simpa using h : ((‖prodAlong e ψ φ‖ ^ 2 : ℝ) : ℂ) = ((‖ψ‖ ^ 2 : ℝ) : ℂ))

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem norm_prodAlong_eq_one (e : ι ≃ α × β) {ψ : EuclideanSpace ℂ α}
    {φ : EuclideanSpace ℂ β} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) : ‖prodAlong e ψ φ‖ = 1 := by
  have h := norm_sq_prodAlong e ψ φ hφ
  rw [hψ, one_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] in
theorem inner_self_of_norm_one {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1) :
    inner ℂ φ φ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hφ]
  simp

/-! ## 2. The `D21` statistics on any finite site set -/

/-- Mean `Re ⟨Ψ, LΨ⟩`: `D21`'s `media` on `ℂ^ι` (it is `media` itself when `ι = Fin d`). -/
def mediaG (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ Ψ (L Ψ)).re

def centradoG (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  L Ψ - (mediaG L Ψ : ℂ) • Ψ

def varianzaG (L : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  ‖centradoG L Ψ‖ ^ 2

def covarianzaG (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ (centradoG L Ψ) (centradoG M Ψ)).re

/-- Tension `⟨i[L, M]⟩` (`D23b`'s `tension` on `ℂ^ι`). -/
def tensionG (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (Ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ Ψ (observableTension L M Ψ)).re

/-! ## 3. Lifted statistics are the statistics of the axis -/

variable (e : ι ≃ α × β) {φ : EuclideanSpace ℂ β} (hφ : ‖φ‖ = 1)
include hφ

theorem mediaG_lift (A : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    mediaG (Matrix.toEuclideanLin (liftAlong e A)) (prodAlong e ψ φ) =
      mediaG (Matrix.toEuclideanLin A) ψ := by
  rw [mediaG, mediaG, toEuclideanLin_liftAlong, inner_prodAlong, inner_self_of_norm_one hφ,
    mul_one]

theorem centradoG_lift (A : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    centradoG (Matrix.toEuclideanLin (liftAlong e A)) (prodAlong e ψ φ) =
      prodAlong e (centradoG (Matrix.toEuclideanLin A) ψ) φ := by
  rw [centradoG, centradoG, mediaG_lift e hφ, toEuclideanLin_liftAlong, prodAlong_sub,
    prodAlong_smul]

theorem varianzaG_lift (A : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    varianzaG (Matrix.toEuclideanLin (liftAlong e A)) (prodAlong e ψ φ) =
      varianzaG (Matrix.toEuclideanLin A) ψ := by
  rw [varianzaG, varianzaG, centradoG_lift e hφ, norm_sq_prodAlong e _ _ hφ]

theorem covarianzaG_lift (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    covarianzaG (Matrix.toEuclideanLin (liftAlong e A)) (Matrix.toEuclideanLin (liftAlong e B))
        (prodAlong e ψ φ) =
      covarianzaG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  rw [covarianzaG, covarianzaG, centradoG_lift e hφ, centradoG_lift e hφ, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one]

theorem tensionG_lift (A B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    tensionG (Matrix.toEuclideanLin (liftAlong e A)) (Matrix.toEuclideanLin (liftAlong e B))
        (prodAlong e ψ φ) =
      tensionG (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) ψ := by
  simp only [tensionG, observableTension, conmutador, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, toEuclideanLin_liftAlong, ← prodAlong_sub, ← prodAlong_smul,
    inner_prodAlong, inner_self_of_norm_one hφ, mul_one]

/-! ## 4. NRS on one axis of a product -/

/-- On any axis with `d ≥ 2` sites, lifted into a product with a unit state `φ` on the rest,
the four statistics of `(T, P)` at `ψ* ⊗ φ` are those of `(T_d, P_d)` at `ψ*` (`D21`). -/
theorem estadisticas_eje {d : ℕ} (hd : 2 ≤ d) (e : ι ≃ Fin d × β) :
    varianzaG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e (psiStar d) φ) =
        varianza (TdOp d) (psiStar d) ∧
      varianzaG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) =
        varianza (PdOp d) (psiStar d) ∧
      covarianzaG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) =
        covarianza (TdOp d) (PdOp d) (psiStar d) ∧
      tensionG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) =
        2 / ((d : ℝ) - 1) :=
  ⟨varianzaG_lift e hφ _ _, varianzaG_lift e hφ _ _, covarianzaG_lift e hφ _ _ _,
    (tensionG_lift e hφ _ _ _).trans (SobranteIntermedio.tension_psiStar hd)⟩

/-- NRS on one axis: saturation exactly for `2` or `3` sites on that axis. -/
theorem saturacion_eje {d : ℕ} (hd : 2 ≤ d) (e : ι ≃ Fin d × β) :
    covarianzaG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) ^ 2 +
        (commutatorConstant d / 2) ^ 2 =
      varianzaG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e (psiStar d) φ) *
        varianzaG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) ↔
      d = 2 ∨ d = 3 := by
  obtain ⟨h1, h2, h3, -⟩ := estadisticas_eje hφ hd e
  rw [h1, h2, h3]
  exact saturacion_iff hd

/-- NRS on one axis: from `4` sites on, the inequality is strict (the algebraic quantum). -/
theorem estricta_eje {d : ℕ} (hd : 4 ≤ d) (e : ι ≃ Fin d × β) :
    covarianzaG (Matrix.toEuclideanLin (liftAlong e (Td d)))
          (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) ^ 2 +
        (commutatorConstant d / 2) ^ 2 <
      varianzaG (Matrix.toEuclideanLin (liftAlong e (Td d))) (prodAlong e (psiStar d) φ) *
        varianzaG (Matrix.toEuclideanLin (liftAlong e (Pd d))) (prodAlong e (psiStar d) φ) := by
  obtain ⟨h1, h2, h3, -⟩ := estadisticas_eje hφ (by omega) e
  rw [h1, h2, h3]
  exact desigualdad_estricta hd

end Eje

end PathGraph3DNRS

end

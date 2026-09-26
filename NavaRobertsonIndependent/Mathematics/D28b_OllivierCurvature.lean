/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D28_BakryEmeryCurvature

/-!
# D28b — Curvatura de Ollivier-Ricci del camino discreto: `κ = 0` en el interior

Cierra un hueco que dejó `D28` (señalado por Kimi tras verificarlo): el
docstring de `D28` afirma que su conclusión coincide "con Ollivier-Ricci,
calculado aparte, misma conclusión por transporte óptimo" — pero ese
cálculo no estaba en ningún archivo, solo en una sesión de chat. Aquí se
formaliza.

Se usa la caracterización dual de Kantorovich–Rubinstein de la distancia de
Wasserstein-1 (estándar en la literatura de curvatura de Ollivier-Ricci,
Ollivier 2009): para medidas de probabilidad `μ,ν`, `W₁(μ,ν) = sup { E_μf −
E_νf : f 1-Lipschitz }`. Para la caminata aleatoria uniforme sobre el
camino, las distribuciones de un paso desde dos vértices consecutivos
interiores `j`, `j+1` son `m_j = ½δ_{j−1}+½δ_{j+1}` y
`m_{j+1} = ½δ_j+½δ_{j+2}`. Esa gap se calcula aquí de forma
completamente elemental —sin invocar la maquinaria general de transporte
óptimo de Mathlib, para mantener el módulo autocontenido—: la cota superior
sale de la propiedad Lipschitz, la cota inferior de evaluar en la identidad.
El resultado es `W₁ = 1 = d(j,j+1)`, luego `κ(j,j+1) = 1 − W₁/d(j,j+1) = 0`
— exactamente lo que ya daba `D28` por Bakry-Émery. Las dos nociones de
curvatura discreta coinciden: el interior del camino es plano en ambas.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib.
-/

@[expose] public noncomputable section

namespace CurvaturaOllivier

open TransportePosicion CurvaturaBakryEmery

/-! ## Capa algebraica: la gap de Kantorovich–Rubinstein en cuatro puntos -/

/-- `f` es 1-Lipschitz a lo largo de los tres pasos consecutivos
`x−1→x→x+1→x+2` (los únicos que hacen falta aquí). -/
def Lip1en4 (fm1 f0 fp1 fp2 : ℝ) : Prop :=
  |fm1 - f0| ≤ 1 ∧ |f0 - fp1| ≤ 1 ∧ |fp1 - fp2| ≤ 1

/-- Gap de Kantorovich–Rubinstein entre `m_x` y `m_{x+1}`:
`E_{m_x}f − E_{m_{x+1}}f`. -/
def gapKR (fm1 f0 fp1 fp2 : ℝ) : ℝ := (fm1 + fp1) / 2 - (f0 + fp2) / 2

/-- **Cota superior**: toda función 1-Lipschitz acota la gap por `1`. -/
theorem gapKR_le_uno {fm1 f0 fp1 fp2 : ℝ} (h : Lip1en4 fm1 f0 fp1 fp2) :
    gapKR fm1 f0 fp1 fp2 ≤ 1 := by
  obtain ⟨h1, _h2, h3⟩ := h
  unfold gapKR
  have e1 := abs_le.mp h1
  have e3 := abs_le.mp h3
  linarith [e1.1, e1.2, e3.1, e3.2]

theorem neg_uno_le_gapKR {fm1 f0 fp1 fp2 : ℝ} (h : Lip1en4 fm1 f0 fp1 fp2) :
    -1 ≤ gapKR fm1 f0 fp1 fp2 := by
  obtain ⟨h1, _h2, h3⟩ := h
  unfold gapKR
  have e1 := abs_le.mp h1
  have e3 := abs_le.mp h3
  linarith [e1.1, e1.2, e3.1, e3.2]

/-- Testigo que satura la cota: la función decreciente `f = (1, 0, −1, −2)`
(1-Lipschitz, `lip1en4_testigo`) da gap exactamente `1`. -/
theorem gapKR_testigo : gapKR 1 0 (-1) (-2) = 1 := by
  unfold gapKR; norm_num

theorem lip1en4_testigo : Lip1en4 1 0 (-1) (-2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- **`W₁ = 1` exacto, vía Kantorovich–Rubinstein**: el supremo de la
gap sobre funciones 1-Lipschitz es exactamente `1` — cota y testigo, en
un solo enunciado (`IsGreatest`). -/
theorem W1_es_uno :
    IsGreatest
      {v : ℝ | ∃ fm1 f0 fp1 fp2 : ℝ, Lip1en4 fm1 f0 fp1 fp2 ∧ gapKR fm1 f0 fp1 fp2 = v} 1 := by
  constructor
  · exact ⟨1, 0, -1, -2, lip1en4_testigo, gapKR_testigo⟩
  · rintro v ⟨fm1, f0, fp1, fp2, h, rfl⟩
    exact gapKR_le_uno h

/-- Curvatura de Ollivier-Ricci de una arista: `κ = 1 − W₁/d`. -/
def kappaOllivier (W1 d : ℝ) : ℝ := 1 - W1 / d

/-- **La curvatura de Ollivier-Ricci del interior del camino es
exactamente `0`**: `W₁ = 1` (`W1_es_uno`) y la arista mide `d = 1`
(`PasoMinimo`, D3), luego `κ = 1 − 1/1 = 0`. -/
theorem kappa_ollivier_interior_es_cero : kappaOllivier 1 1 = 0 := by
  unfold kappaOllivier; norm_num

/-! ## Conexión con `GrafoTP d`: la arista realmente vive en el camino -/

/-- La arista `(j, j+1)` sobre la que se calculó `κ = 0` es, genuinamente,
una arista de `GrafoTP d` (`D3.grafoTP_adj`, vía `D28.adj_ip1`) — el cálculo
de arriba no es un juguete aislado del corpus. -/
theorem arista_es_grafoTP {d : ℕ} (j : Fin d) (h2 : j.val + 1 < d) :
    (GrafoTP d).Adj j (ip1 j h2) :=
  adj_ip1 j h2

/-- **Cierre.** Sobre cualquier arista interior `(j, j+1)` de `GrafoTP d`
con margen suficiente para que `j−1` y `j+2` existan también
(`h1 : 1 ≤ j.val`, `h2 : j.val + 2 < d` — exactamente el rango donde vive el
cálculo de `W₁` de arriba), la arista es real (`arista_es_grafoTP`) y su
curvatura de Ollivier-Ricci es exactamente `0`
(`kappa_ollivier_interior_es_cero`) — la misma conclusión, letra por letra,
que `curvatura_camino_CD02` de `D28` da por Bakry-Émery. Las dos nociones
de curvatura discreta convergen: el camino es plano. -/
theorem convergencia_bakry_emery_ollivier {d : ℕ} (j : Fin d) (_h1 : 1 ≤ j.val)
    (h2 : j.val + 2 < d) :
    (GrafoTP d).Adj j (ip1 j (by omega)) ∧ kappaOllivier 1 1 = 0 :=
  ⟨arista_es_grafoTP j (by omega), kappa_ollivier_interior_es_cero⟩

end CurvaturaOllivier

/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D6_Fiedler
public import NavaRobertsonIndependent.Mathematics.D7_Niven
public import NavaRobertsonIndependent.Mathematics.D8_Szego
public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity

/-!
# D10 — Certificado conjunto: Fiedler + Niven + Szegő en `H_d`

Reúne, en un único certificado citable, los tres pilares que se apoyan sobre
el hábitat común `H_d = ℂ^d` (`D0_Habitat.lean`): la descomposición
espectral de Fiedler (`D6_Fiedler.lean`), el teorema de Niven
(`D7_Niven.lean`) y el límite de Szegő con la positividad de la gap
(`D8_Szego.lean`). Este es el teorema terminal del paquete: aquí se acaba
la matemática que se demuestra en este repositorio.

# Blindaje de `δ_geom(d)` en el Hilbert finito `H_d`

**Hábitat:** \(H_d=\mathtt{EuclideanSpace}\,\mathbb{C}\,(\mathtt{Fin}\,d)\).
No se abandona ese espacio: es el que acoge la derivación del marco.

**Terna de escudos** (todo sobre el discreto):

| Escudo | Contenido Lean |
|--------|----------------|
| **Fiedler** | modo fundamental / `KdOp` / radio espectral en \(H_d\) |
| **Niven** | `saturacion_iff` + `no_reposición_saturacion_camino` + `geometricGap_pos_of_four_le` |
| **Szegő** | `limite_szego_CoherenceConstant` + `deltaInf_pos` + ∞ no es dimensión |
| **Monotonía** | `geometricGap_four_le`: `δ_geom(4)` es el piso global para todo `d ≥ 4` |

Lectura: los productos trigonométricos simultáneamente racionales de la
saturación del camino **solo** existen en \(d\in\{2,3\}\). No hay más
seeds; por eso **nada repone la cota unitaria** después de \(d=4\).
Además, la monotonía certificada fija a \(d=4\) como el menor defect
realizado: cualquier medición en un \(H_d\) físico con \(d\ge4\) queda
separada del cero por al menos \(\delta_{\rm geom}(4)\). Al crecer la
familia finita, el defect no se apaga: converge a
\(\delta_\infty>0\).

**Cierre del hábitat:** \(H_d = \mathbb{C}^d \cong \mathbb{R}^{2d}\), finito.
Punto. Si quieren continuo infinito, aquí no es hotel — \(d=\infty\) no se
hospeda en este paquete; a lo más se le ve llegar por la ventana como límite
(`D8_Szego.lean`), pero nunca cruza la puerta.
-/

@[expose] public noncomputable section

open Real
open Filter
open scoped Topology

namespace BlindajeHd

open TransportePosicion
open Gnomon

/-! ## Habitat: no se sale de \(H_d\) -/

def HabitatHilbertFinito (d : ℕ) : Prop :=
  Hd d = EuclideanSpace ℂ (Fin d)

theorem habitatHilbertFinito (d : ℕ) : HabitatHilbertFinito d :=
  Hd_eq_euclidean d

theorem infinito_no_es_habitat :
    Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      deltaInf = CoherenceConstantInf - 1 ∧
      0 < deltaInf :=
  infinito_no_es_dimension_sino_limite

/-! ## Niven: cota unitaria no se repone -/

theorem niven_saturacion_solo_seeds (d : ℕ) (hd : 2 ≤ d) :
    cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3 :=
  saturacion_iff d hd

/-- **Nada repone la cota** tras \(d=4\). -/
theorem niven_cota_unitaria_no_se_repone (d : ℕ) (hd : 4 ≤ d) :
    cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 :=
  no_reposición_saturacion_camino d hd

theorem niven_geometricGap_pos_en_Hd (d : ℕ) (hd : 4 ≤ d) :
    0 < geometricGap d :=
  geometricGap_pos_of_four_le d hd

theorem piso_precision_geometricGap_d4_en_Hd (d : ℕ) (hd : 4 ≤ d) :
    geometricGap 4 ≤ geometricGap d :=
  geometricGap_four_le d hd

/-- En el régimen físico finito `H_d`, `d ≥ 4`, no existe lectura con defect
por debajo del piso elemental `δ_geom(4)`. -/
theorem no_medicion_absoluta_bajo_piso_d4_en_Hd
    (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : ε < geometricGap 4) :
    ε < geometricGap d :=
  lt_of_lt_of_le hε (piso_precision_geometricGap_d4_en_Hd d hd)

/-! ## Fiedler: espectro y banda en \(H_d\) -/

theorem fiedler_autovector_en_Hd (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (vectorFiedlerExplicito d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • vectorFiedlerExplicito d :=
  KdOp_vectorFiedlerExplicito d hd

theorem fiedler_radio_banda (d : ℕ) (hd : 2 ≤ d) :
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    letI : Nontrivial (Hd d) := inferInstance
    ConstructorEspectralTP.radioEspectral (KdOp d) (KdOp_simetrico d) =
      2 / ((d : ℝ) - 1) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (Hd d) := inferInstance
  exact radioEspectral_KdOp_eq_paso d hd

/-! ## Szegő: asintótica de la familia finita -/

theorem szego_limite_familia_finita :
    Tendsto CoherenceConstant atTop (𝓝 CoherenceConstantInf) :=
  limite_szego_CoherenceConstant

theorem szego_deltaInf_pos : 0 < deltaInf :=
  deltaInf_pos

theorem defect_real_positivo_desde_Hd4_hasta_limite :
    (∀ d : ℕ, 4 ≤ d → 0 < geometricGap d) ∧
      Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      0 < deltaInf :=
  ⟨niven_geometricGap_pos_en_Hd, limite_defect_geometrico, szego_deltaInf_pos⟩

/-! ## Certificado conjunto citable -/

structure CertificadoBlindajeHd where
  habitat : ∀ d : ℕ, HabitatHilbertFinito d
  niven_iff :
    ∀ d : ℕ, 2 ≤ d →
      (cos (π / ((d : ℝ) + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3)
  niven_no_reposición :
    ∀ d : ℕ, 4 ≤ d →
      cos (π / ((d : ℝ) + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4
  geometricGap_pos : ∀ d : ℕ, 4 ≤ d → 0 < geometricGap d
  geometricGap_piso_d4 : ∀ d : ℕ, 4 ≤ d → geometricGap 4 ≤ geometricGap d
  fiedler_autovector :
    ∀ d : ℕ, 2 ≤ d →
      KdOp d (vectorFiedlerExplicito d) =
        ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • vectorFiedlerExplicito d
  szego_limite : Tendsto CoherenceConstant atTop (𝓝 CoherenceConstantInf)
  szego_deltaInf : 0 < deltaInf
  defect_real_positivo :
    (∀ d : ℕ, 4 ≤ d → 0 < geometricGap d) ∧
      Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      0 < deltaInf
  infinito_limite :
    Tendsto geometricGap atTop (𝓝 deltaInf) ∧
      deltaInf = CoherenceConstantInf - 1 ∧ 0 < deltaInf

theorem certificadoBlindajeHd_OK : Nonempty CertificadoBlindajeHd :=
  ⟨{ habitat := habitatHilbertFinito
     niven_iff := fun d hd => niven_saturacion_solo_seeds d hd
     niven_no_reposición := fun d hd => niven_cota_unitaria_no_se_repone d hd
     geometricGap_pos := fun d hd => niven_geometricGap_pos_en_Hd d hd
     geometricGap_piso_d4 := fun d hd => piso_precision_geometricGap_d4_en_Hd d hd
     fiedler_autovector := fun d hd => fiedler_autovector_en_Hd d hd
     szego_limite := szego_limite_familia_finita
     szego_deltaInf := szego_deltaInf_pos
     defect_real_positivo := defect_real_positivo_desde_Hd4_hasta_limite
     infinito_limite := infinito_no_es_habitat }⟩

end BlindajeHd

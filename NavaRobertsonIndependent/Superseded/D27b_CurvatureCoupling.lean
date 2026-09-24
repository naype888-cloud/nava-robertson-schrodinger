import NavaRobertsonIndependent.Physics.SchwarzschildCollapse
import NavaRobertsonIndependent.Physics.SubPlanckianLimit
import NavaRobertsonIndependent.Superseded.D27_TimeDeformation

/-!
# D27b — `s(ρ)`, analítico: la masa de Schwarzschild acopla el estiramiento

> **Superseded (v14).** Depende de `D27` (celda estirada), que el mecanismo
> vigente reemplaza por el conteo de celdas (`D32`). Se conserva compilando, fuera de
> las cuatro capas.

Cierra el hallazgo (1) de la auditoría de `D27`: `HCurv` era una hipótesis
existencial (`∃ s>1, ρ>0`) sin ninguna función que los relacionara. Este
módulo da esa función — **puramente algebraica, sin aproximación numérica,
sin series de Taylor**: la monotonía sale del signo de un coeficiente
lineal, no de una cota de convergencia.

## La idea

`ColapsoSchwarzschild.masaSchwarzschild (G r) := r·c²/(2G)` ya está
demostrado. Leyendo el radio como la celda estirada, `r = s·Lsbpk`:

`M(G,s) = s·Lsbpk·c²/(2G) = s · K(G)`, con `K(G) = Lsbpk·c²/(2G) > 0`.

Es **lineal en `s`**, coeficiente estrictamente positivo. La monotonía de
`M` en `s` —y su inversa, `s` en `ρ := M`— es consecuencia directa del
signo de `K(G)`, sin necesitar nada más fuerte que álgebra de
desigualdades. `sDeRho` es la inversa exacta de `M` (no una función
elegida a mano): `sDeRho G (M G s) = s`, demostrado por `field_simp`.

Estatus: **verificado** (sin `sorry`). Depende solo de los tres axiomas
estándar de Mathlib.
-/

noncomputable section

open ColapsoSchwarzschild LimiteSubPlanckiano

namespace CurvaturaAcoplamiento

/-- La masa de Schwarzschild que corresponde a estirar la celda un factor
`s`: `M(G,s) := masaSchwarzschild(G, s·Lsbpk)`. -/
noncomputable def M (G s : ℝ) : ℝ := masaSchwarzschild G (s * Lsbpk)

/-- El coeficiente lineal: `K(G) = Lsbpk·c²/(2G)`. -/
noncomputable def K (G : ℝ) : ℝ := Lsbpk * cSI ^ 2 / (2 * G)

theorem K_pos {G : ℝ} (hG : 0 < G) : 0 < K G := by
  unfold K
  have hcSI2 : 0 < cSI ^ 2 := pow_pos cSI_pos 2
  have h2G : 0 < 2 * G := by linarith
  exact div_pos (mul_pos Lsbpk_pos hcSI2) h2G

/-- `M` es exactamente lineal en `s`, con coeficiente `K(G)`. -/
theorem M_eq_s_mul_K (G s : ℝ) : M G s = s * K G := by
  unfold M K masaSchwarzschild
  ring

/-- **Monotonía de `M` en `s`** — puro signo del coeficiente lineal, sin
aproximación: más estiramiento exige estrictamente más masa. -/
theorem M_monotona {G : ℝ} (hG : 0 < G) {s1 s2 : ℝ} (h : s1 < s2) :
    M G s1 < M G s2 := by
  rw [M_eq_s_mul_K, M_eq_s_mul_K]
  exact mul_lt_mul_of_pos_right h (K_pos hG)

/-- **La inversa exacta**: dado `ρ` (la masa/densidad), el estiramiento
`s` que la produce. No es una función elegida a mano — es la inversa
algebraica de `M`, como confirma `sDeRho_M_eq_s` abajo. -/
noncomputable def sDeRho (G ρ : ℝ) : ℝ := ρ / K G

/-- **Monotonía de `s(ρ)`** — la pieza que hacía falta: a más masa/densidad,
estrictamente más estiramiento. De nuevo, solo signo de `K(G)`, ninguna
cota numérica. -/
theorem sDeRho_monotona {G : ℝ} (hG : 0 < G) {ρ1 ρ2 : ℝ} (h : ρ1 < ρ2) :
    sDeRho G ρ1 < sDeRho G ρ2 := by
  unfold sDeRho
  exact div_lt_div_of_pos_right h (K_pos hG)

/-- **Ida y vuelta exacta**: `sDeRho` deshace `M` sin pérdida — no es una
función arbitraria que "también resulta monótona", es literalmente la
inversa de la que ya se demostró monótona arriba. -/
theorem sDeRho_M_eq_s {G : ℝ} (hG : 0 < G) (s : ℝ) :
    sDeRho G (M G s) = s := by
  unfold sDeRho
  rw [M_eq_s_mul_K]
  exact mul_div_cancel_right₀ s (K_pos hG).ne'

/-- **Cierre.** Bajo `HCurv` (`D27`, la hipótesis declarada de
acoplamiento materia↔estiramiento), la masa asociada al estiramiento que
`HCurv` exige es estrictamente mayor que la masa de un estiramiento
trivial (`s=1`) — la dilatación temporal (`D27.materia_dilata_el_tiempo`)
viene acompañada, no gratis, de más masa exigida. -/
theorem HCurv_exige_mas_masa (h : DeformacionTiempo.HCurv) (G : ℝ) (hG : 0 < G) :
    M G 1 < M G h.factor :=
  M_monotona hG h.estiramiento

#print axioms K_pos
#print axioms M_eq_s_mul_K
#print axioms M_monotona
#print axioms sDeRho_monotona
#print axioms sDeRho_M_eq_s
#print axioms HCurv_exige_mas_masa

end CurvaturaAcoplamiento

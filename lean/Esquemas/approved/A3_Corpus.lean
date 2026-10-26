import Mathlib

/-!
# A2. Plantilla de esquemas explícitos de dos niveles (diseño A)

Enunciados con `sorry`: pendientes de la aprobación de Carlos.

Un esquema explícito de dos niveles en la malla infinita `ℤ` es un stencil finito:
`uⁿ⁺¹_j = Σ_{k ∈ S} a_k · uⁿ_{j+k}`. Los parámetros del esquema (`r = α·Δt/Δx²`, `ν = c·Δt/Δx`)
van dentro de los coeficientes. Con esta plantilla, un esquema que proponga el agente es un dato
(`S` y `a`), y lo que hay que probar de él tiene siempre la misma forma.

Qué hay aquí:
- `paso_modo`: el puente, probado una sola vez para todo esquema: los modos de Fourier son
  autovectores y el autovalor es el símbolo `g(θ) = Σ a_k e^{ikθ}`.
- `simbolo_eq`: el símbolo en partes real e imaginaria (lo que se usa para probar `‖g‖ ≤ 1`).
- `vonNeumann_iff_sq`: von Neumann como desigualdad polinomial en senos y cosenos (la forma
  en que se prueba cada esquema concreto).
- `vonNeumann_momento_cero`: una condición necesaria (`|Σ a_k| ≤ 1`).
- `vonNeumann_de_positivo` y `pasoR_iterado_acotado`: un esquema de coeficientes no negativos que
  conserva constantes cumple von Neumann y además el principio del máximo discreto, que es
  estabilidad en norma del supremo para cualquier número de pasos (no solo para modos de Fourier).
- `laxWendroff_vonNeumann_iff` y el control `controlPositividad_falso`: Lax-Wendroff es estable
  si y solo si `|ν| ≤ 1`, y con `ν = 1/2` tiene un coeficiente negativo; la positividad es
  suficiente pero no necesaria.

Alcance: von Neumann en `ℤ` con coeficientes constantes. No hay aquí fronteras, coeficientes
variables ni el puente von Neumann ⇒ estabilidad en ℓ² (Parseval discreto); la consistencia por
momentos tiene su definición (`momento`) pero su puente con el error de truncamiento (Taylor) queda
para otra tanda.
-/

namespace PrometeoLean.Esquemas

open Complex

/-- Esquema explícito de dos niveles en `ℤ`: soporte finito `S` y coeficientes `a`. -/
structure Esquema where
  /-- Los desplazamientos del stencil. -/
  S : Finset ℤ
  /-- Los coeficientes (fuera de `S` no se usan). -/
  a : ℤ → ℝ

namespace Esquema

/-- Un paso del esquema sobre una malla compleja: `(E u)_j = Σ_{k ∈ S} a_k · u_{j+k}`. -/
noncomputable def paso (E : Esquema) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun j => ∑ k ∈ E.S, (E.a k : ℂ) * u (j + k)

/-- Un paso del esquema sobre una malla real. -/
noncomputable def pasoR (E : Esquema) (u : ℤ → ℝ) : ℤ → ℝ :=
  fun j => ∑ k ∈ E.S, E.a k * u (j + k)

/-- El símbolo (factor de amplificación): `g(θ) = Σ_{k ∈ S} a_k · e^{i·k·θ}`. -/
noncomputable def simbolo (E : Esquema) (θ : ℝ) : ℂ :=
  ∑ k ∈ E.S, (E.a k : ℂ) * Complex.exp (((k : ℝ) * θ : ℝ) * I)

/-- El momento `m` del stencil: `Σ_{k ∈ S} a_k · k^m`. -/
noncomputable def momento (E : Esquema) (m : ℕ) : ℝ :=
  ∑ k ∈ E.S, E.a k * (k : ℝ) ^ m

/-- Condición de von Neumann: `‖g(θ)‖ ≤ 1` para todo `θ`. -/
def vonNeumann (E : Esquema) : Prop :=
  ∀ θ : ℝ, ‖E.simbolo θ‖ ≤ 1

/-- Esquema positivo: coeficientes no negativos y conservación de constantes (`Σ a_k = 1`). -/
def Positivo (E : Esquema) : Prop :=
  (∀ k ∈ E.S, 0 ≤ E.a k) ∧ E.momento 0 = 1

/-- **A2.0 (puente).** Para todo esquema, el modo de Fourier `j ↦ exp(i·j·θ)` es autovector del
paso con autovalor `E.simbolo θ`. -/
theorem paso_modo (E : Esquema) (θ : ℝ) (j : ℤ) :
    E.paso (fun k => Complex.exp (((k : ℝ) * θ : ℝ) * I)) j
      = E.simbolo θ * Complex.exp (((j : ℝ) * θ : ℝ) * I) := by
  sorry

/-- **A2.1.** El símbolo en partes real e imaginaria. -/
theorem simbolo_eq (E : Esquema) (θ : ℝ) :
    E.simbolo θ = ((∑ k ∈ E.S, E.a k * Real.cos ((k : ℝ) * θ) : ℝ) : ℂ)
      + ((∑ k ∈ E.S, E.a k * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * I := by
  sorry

/-- **A2.2′ (forma polinomial).** Von Neumann equivale a una desigualdad en senos y cosenos:
`(Σ a_k cos kθ)² + (Σ a_k sin kθ)² ≤ 1` para todo `θ`. -/
theorem vonNeumann_iff_sq (E : Esquema) :
    E.vonNeumann ↔ ∀ θ : ℝ, (∑ k ∈ E.S, E.a k * Real.cos ((k : ℝ) * θ)) ^ 2
      + (∑ k ∈ E.S, E.a k * Real.sin ((k : ℝ) * θ)) ^ 2 ≤ 1 := by
  sorry

/-- **A2.2 (necesaria).** Si el esquema cumple von Neumann, entonces `|Σ a_k| ≤ 1`. -/
theorem vonNeumann_momento_cero (E : Esquema) (h : E.vonNeumann) : |E.momento 0| ≤ 1 := by
  sorry

/-- **A2.3.** Un esquema positivo cumple von Neumann. -/
theorem vonNeumann_de_positivo (E : Esquema) (h : E.Positivo) : E.vonNeumann := by
  sorry

/-- **A2.4 (principio del máximo, un paso).** Si `E` es positivo y `|u_j| ≤ M` para todo `j`,
entonces `|(E u)_j| ≤ M` para todo `j`. -/
theorem pasoR_acotado (E : Esquema) (h : E.Positivo) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |E.pasoR u j| ≤ M := by
  sorry

/-- **A2.5 (estabilidad en norma del supremo).** Lo mismo para `n` pasos, con la misma cota. -/
theorem pasoR_iterado_acotado (E : Esquema) (h : E.Positivo) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (n : ℕ) (j : ℤ) : |(E.pasoR)^[n] u j| ≤ M := by
  sorry

end Esquema

/-- Lax-Wendroff para `u_t + c·u_x = 0`, con `ν = c·Δt/Δx`:
`uⁿ⁺¹_j = uⁿ_j - (ν/2)(uⁿ_{j+1} - uⁿ_{j-1}) + (ν²/2)(uⁿ_{j+1} - 2uⁿ_j + uⁿ_{j-1})`. -/
noncomputable def laxWendroff (ν : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then ν * (1 + ν) / 2 else if k = 0 then 1 - ν ^ 2
    else if k = 1 then -(ν * (1 - ν)) / 2 else 0

/-- **A2.6.** Lax-Wendroff cumple von Neumann si y solo si `|ν| ≤ 1`. -/
theorem laxWendroff_vonNeumann_iff (ν : ℝ) : (laxWendroff ν).vonNeumann ↔ |ν| ≤ 1 := by
  sorry

/-- **Control falso P.** «Todo esquema que cumple von Neumann es positivo». Falso: Lax-Wendroff con
`ν = 1/2` cumple von Neumann y tiene `a_1 = -1/8`. -/
def controlPositividad : Prop :=
  ∀ E : Esquema, E.vonNeumann → E.Positivo

/-- Refutación del control P. -/
theorem controlPositividad_falso : ¬ controlPositividad := by
  sorry

/-! ## A3. Corpus inicial de esquemas (diseño A)

Enunciados generados mecánicamente desde `esquemas_corpus_A3.json`; no se escriben a mano. -/

/-- **ftcs_calor.** FTCS para u_t = α·u_xx, con r = α·Δt/Δx². Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_ftcs_calor (r : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r else if k = 0 then 1 - 2 * r else if k = 1 then r else 0

/-- Momentos 0, 1 y 2 de `esq_ftcs_calor`. -/
theorem esq_ftcs_calor_momentos (r : ℝ) :
    (esq_ftcs_calor r).momento 0 = 1 ∧ (esq_ftcs_calor r).momento 1 = 0 ∧ (esq_ftcs_calor r).momento 2 = 2 * r := by
  sorry

/-- Región exacta de von Neumann de `esq_ftcs_calor`. -/
theorem esq_ftcs_calor_vonNeumann_iff (r : ℝ) : (esq_ftcs_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 2) := by
  sorry

/-- `esq_ftcs_calor` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_ftcs_calor_positivo (r : ℝ) (h : 0 ≤ r ∧ r ≤ 1 / 2) : (esq_ftcs_calor r).Positivo := by
  sorry

/-- La región «estable_sii» de `esq_ftcs_calor` no es vacía. -/
theorem esq_ftcs_calor_region_estable : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 := by
  sorry

/-- La región «positivo_si» de `esq_ftcs_calor` no es vacía. -/
theorem esq_ftcs_calor_region_positivo : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 := by
  sorry

/-- **upwind.** Upwind para u_t + c·u_x = 0 con c > 0, ν = c·Δt/Δx. Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_upwind (nu : ℝ) : Esquema where
  S := {-1, 0}
  a := fun k => if k = -1 then nu else if k = 0 then 1 - nu else 0

/-- Momentos 0, 1 y 2 de `esq_upwind`. -/
theorem esq_upwind_momentos (nu : ℝ) :
    (esq_upwind nu).momento 0 = 1 ∧ (esq_upwind nu).momento 1 = -nu ∧ (esq_upwind nu).momento 2 = nu := by
  sorry

/-- Región exacta de von Neumann de `esq_upwind`. -/
theorem esq_upwind_vonNeumann_iff (nu : ℝ) : (esq_upwind nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 1) := by
  sorry

/-- `esq_upwind` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_upwind_positivo (nu : ℝ) (h : 0 ≤ nu ∧ nu ≤ 1) : (esq_upwind nu).Positivo := by
  sorry

/-- La región «estable_sii» de `esq_upwind` no es vacía. -/
theorem esq_upwind_region_estable : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 := by
  sorry

/-- La región «positivo_si» de `esq_upwind` no es vacía. -/
theorem esq_upwind_region_positivo : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 := by
  sorry

/-- **downwind.** Downwind (diferencia hacia adelante) para u_t + c·u_x = 0. Origen: control falso. -/
noncomputable def esq_downwind (nu : ℝ) : Esquema where
  S := {0, 1}
  a := fun k => if k = 0 then 1 + nu else if k = 1 then -nu else 0

/-- Momentos 0, 1 y 2 de `esq_downwind`. -/
theorem esq_downwind_momentos (nu : ℝ) :
    (esq_downwind nu).momento 0 = 1 ∧ (esq_downwind nu).momento 1 = -nu ∧ (esq_downwind nu).momento 2 = -nu := by
  sorry

/-- **Control.** `esq_downwind` no cumple von Neumann si 0 < nu. -/
theorem esq_downwind_inestable (nu : ℝ) (h : 0 < nu) : ¬ (esq_downwind nu).vonNeumann := by
  sorry

/-- La región «inestable_si» de `esq_downwind` no es vacía. -/
theorem esq_downwind_region_inestable : ∃ nu : ℝ, 0 < nu := by
  sorry

/-- **ftcs_adveccion.** FTCS centrado para u_t + c·u_x = 0. Origen: control falso. -/
noncomputable def esq_ftcs_adveccion (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then nu / 2 else if k = 0 then 1 else if k = 1 then -nu / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_ftcs_adveccion`. -/
theorem esq_ftcs_adveccion_momentos (nu : ℝ) :
    (esq_ftcs_adveccion nu).momento 0 = 1 ∧ (esq_ftcs_adveccion nu).momento 1 = -nu ∧ (esq_ftcs_adveccion nu).momento 2 = 0 := by
  sorry

/-- **Control.** `esq_ftcs_adveccion` no cumple von Neumann si nu ≠ 0. -/
theorem esq_ftcs_adveccion_inestable (nu : ℝ) (h : nu ≠ 0) : ¬ (esq_ftcs_adveccion nu).vonNeumann := by
  sorry

/-- La región «inestable_si» de `esq_ftcs_adveccion` no es vacía. -/
theorem esq_ftcs_adveccion_region_inestable : ∃ nu : ℝ, nu ≠ 0 := by
  sorry

/-- **lax_friedrichs.** Lax-Friedrichs para u_t + c·u_x = 0. Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_lax_friedrichs (nu : ℝ) : Esquema where
  S := {-1, 1}
  a := fun k => if k = -1 then (1 + nu) / 2 else if k = 1 then (1 - nu) / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_lax_friedrichs`. -/
theorem esq_lax_friedrichs_momentos (nu : ℝ) :
    (esq_lax_friedrichs nu).momento 0 = 1 ∧ (esq_lax_friedrichs nu).momento 1 = -nu ∧ (esq_lax_friedrichs nu).momento 2 = 1 := by
  sorry

/-- Región exacta de von Neumann de `esq_lax_friedrichs`. -/
theorem esq_lax_friedrichs_vonNeumann_iff (nu : ℝ) : (esq_lax_friedrichs nu).vonNeumann ↔ (-1 ≤ nu ∧ nu ≤ 1) := by
  sorry

/-- `esq_lax_friedrichs` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_lax_friedrichs_positivo (nu : ℝ) (h : -1 ≤ nu ∧ nu ≤ 1) : (esq_lax_friedrichs nu).Positivo := by
  sorry

/-- La región «estable_sii» de `esq_lax_friedrichs` no es vacía. -/
theorem esq_lax_friedrichs_region_estable : ∃ nu : ℝ, -1 ≤ nu ∧ nu ≤ 1 := by
  sorry

/-- La región «positivo_si» de `esq_lax_friedrichs` no es vacía. -/
theorem esq_lax_friedrichs_region_positivo : ∃ nu : ℝ, -1 ≤ nu ∧ nu ≤ 1 := by
  sorry

/-- **beam_warming.** Beam-Warming (upwind de segundo orden) para u_t + c·u_x = 0. Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_beam_warming (nu : ℝ) : Esquema where
  S := {-2, -1, 0}
  a := fun k => if k = -2 then nu * (nu - 1) / 2 else if k = -1 then nu * (2 - nu) else if k = 0 then (1 - nu) * (2 - nu) / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_beam_warming`. -/
theorem esq_beam_warming_momentos (nu : ℝ) :
    (esq_beam_warming nu).momento 0 = 1 ∧ (esq_beam_warming nu).momento 1 = -nu ∧ (esq_beam_warming nu).momento 2 = nu ^ 2 := by
  sorry

/-- Región exacta de von Neumann de `esq_beam_warming`. -/
theorem esq_beam_warming_vonNeumann_iff (nu : ℝ) : (esq_beam_warming nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 2) := by
  sorry

/-- La región «estable_sii» de `esq_beam_warming` no es vacía. -/
theorem esq_beam_warming_region_estable : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 2 := by
  sorry

/-- **ftcs_conv_dif.** FTCS para u_t + c·u_x = α·u_xx (advección centrada), con r = α·Δt/Δx² y ν = c·Δt/Δx; es el esquema del FD del cuaderno de PINNs. Origen: cuaderno Framework_PINN_EspacioTemporal (tarea 0). -/
noncomputable def esq_ftcs_conv_dif (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu / 2 else if k = 0 then 1 - 2 * r else if k = 1 then r - nu / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_ftcs_conv_dif`. -/
theorem esq_ftcs_conv_dif_momentos (r : ℝ) (nu : ℝ) :
    (esq_ftcs_conv_dif r nu).momento 0 = 1 ∧ (esq_ftcs_conv_dif r nu).momento 1 = -nu ∧ (esq_ftcs_conv_dif r nu).momento 2 = 2 * r := by
  sorry

/-- Región exacta de von Neumann de `esq_ftcs_conv_dif`. -/
theorem esq_ftcs_conv_dif_vonNeumann_iff (r : ℝ) (nu : ℝ) : (esq_ftcs_conv_dif r nu).vonNeumann ↔ (nu ^ 2 ≤ 2 * r ∧ 2 * r ≤ 1) := by
  sorry

/-- `esq_ftcs_conv_dif` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_ftcs_conv_dif_positivo (r : ℝ) (nu : ℝ) (h : nu ≤ 2 * r ∧ -nu ≤ 2 * r ∧ r ≤ 1 / 2) : (esq_ftcs_conv_dif r nu).Positivo := by
  sorry

/-- La región «estable_sii» de `esq_ftcs_conv_dif` no es vacía. -/
theorem esq_ftcs_conv_dif_region_estable : ∃ r nu : ℝ, nu ^ 2 ≤ 2 * r ∧ 2 * r ≤ 1 := by
  sorry

/-- La región «positivo_si» de `esq_ftcs_conv_dif` no es vacía. -/
theorem esq_ftcs_conv_dif_region_positivo : ∃ r nu : ℝ, nu ≤ 2 * r ∧ -nu ≤ 2 * r ∧ r ≤ 1 / 2 := by
  sorry

end PrometeoLean.Esquemas

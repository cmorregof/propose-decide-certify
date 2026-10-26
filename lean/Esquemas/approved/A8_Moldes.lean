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


/-! ## A4. Consistencia y convergencia (diseño A)

Enunciados con `sorry`: pendientes de la aprobación de Carlos.

- `Esquema.taylor`: el puente entre momentos y error de truncamiento (Taylor de orden `n`, válido
  para cualquier esquema): `|Σ a_k f(x+kh) − Σ_{m≤n} M_m hᵐ/m! f⁽ᵐ⁾(x)| ≤ (Σ|a_k||k|ⁿ⁺¹)|h|ⁿ⁺¹K/(n+1)!`.
- `Esquema.error_positivo`: estabilidad + error local ⇒ error global (Lax para esquemas positivos, en
  norma del supremo): si `eⁿ⁺¹ = E eⁿ + δⁿ` y `|δⁿ_j| ≤ ε`, entonces `|eⁿ_j| ≤ |e⁰| + n·ε`.
- `esq_ftcs_calor_consistencia`: FTCS es consistente de orden 2 en espacio.
- `esq_ftcs_calor_converge`: convergencia de FTCS para `u_t = α·u_xx` en toda la recta, con error
  `n·Δt·(Δt·Kₜ/2 + α·Δx²·Kₓ/12)`.

Alcance: problema de Cauchy en la recta (sin fronteras), solución clásica con cotas de `∂ₜ²u` y `∂ₓ⁴u`
para `t ≥ 0` (en toda la recta en `x`); las derivadas se toman de las secciones `t ↦ u t x` y `x ↦ u t x`.
-/

namespace Esquema

open Nat in
/-- **A4.1 (puente de consistencia).** Para todo esquema y toda `f` de clase `Cⁿ⁺¹` con
`|f⁽ⁿ⁺¹⁾| ≤ K`, el paso aplicado a `f` difiere de la serie de momentos truncada en a lo sumo
`(Σ |a_k| |k|ⁿ⁺¹) |h|ⁿ⁺¹ K / (n+1)!`. -/
theorem taylor (E : Esquema) (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1) f) (K : ℝ)
    (hK : ∀ y, |iteratedDeriv (n + 1) f y| ≤ K) (x h : ℝ) :
    |∑ k ∈ E.S, E.a k * f (x + k * h)
        - ∑ m ∈ Finset.range (n + 1), E.momento m * h ^ m / (m ! : ℝ) * iteratedDeriv m f x|
      ≤ (∑ k ∈ E.S, |E.a k| * |(k : ℝ)| ^ (n + 1)) * |h| ^ (n + 1) * K / ((n + 1) ! : ℝ) := by
  sorry

/-- **A4.2 (Lax para esquemas positivos).** Si `E` es positivo y el error cumple
`eⁿ⁺¹_j = (E eⁿ)_j + δⁿ_j` con `|e⁰_j| ≤ ε₀` y `|δⁿ_j| ≤ ε`, entonces `|eⁿ_j| ≤ ε₀ + n·ε`. -/
theorem error_positivo (E : Esquema) (hE : E.Positivo) (e δ : ℕ → ℤ → ℝ) (ε₀ ε : ℝ)
    (he : ∀ n j, e (n + 1) j = E.pasoR (e n) j + δ n j)
    (h0 : ∀ j, |e 0 j| ≤ ε₀) (hδ : ∀ n j, |δ n j| ≤ ε) (n : ℕ) (j : ℤ) :
    |e n j| ≤ ε₀ + n * ε := by
  sorry

end Esquema

/-- **A4.3.** FTCS es consistente de orden 2 en espacio: si `f` es `C⁴` con `|f⁗| ≤ K` y `r ≥ 0`,
`|(E f)(x) − f(x) − r·h²·f''(x)| ≤ r·h⁴·K/12`. -/
theorem esq_ftcs_calor_consistencia (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (K : ℝ)
    (hK : ∀ y, |iteratedDeriv 4 f y| ≤ K) (x h : ℝ) :
    |∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * f (x + k * h)
        - (f x + r * h ^ 2 * iteratedDeriv 2 f x)| ≤ r * h ^ 4 * K / 12 := by
  sorry

/-- **A4.4 (convergencia de FTCS).** Sea `u` solución clásica de `u_t = α·u_xx` en `ℝ × ℝ`, con
`|∂ₜ²u| ≤ Kₜ` y `|∂ₓ⁴u| ≤ Kₓ` para `t ≥ 0` (por ejemplo `u = e^{-αt}·sin x`, con `Kₜ = α²` y `Kₓ = 1`),
y sea `V` la solución de FTCS con `r = α·Δt/Δx² ≤ 1/2` que parte de
`u(0, ·)` en la malla. Entonces `|u(nΔt, jΔx) − Vⁿ_j| ≤ n·Δt·(Δt·Kₜ/2 + α·Δx²·Kₓ/12)`. -/
theorem esq_ftcs_calor_converge (u : ℝ → ℝ → ℝ) (α Δt Δx Kt Kx : ℝ)
    (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hΔx : Δx ≠ 0) (hr : α * Δt / Δx ^ 2 ≤ 1 / 2)
    (hx : ∀ t, ContDiff ℝ 4 (u t)) (ht : ∀ x, ContDiff ℝ 2 (fun t => u t x))
    (hEDP : ∀ t x, deriv (fun s => u s x) t = α * iteratedDeriv 2 (u t) x)
    (hKt : ∀ t, 0 ≤ t → ∀ x, |iteratedDeriv 2 (fun s => u s x) t| ≤ Kt)
    (hKx : ∀ t, 0 ≤ t → ∀ x, |iteratedDeriv 4 (u t) x| ≤ Kx)
    (V : ℕ → ℤ → ℝ) (hV : ∀ n j, V (n + 1) j = (esq_ftcs_calor (α * Δt / Δx ^ 2)).pasoR (V n) j)
    (hV0 : ∀ j, V 0 j = u 0 (j * Δx)) (n : ℕ) (j : ℤ) :
    |u (n * Δt) (j * Δx) - V n j| ≤ n * Δt * (Δt * Kt / 2 + α * Δx ^ 2 * Kx / 12) := by
  sorry

/-- **A4.5 (A4.4 no es vacía).** Para la solución `u(t, x) = e^{-αt}·sin x` y FTCS que parte de
`V⁰_j = sin(jΔx)` con `α·Δt/Δx² ≤ 1/2`: `|u(nΔt, jΔx) − Vⁿ_j| ≤ n·Δt·(Δt·α²/2 + α·Δx²/12)`. -/
theorem esq_ftcs_calor_converge_seno (α Δt Δx : ℝ) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hΔx : Δx ≠ 0)
    (hr : α * Δt / Δx ^ 2 ≤ 1 / 2) (V : ℕ → ℤ → ℝ)
    (hV : ∀ n j, V (n + 1) j = (esq_ftcs_calor (α * Δt / Δx ^ 2)).pasoR (V n) j)
    (hV0 : ∀ j, V 0 j = Real.sin (j * Δx)) (n : ℕ) (j : ℤ) :
    |Real.exp (-α * (n * Δt)) * Real.sin (j * Δx) - V n j|
      ≤ n * Δt * (Δt * α ^ 2 / 2 + α * Δx ^ 2 / 12) := by
  sorry

/-! ## A8. Moldes físicos y consistencia (diseño A: la cadena problema → modelo → esquema)

Enunciados con `sorry`: pendientes de la aprobación de Carlos.

Un *molde* es una EDP lineal de coeficientes constantes en la recta, `u_t = Σ_{m ≤ orden} cₘ ∂ₓᵐ u`. Con la
convención `u_t + v·u_x = α·u_xx + λ·u` es `c₀ = λ`, `c₁ = −v`, `c₂ = α`. El agente selector escoge un molde del
catálogo de abajo; lo que este archivo certifica es lo que se puede certificar después de esa elección:

- `Esquema.Consistente1 E P k h n`: los momentos de `E` cumplen `Mₘ hᵐ/m! = δ_{m0} + k·cₘ` para `m ≤ n`
  (paso de tiempo `k`, malla `h`; primer orden en el tiempo);
- `Esquema.Consistente2 E P k h n`: lo mismo con `+ k²/2·(P²)ₘ` (segundo orden en el tiempo, tipo Lax–Wendroff);
- `Esquema.consistencia1` y `Esquema.consistencia2` (el puente): si el esquema es consistente con `P` hasta `n` y
  `orden P ≤ n`, entonces para toda `f` de clase `Cⁿ⁺¹` con `|f⁽ⁿ⁺¹⁾| ≤ K`
  `|Σ a_j f(x + j h) − (f(x) + k (P f)(x) [+ k²/2 (P² f)ₙ(x)])| ≤ (Σ |a_j| |j|ⁿ⁺¹) |h|ⁿ⁺¹ K/(n+1)!`,
  donde `(P² f)ₙ` es la parte de orden `≤ n` de `P²` aplicado a `f`. Sale del Taylor de A4.

Alcance y advertencias:
- `Consistente1/2` es una *igualdad exacta de momentos*: el paso reproduce exactamente `I + kP [+ k²/2·P²]` sobre los
  polinomios de grado `≤ n`. Con `n ≥ orden P` implica la consistencia usual (no hay falsos positivos), pero es más
  fuerte: un esquema consistente de primer orden puede no cumplirla. Ejemplo: upwind con difusión central es
  consistente con advección–difusión en el sentido de los libros y falla `Consistente1` para todo `n ≥ 2` (su
  difusión numérica `|v|·h/2` no cuadra exactamente). Un «no» aquí no dice que el esquema sea inconsistente.
- Con `n < orden P` la afirmación no ve el término más alto del molde y no sirve; el generador exige `n ≥ orden P`
  (orden 1 en el tiempo) y `n ≥ 2·orden P` (orden 2, para que `(P²)ₘ` entre completo; con `n` menor «segundo orden en
  el tiempo» no estaría certificado).
- La cota del puente es sobre el paso entero; el error de truncamiento local por unidad de tiempo es esa cota dividida
  por `k`.
- Es la consistencia espacial del paso (lo que el paso hace con una función suave frente a lo que hace el operador del
  molde); la parte temporal (`u(t+k) = u + kPu + k²/2 P²u + O(k³)` para la solución) no se formaliza aquí.
- Los moldes del catálogo están definidos para todo valor de sus coeficientes; las restricciones físicas
  (`α ≥ 0`, `λ ≤ 0`) son del catálogo del selector y no se imponen en los enunciados (que valen para todo valor real).
  Los moldes no lineales quedan fuera.
-/

/-- Un molde físico: una EDP lineal de coeficientes constantes `u_t = Σ_{m ≤ orden} cₘ ∂ₓᵐ u`. -/
structure Molde where
  /-- El orden más alto de derivada espacial. -/
  orden : ℕ
  /-- Los coeficientes `cₘ` (los de índice mayor que `orden` no se usan). -/
  c : ℕ → ℝ

namespace Molde

/-- El coeficiente `m` del molde, cero por encima del orden. -/
noncomputable def coef (P : Molde) (m : ℕ) : ℝ := if m ≤ P.orden then P.c m else 0

/-- El operador espacial del molde: `(P f)(x) = Σ_{m ≤ orden} cₘ f⁽ᵐ⁾(x)`. -/
noncomputable def op (P : Molde) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (P.orden + 1), P.coef m * iteratedDeriv m f x

/-- Los coeficientes del operador al cuadrado: `(P²)ₘ = Σ_{i + j = m} cᵢ cⱼ`. -/
noncomputable def coef2 (P : Molde) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), P.coef i * P.coef (m - i)

/-- La parte de orden `≤ n` de `P²` aplicado a `f`: `Σ_{m ≤ n} (P²)ₘ f⁽ᵐ⁾(x)`. -/
noncomputable def op2 (P : Molde) (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), P.coef2 m * iteratedDeriv m f x

end Molde

/-- Catálogo: calor, `u_t = α u_xx`. -/
noncomputable def molde_calor (alpha : ℝ) : Molde := ⟨2, fun m => if m = 2 then alpha else 0⟩

/-- Catálogo: advección, `u_t + v u_x = 0`. -/
noncomputable def molde_adveccion (v : ℝ) : Molde := ⟨1, fun m => if m = 1 then -v else 0⟩

/-- Catálogo: advección–difusión, `u_t + v u_x = α u_xx`. -/
noncomputable def molde_adveccion_difusion (v alpha : ℝ) : Molde :=
  ⟨2, fun m => if m = 1 then -v else if m = 2 then alpha else 0⟩

/-- Catálogo: reacción–difusión lineal, `u_t = α u_xx + λ u` (el selector usa `λ < 0`). -/
noncomputable def molde_reaccion_difusion (lam alpha : ℝ) : Molde :=
  ⟨2, fun m => if m = 0 then lam else if m = 2 then alpha else 0⟩

/-- Catálogo: advección–reacción–difusión lineal, `u_t + v u_x = α u_xx + λ u` (el selector usa `λ < 0`). -/
noncomputable def molde_adveccion_reaccion_difusion (v lam alpha : ℝ) : Molde :=
  ⟨2, fun m => if m = 0 then lam else if m = 1 then -v else if m = 2 then alpha else 0⟩

namespace Esquema

/-- Consistencia de primer orden en el tiempo con el molde `P`, hasta el momento `n`. -/
def Consistente1 (E : Esquema) (P : Molde) (k h : ℝ) (n : ℕ) : Prop :=
  ∀ m ≤ n, E.momento m * h ^ m / (Nat.factorial m : ℝ) = (if m = 0 then 1 else 0) + k * P.coef m

/-- Consistencia de segundo orden en el tiempo (tipo Lax–Wendroff) con el molde `P`, hasta el momento `n`. -/
def Consistente2 (E : Esquema) (P : Molde) (k h : ℝ) (n : ℕ) : Prop :=
  ∀ m ≤ n, E.momento m * h ^ m / (Nat.factorial m : ℝ)
    = (if m = 0 then 1 else 0) + k * P.coef m + k ^ 2 / 2 * P.coef2 m

open Nat in
/-- **A8.1 (puente de consistencia, primer orden).** -/
theorem consistencia1 (E : Esquema) (P : Molde) (k h : ℝ) (n : ℕ) (hc : E.Consistente1 P k h n)
    (hn : P.orden ≤ n) (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1) f) (K : ℝ)
    (hK : ∀ y, |iteratedDeriv (n + 1) f y| ≤ K) (x : ℝ) :
    |∑ j ∈ E.S, E.a j * f (x + j * h) - (f x + k * P.op f x)|
      ≤ (∑ j ∈ E.S, |E.a j| * |(j : ℝ)| ^ (n + 1)) * |h| ^ (n + 1) * K / ((n + 1) ! : ℝ) := by
  sorry

open Nat in
/-- **A8.2 (puente de consistencia, segundo orden en el tiempo).** -/
theorem consistencia2 (E : Esquema) (P : Molde) (k h : ℝ) (n : ℕ) (hc : E.Consistente2 P k h n)
    (hn : P.orden ≤ n) (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1) f) (K : ℝ)
    (hK : ∀ y, |iteratedDeriv (n + 1) f y| ≤ K) (x : ℝ) :
    |∑ j ∈ E.S, E.a j * f (x + j * h) - (f x + k * P.op f x + k ^ 2 / 2 * P.op2 n f x)|
      ≤ (∑ j ∈ E.S, |E.a j| * |(j : ℝ)| ^ (n + 1)) * |h| ^ (n + 1) * K / ((n + 1) ! : ℝ) := by
  sorry

end Esquema

/-! ## A8. Consistencia de esquemas con los moldes físicos (diseño A, cadena problema → modelo → esquema)

Enunciados generados mecánicamente desde `esquemas_moldes_A8.json`; no se escriben a mano. -/

/-- **m_ftcs_calor.** FTCS para la difusión, r = α·Δt/Δx². Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_ftcs_calor (r : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r else if k = 0 then 1 - 2 * r else if k = 1 then r else 0

/-- Momentos 0, 1 y 2 de `esq_m_ftcs_calor`. -/
theorem esq_m_ftcs_calor_momentos (r : ℝ) :
    (esq_m_ftcs_calor r).momento 0 = 1 ∧ (esq_m_ftcs_calor r).momento 1 = 0 ∧ (esq_m_ftcs_calor r).momento 2 = 2 * r := by
  sorry

/-- **Decidir m_ftcs_calor/a, sí.** El paso de `esq_m_ftcs_calor` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `calor`) sobre los polinomios de grado ≤ 4: la identidad de momentos `Consistente2` vale para todo m ≤ 4. -/
theorem esq_m_ftcs_calor_decide_a_si : ∀ alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_calor (alpha * dt / dx ^ 2)).Consistente2 (molde_calor alpha) dt dx 4 := by
  sorry

/-- **Decidir m_ftcs_calor/a, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 4 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_calor_decide_a_no : ∃ alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_calor (alpha * dt / dx ^ 2)).Consistente2 (molde_calor alpha) dt dx 4 := by
  sorry

/-- **Decidir m_ftcs_calor/b, sí.** El paso de `esq_m_ftcs_calor` reproduce exactamente `I + dt·P` (P = molde `calor`) sobre los polinomios de grado ≤ 3: la identidad de momentos `Consistente1` vale para todo m ≤ 3. -/
theorem esq_m_ftcs_calor_decide_b_si : ∀ alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_calor (alpha * dt / dx ^ 2)).Consistente1 (molde_calor alpha) dt dx 3 := by
  sorry

/-- **Decidir m_ftcs_calor/b, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 3 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_calor_decide_b_no : ∃ alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_calor (alpha * dt / dx ^ 2)).Consistente1 (molde_calor alpha) dt dx 3 := by
  sorry

/-- **m_upwind.** Upwind para la advección, ν = v·Δt/Δx. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_upwind (nu : ℝ) : Esquema where
  S := {-1, 0}
  a := fun k => if k = -1 then nu else if k = 0 then 1 - nu else 0

/-- Momentos 0, 1 y 2 de `esq_m_upwind`. -/
theorem esq_m_upwind_momentos (nu : ℝ) :
    (esq_m_upwind nu).momento 0 = 1 ∧ (esq_m_upwind nu).momento 1 = -nu ∧ (esq_m_upwind nu).momento 2 = nu := by
  sorry

/-- **Decidir m_upwind/a, sí.** El paso de `esq_m_upwind` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `adveccion`) sobre los polinomios de grado ≤ 2: la identidad de momentos `Consistente2` vale para todo m ≤ 2. -/
theorem esq_m_upwind_decide_a_si : ∀ v dt dx : ℝ, dx ≠ 0 → (esq_m_upwind (v * dt / dx)).Consistente2 (molde_adveccion v) dt dx 2 := by
  sorry

/-- **Decidir m_upwind/a, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 2 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_upwind_decide_a_no : ∃ v dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_upwind (v * dt / dx)).Consistente2 (molde_adveccion v) dt dx 2 := by
  sorry

/-- **Decidir m_upwind/b, sí.** El paso de `esq_m_upwind` reproduce exactamente `I + dt·P` (P = molde `adveccion`) sobre los polinomios de grado ≤ 1: la identidad de momentos `Consistente1` vale para todo m ≤ 1. -/
theorem esq_m_upwind_decide_b_si : ∀ v dt dx : ℝ, dx ≠ 0 → (esq_m_upwind (v * dt / dx)).Consistente1 (molde_adveccion v) dt dx 1 := by
  sorry

/-- **Decidir m_upwind/b, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 1 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_upwind_decide_b_no : ∃ v dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_upwind (v * dt / dx)).Consistente1 (molde_adveccion v) dt dx 1 := by
  sorry

/-- **m_lax_wendroff.** Lax–Wendroff para la advección, ν = v·Δt/Δx. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_lax_wendroff (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then nu * (nu + 1) / 2 else if k = 0 then 1 - nu ^ 2 else if k = 1 then nu * (nu - 1) / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_m_lax_wendroff`. -/
theorem esq_m_lax_wendroff_momentos (nu : ℝ) :
    (esq_m_lax_wendroff nu).momento 0 = 1 ∧ (esq_m_lax_wendroff nu).momento 1 = -nu ∧ (esq_m_lax_wendroff nu).momento 2 = nu ^ 2 := by
  sorry

/-- **Decidir m_lax_wendroff/a, sí.** El paso de `esq_m_lax_wendroff` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `adveccion`) sobre los polinomios de grado ≤ 3: la identidad de momentos `Consistente2` vale para todo m ≤ 3. -/
theorem esq_m_lax_wendroff_decide_a_si : ∀ v dt dx : ℝ, dx ≠ 0 → (esq_m_lax_wendroff (v * dt / dx)).Consistente2 (molde_adveccion v) dt dx 3 := by
  sorry

/-- **Decidir m_lax_wendroff/a, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 3 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_lax_wendroff_decide_a_no : ∃ v dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_lax_wendroff (v * dt / dx)).Consistente2 (molde_adveccion v) dt dx 3 := by
  sorry

/-- **Decidir m_lax_wendroff/b, sí.** El paso de `esq_m_lax_wendroff` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `adveccion`) sobre los polinomios de grado ≤ 2: la identidad de momentos `Consistente2` vale para todo m ≤ 2. -/
theorem esq_m_lax_wendroff_decide_b_si : ∀ v dt dx : ℝ, dx ≠ 0 → (esq_m_lax_wendroff (v * dt / dx)).Consistente2 (molde_adveccion v) dt dx 2 := by
  sorry

/-- **Decidir m_lax_wendroff/b, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 2 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_lax_wendroff_decide_b_no : ∃ v dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_lax_wendroff (v * dt / dx)).Consistente2 (molde_adveccion v) dt dx 2 := by
  sorry

/-- **m_ftcs_conv_dif.** FTCS con advección centrada para la advección–difusión. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_ftcs_conv_dif (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu / 2 else if k = 0 then 1 - 2 * r else if k = 1 then r - nu / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_m_ftcs_conv_dif`. -/
theorem esq_m_ftcs_conv_dif_momentos (r : ℝ) (nu : ℝ) :
    (esq_m_ftcs_conv_dif r nu).momento 0 = 1 ∧ (esq_m_ftcs_conv_dif r nu).momento 1 = -nu ∧ (esq_m_ftcs_conv_dif r nu).momento 2 = 2 * r := by
  sorry

/-- **Decidir m_ftcs_conv_dif/a, sí.** El paso de `esq_m_ftcs_conv_dif` reproduce exactamente `I + dt·P` (P = molde `adveccion_difusion`) sobre los polinomios de grado ≤ 2: la identidad de momentos `Consistente1` vale para todo m ≤ 2. -/
theorem esq_m_ftcs_conv_dif_decide_a_si : ∀ v alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_conv_dif (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente1 (molde_adveccion_difusion v alpha) dt dx 2 := by
  sorry

/-- **Decidir m_ftcs_conv_dif/a, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 2 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_conv_dif_decide_a_no : ∃ v alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_conv_dif (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente1 (molde_adveccion_difusion v alpha) dt dx 2 := by
  sorry

/-- **Decidir m_ftcs_conv_dif/b, sí.** El paso de `esq_m_ftcs_conv_dif` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `adveccion_difusion`) sobre los polinomios de grado ≤ 4: la identidad de momentos `Consistente2` vale para todo m ≤ 4. -/
theorem esq_m_ftcs_conv_dif_decide_b_si : ∀ v alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_conv_dif (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente2 (molde_adveccion_difusion v alpha) dt dx 4 := by
  sorry

/-- **Decidir m_ftcs_conv_dif/b, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 4 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_conv_dif_decide_b_no : ∃ v alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_conv_dif (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente2 (molde_adveccion_difusion v alpha) dt dx 4 := by
  sorry

/-- **m_lw_difusion.** Lax–Wendroff con difusión central para la advección–difusión. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_lw_difusion (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu * (nu + 1) / 2 else if k = 0 then 1 - 2 * r - nu ^ 2 else if k = 1 then r + nu * (nu - 1) / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_m_lw_difusion`. -/
theorem esq_m_lw_difusion_momentos (r : ℝ) (nu : ℝ) :
    (esq_m_lw_difusion r nu).momento 0 = 1 ∧ (esq_m_lw_difusion r nu).momento 1 = -nu ∧ (esq_m_lw_difusion r nu).momento 2 = 2 * r + nu ^ 2 := by
  sorry

/-- **Decidir m_lw_difusion/a, sí.** El paso de `esq_m_lw_difusion` reproduce exactamente `I + dt·P` (P = molde `adveccion_difusion`) sobre los polinomios de grado ≤ 2: la identidad de momentos `Consistente1` vale para todo m ≤ 2. -/
theorem esq_m_lw_difusion_decide_a_si : ∀ v alpha dt dx : ℝ, dx ≠ 0 → (esq_m_lw_difusion (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente1 (molde_adveccion_difusion v alpha) dt dx 2 := by
  sorry

/-- **Decidir m_lw_difusion/a, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 2 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_lw_difusion_decide_a_no : ∃ v alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_lw_difusion (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente1 (molde_adveccion_difusion v alpha) dt dx 2 := by
  sorry

/-- **Decidir m_lw_difusion/b, sí.** El paso de `esq_m_lw_difusion` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `adveccion_difusion`) sobre los polinomios de grado ≤ 4: la identidad de momentos `Consistente2` vale para todo m ≤ 4. -/
theorem esq_m_lw_difusion_decide_b_si : ∀ v alpha dt dx : ℝ, dx ≠ 0 → (esq_m_lw_difusion (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente2 (molde_adveccion_difusion v alpha) dt dx 4 := by
  sorry

/-- **Decidir m_lw_difusion/b, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 4 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_lw_difusion_decide_b_no : ∃ v alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_lw_difusion (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente2 (molde_adveccion_difusion v alpha) dt dx 4 := by
  sorry

/-- **m_upwind_difusion.** Upwind con difusión central para la advección–difusión. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_upwind_difusion (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu else if k = 0 then 1 - 2 * r - nu else if k = 1 then r else 0

/-- Momentos 0, 1 y 2 de `esq_m_upwind_difusion`. -/
theorem esq_m_upwind_difusion_momentos (r : ℝ) (nu : ℝ) :
    (esq_m_upwind_difusion r nu).momento 0 = 1 ∧ (esq_m_upwind_difusion r nu).momento 1 = -nu ∧ (esq_m_upwind_difusion r nu).momento 2 = 2 * r + nu := by
  sorry

/-- **Decidir m_upwind_difusion/a, sí.** El paso de `esq_m_upwind_difusion` reproduce exactamente `I + dt·P` (P = molde `adveccion_difusion`) sobre los polinomios de grado ≤ 2: la identidad de momentos `Consistente1` vale para todo m ≤ 2. -/
theorem esq_m_upwind_difusion_decide_a_si : ∀ v alpha dt dx : ℝ, dx ≠ 0 → (esq_m_upwind_difusion (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente1 (molde_adveccion_difusion v alpha) dt dx 2 := by
  sorry

/-- **Decidir m_upwind_difusion/a, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 2 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_upwind_difusion_decide_a_no : ∃ v alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_upwind_difusion (alpha * dt / dx ^ 2) (v * dt / dx)).Consistente1 (molde_adveccion_difusion v alpha) dt dx 2 := by
  sorry

/-- **m_ftcs4_calor.** Diferencias centradas de cuarto orden y Euler explícito para la difusión. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_ftcs4_calor (r : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -r / 12 else if k = -1 then 4 * r / 3 else if k = 0 then 1 - 5 * r / 2 else if k = 1 then 4 * r / 3 else if k = 2 then -r / 12 else 0

/-- Momentos 0, 1 y 2 de `esq_m_ftcs4_calor`. -/
theorem esq_m_ftcs4_calor_momentos (r : ℝ) :
    (esq_m_ftcs4_calor r).momento 0 = 1 ∧ (esq_m_ftcs4_calor r).momento 1 = 0 ∧ (esq_m_ftcs4_calor r).momento 2 = 2 * r := by
  sorry

/-- **Decidir m_ftcs4_calor/a, sí.** El paso de `esq_m_ftcs4_calor` reproduce exactamente `I + dt·P` (P = molde `calor`) sobre los polinomios de grado ≤ 5: la identidad de momentos `Consistente1` vale para todo m ≤ 5. -/
theorem esq_m_ftcs4_calor_decide_a_si : ∀ alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs4_calor (alpha * dt / dx ^ 2)).Consistente1 (molde_calor alpha) dt dx 5 := by
  sorry

/-- **Decidir m_ftcs4_calor/a, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 5 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs4_calor_decide_a_no : ∃ alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs4_calor (alpha * dt / dx ^ 2)).Consistente1 (molde_calor alpha) dt dx 5 := by
  sorry

/-- **Decidir m_ftcs4_calor/b, sí.** El paso de `esq_m_ftcs4_calor` reproduce exactamente `I + dt·P` (P = molde `calor`) sobre los polinomios de grado ≤ 3: la identidad de momentos `Consistente1` vale para todo m ≤ 3. -/
theorem esq_m_ftcs4_calor_decide_b_si : ∀ alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs4_calor (alpha * dt / dx ^ 2)).Consistente1 (molde_calor alpha) dt dx 3 := by
  sorry

/-- **Decidir m_ftcs4_calor/b, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 3 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs4_calor_decide_b_no : ∃ alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs4_calor (alpha * dt / dx ^ 2)).Consistente1 (molde_calor alpha) dt dx 3 := by
  sorry

/-- **m_ftcs_reac_dif.** FTCS con reacción explícita para la reacción–difusión lineal, s = λ·Δt. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_ftcs_reac_dif (r : ℝ) (s : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r else if k = 0 then 1 - 2 * r + s else if k = 1 then r else 0

/-- Momentos 0, 1 y 2 de `esq_m_ftcs_reac_dif`. -/
theorem esq_m_ftcs_reac_dif_momentos (r : ℝ) (s : ℝ) :
    (esq_m_ftcs_reac_dif r s).momento 0 = 1 + s ∧ (esq_m_ftcs_reac_dif r s).momento 1 = 0 ∧ (esq_m_ftcs_reac_dif r s).momento 2 = 2 * r := by
  sorry

/-- **Decidir m_ftcs_reac_dif/a, sí.** El paso de `esq_m_ftcs_reac_dif` reproduce exactamente `I + dt·P + dt²/2·P²` (P = molde `reaccion_difusion`) sobre los polinomios de grado ≤ 4: la identidad de momentos `Consistente2` vale para todo m ≤ 4. -/
theorem esq_m_ftcs_reac_dif_decide_a_si : ∀ lam alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_reac_dif (alpha * dt / dx ^ 2) (lam * dt)).Consistente2 (molde_reaccion_difusion lam alpha) dt dx 4 := by
  sorry

/-- **Decidir m_ftcs_reac_dif/a, no.** La identidad de momentos `Consistente2` falla en algún m ≤ 4 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_reac_dif_decide_a_no : ∃ lam alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_reac_dif (alpha * dt / dx ^ 2) (lam * dt)).Consistente2 (molde_reaccion_difusion lam alpha) dt dx 4 := by
  sorry

/-- **Decidir m_ftcs_reac_dif/b, sí.** El paso de `esq_m_ftcs_reac_dif` reproduce exactamente `I + dt·P` (P = molde `reaccion_difusion`) sobre los polinomios de grado ≤ 3: la identidad de momentos `Consistente1` vale para todo m ≤ 3. -/
theorem esq_m_ftcs_reac_dif_decide_b_si : ∀ lam alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_reac_dif (alpha * dt / dx ^ 2) (lam * dt)).Consistente1 (molde_reaccion_difusion lam alpha) dt dx 3 := by
  sorry

/-- **Decidir m_ftcs_reac_dif/b, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 3 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_reac_dif_decide_b_no : ∃ lam alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_reac_dif (alpha * dt / dx ^ 2) (lam * dt)).Consistente1 (molde_reaccion_difusion lam alpha) dt dx 3 := by
  sorry

/-- **m_ftcs_adv_reac_dif.** FTCS con advección centrada y reacción explícita. Origen: A8 (26 oct 2026). -/
noncomputable def esq_m_ftcs_adv_reac_dif (r : ℝ) (nu : ℝ) (s : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu / 2 else if k = 0 then 1 - 2 * r + s else if k = 1 then r - nu / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_m_ftcs_adv_reac_dif`. -/
theorem esq_m_ftcs_adv_reac_dif_momentos (r : ℝ) (nu : ℝ) (s : ℝ) :
    (esq_m_ftcs_adv_reac_dif r nu s).momento 0 = 1 + s ∧ (esq_m_ftcs_adv_reac_dif r nu s).momento 1 = -nu ∧ (esq_m_ftcs_adv_reac_dif r nu s).momento 2 = 2 * r := by
  sorry

/-- **Decidir m_ftcs_adv_reac_dif/a, sí.** El paso de `esq_m_ftcs_adv_reac_dif` reproduce exactamente `I + dt·P` (P = molde `adveccion_reaccion_difusion`) sobre los polinomios de grado ≤ 2: la identidad de momentos `Consistente1` vale para todo m ≤ 2. -/
theorem esq_m_ftcs_adv_reac_dif_decide_a_si : ∀ v lam alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_adv_reac_dif (alpha * dt / dx ^ 2) (v * dt / dx) (lam * dt)).Consistente1 (molde_adveccion_reaccion_difusion v lam alpha) dt dx 2 := by
  sorry

/-- **Decidir m_ftcs_adv_reac_dif/a, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 2 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_adv_reac_dif_decide_a_no : ∃ v lam alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_adv_reac_dif (alpha * dt / dx ^ 2) (v * dt / dx) (lam * dt)).Consistente1 (molde_adveccion_reaccion_difusion v lam alpha) dt dx 2 := by
  sorry

/-- **Decidir m_ftcs_adv_reac_dif/b, sí.** El paso de `esq_m_ftcs_adv_reac_dif` reproduce exactamente `I + dt·P` (P = molde `adveccion_reaccion_difusion`) sobre los polinomios de grado ≤ 3: la identidad de momentos `Consistente1` vale para todo m ≤ 3. -/
theorem esq_m_ftcs_adv_reac_dif_decide_b_si : ∀ v lam alpha dt dx : ℝ, dx ≠ 0 → (esq_m_ftcs_adv_reac_dif (alpha * dt / dx ^ 2) (v * dt / dx) (lam * dt)).Consistente1 (molde_adveccion_reaccion_difusion v lam alpha) dt dx 3 := by
  sorry

/-- **Decidir m_ftcs_adv_reac_dif/b, no.** La identidad de momentos `Consistente1` falla en algún m ≤ 3 para algunos coeficientes y pasos (esto no dice que el esquema sea inconsistente en el sentido usual). -/
theorem esq_m_ftcs_adv_reac_dif_decide_b_no : ∃ v lam alpha dt dx : ℝ, dx ≠ 0 ∧ ¬ (esq_m_ftcs_adv_reac_dif (alpha * dt / dx ^ 2) (v * dt / dx) (lam * dt)).Consistente1 (molde_adveccion_reaccion_difusion v lam alpha) dt dx 3 := by
  sorry

end PrometeoLean.Esquemas

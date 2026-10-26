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

/-! ## A7. Nivel difícil: regiones exactas (decidir exacta) para 4 esquemas, y las formulaciones cuárticas de la región de Lax-Wendroff con difusión que propusieron Sonnet 5.5 y Haiku 5.5 en el lazo (caso 2)

Enunciados generados mecánicamente desde `esquemas_dificil_A7.json`; no se escriben a mano. -/

/-- **lw_difusion.** Lax-Wendroff con difusión central para u_t + c·u_x = α·u_xx, r = α·Δt/Δx², ν = c·Δt/Δx. Origen: nivel difícil del diseño A (25 oct 2026). -/
noncomputable def esq_lw_difusion (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu * (nu + 1) / 2 else if k = 0 then 1 - 2 * r - nu ^ 2 else if k = 1 then r + nu * (nu - 1) / 2 else 0

/-- Momentos 0, 1 y 2 de `esq_lw_difusion`. -/
theorem esq_lw_difusion_momentos (r : ℝ) (nu : ℝ) :
    (esq_lw_difusion r nu).momento 0 = 1 ∧ (esq_lw_difusion r nu).momento 1 = -nu ∧ (esq_lw_difusion r nu).momento 2 = 2 * r + nu ^ 2 := by
  sorry

/-- **Decidir exacta lw_difusion/a, sí.** `esq_lw_difusion` cumple von Neumann exactamente en la región. -/
theorem esq_lw_difusion_decide_a_si : ∀ r nu : ℝ, ((esq_lw_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ nu ^ 2 + 2 * r ≤ 1)) := by
  sorry

/-- **Decidir exacta lw_difusion/a, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_lw_difusion_decide_a_no : ∃ r nu : ℝ, ¬ ((esq_lw_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ nu ^ 2 + 2 * r ≤ 1)) := by
  sorry

/-- La región de decidir exacta lw_difusion/a no es vacía. -/
theorem esq_lw_difusion_region_decide_a : ∃ r nu : ℝ, 0 ≤ r ∧ nu ^ 2 + 2 * r ≤ 1 := by
  sorry

/-- **Decidir exacta lw_difusion/b, sí.** `esq_lw_difusion` cumple von Neumann exactamente en la región. -/
theorem esq_lw_difusion_decide_b_si : ∀ r nu : ℝ, ((esq_lw_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 2 ∧ nu ^ 2 ≤ 1)) := by
  sorry

/-- **Decidir exacta lw_difusion/b, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_lw_difusion_decide_b_no : ∃ r nu : ℝ, ¬ ((esq_lw_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 2 ∧ nu ^ 2 ≤ 1)) := by
  sorry

/-- La región de decidir exacta lw_difusion/b no es vacía. -/
theorem esq_lw_difusion_region_decide_b : ∃ r nu : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ nu ^ 2 ≤ 1 := by
  sorry

/-- **Decidir exacta lw_difusion/c, sí.** `esq_lw_difusion` cumple von Neumann exactamente en la región. -/
theorem esq_lw_difusion_decide_c_si : ∀ r nu : ℝ, ((esq_lw_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ (nu ^ 2 + 2 * r) ^ 2 - nu ^ 2 ≤ 2 * r)) := by
  sorry

/-- **Decidir exacta lw_difusion/c, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_lw_difusion_decide_c_no : ∃ r nu : ℝ, ¬ ((esq_lw_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ (nu ^ 2 + 2 * r) ^ 2 - nu ^ 2 ≤ 2 * r)) := by
  sorry

/-- La región de decidir exacta lw_difusion/c no es vacía. -/
theorem esq_lw_difusion_region_decide_c : ∃ r nu : ℝ, 0 ≤ r ∧ (nu ^ 2 + 2 * r) ^ 2 - nu ^ 2 ≤ 2 * r := by
  sorry

/-- **upwind_difusion.** Upwind con difusión central para u_t + c·u_x = α·u_xx, r = α·Δt/Δx², ν = c·Δt/Δx. Origen: nivel difícil del diseño A (25 oct 2026). -/
noncomputable def esq_upwind_difusion (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu else if k = 0 then 1 - 2 * r - nu else if k = 1 then r else 0

/-- Momentos 0, 1 y 2 de `esq_upwind_difusion`. -/
theorem esq_upwind_difusion_momentos (r : ℝ) (nu : ℝ) :
    (esq_upwind_difusion r nu).momento 0 = 1 ∧ (esq_upwind_difusion r nu).momento 1 = -nu ∧ (esq_upwind_difusion r nu).momento 2 = 2 * r + nu := by
  sorry

/-- **Decidir exacta upwind_difusion/a, sí.** `esq_upwind_difusion` cumple von Neumann exactamente en la región. -/
theorem esq_upwind_difusion_decide_a_si : ∀ r nu : ℝ, ((esq_upwind_difusion r nu).vonNeumann ↔ (nu ^ 2 ≤ 2 * r + nu ∧ 2 * r + nu ≤ 1)) := by
  sorry

/-- **Decidir exacta upwind_difusion/a, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_upwind_difusion_decide_a_no : ∃ r nu : ℝ, ¬ ((esq_upwind_difusion r nu).vonNeumann ↔ (nu ^ 2 ≤ 2 * r + nu ∧ 2 * r + nu ≤ 1)) := by
  sorry

/-- La región de decidir exacta upwind_difusion/a no es vacía. -/
theorem esq_upwind_difusion_region_decide_a : ∃ r nu : ℝ, nu ^ 2 ≤ 2 * r + nu ∧ 2 * r + nu ≤ 1 := by
  sorry

/-- **Decidir exacta upwind_difusion/b, sí.** `esq_upwind_difusion` cumple von Neumann exactamente en la región. -/
theorem esq_upwind_difusion_decide_b_si : ∀ r nu : ℝ, ((esq_upwind_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ 0 ≤ nu ∧ 2 * r + nu ≤ 1)) := by
  sorry

/-- **Decidir exacta upwind_difusion/b, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_upwind_difusion_decide_b_no : ∃ r nu : ℝ, ¬ ((esq_upwind_difusion r nu).vonNeumann ↔ (0 ≤ r ∧ 0 ≤ nu ∧ 2 * r + nu ≤ 1)) := by
  sorry

/-- La región de decidir exacta upwind_difusion/b no es vacía. -/
theorem esq_upwind_difusion_region_decide_b : ∃ r nu : ℝ, 0 ≤ r ∧ 0 ≤ nu ∧ 2 * r + nu ≤ 1 := by
  sorry

/-- **ftcs4_calor.** Diferencias centradas de cuarto orden en espacio, Euler explícito en tiempo, para u_t = α·u_xx, r = α·Δt/Δx². Origen: nivel difícil del diseño A (25 oct 2026). -/
noncomputable def esq_ftcs4_calor (r : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -r / 12 else if k = -1 then 4 * r / 3 else if k = 0 then 1 - 5 * r / 2 else if k = 1 then 4 * r / 3 else if k = 2 then -r / 12 else 0

/-- Momentos 0, 1 y 2 de `esq_ftcs4_calor`. -/
theorem esq_ftcs4_calor_momentos (r : ℝ) :
    (esq_ftcs4_calor r).momento 0 = 1 ∧ (esq_ftcs4_calor r).momento 1 = 0 ∧ (esq_ftcs4_calor r).momento 2 = 2 * r := by
  sorry

/-- **Decidir exacta ftcs4_calor/a, sí.** `esq_ftcs4_calor` cumple von Neumann exactamente en la región. -/
theorem esq_ftcs4_calor_decide_a_si : ∀ r : ℝ, ((esq_ftcs4_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 3 / 8)) := by
  sorry

/-- **Decidir exacta ftcs4_calor/a, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_ftcs4_calor_decide_a_no : ∃ r : ℝ, ¬ ((esq_ftcs4_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 3 / 8)) := by
  sorry

/-- La región de decidir exacta ftcs4_calor/a no es vacía. -/
theorem esq_ftcs4_calor_region_decide_a : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 3 / 8 := by
  sorry

/-- **Decidir exacta ftcs4_calor/b, sí.** `esq_ftcs4_calor` cumple von Neumann exactamente en la región. -/
theorem esq_ftcs4_calor_decide_b_si : ∀ r : ℝ, ((esq_ftcs4_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 2)) := by
  sorry

/-- **Decidir exacta ftcs4_calor/b, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_ftcs4_calor_decide_b_no : ∃ r : ℝ, ¬ ((esq_ftcs4_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 2)) := by
  sorry

/-- La región de decidir exacta ftcs4_calor/b no es vacía. -/
theorem esq_ftcs4_calor_region_decide_b : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 := by
  sorry

/-- **Decidir exacta ftcs4_calor/c, sí.** `esq_ftcs4_calor` cumple von Neumann exactamente en la región. -/
theorem esq_ftcs4_calor_decide_c_si : ∀ r : ℝ, ((esq_ftcs4_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 3)) := by
  sorry

/-- **Decidir exacta ftcs4_calor/c, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_ftcs4_calor_decide_c_no : ∃ r : ℝ, ¬ ((esq_ftcs4_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 3)) := by
  sorry

/-- La región de decidir exacta ftcs4_calor/c no es vacía. -/
theorem esq_ftcs4_calor_region_decide_c : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 3 := by
  sorry

/-- **fromm.** Esquema de Fromm (promedio de Lax-Wendroff y Beam-Warming) para u_t + c·u_x = 0, ν = c·Δt/Δx. Origen: nivel difícil del diseño A (25 oct 2026). -/
noncomputable def esq_fromm (nu : ℝ) : Esquema where
  S := {-2, -1, 0, 1}
  a := fun k => if k = -2 then (nu ^ 2 - nu) / 4 else if k = -1 then (5 * nu - nu ^ 2) / 4 else if k = 0 then (4 - 3 * nu - nu ^ 2) / 4 else if k = 1 then (nu ^ 2 - nu) / 4 else 0

/-- Momentos 0, 1 y 2 de `esq_fromm`. -/
theorem esq_fromm_momentos (nu : ℝ) :
    (esq_fromm nu).momento 0 = 1 ∧ (esq_fromm nu).momento 1 = -nu ∧ (esq_fromm nu).momento 2 = nu ^ 2 := by
  sorry

/-- **Decidir exacta fromm/a, sí.** `esq_fromm` cumple von Neumann exactamente en la región. -/
theorem esq_fromm_decide_a_si : ∀ nu : ℝ, ((esq_fromm nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 1)) := by
  sorry

/-- **Decidir exacta fromm/a, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_fromm_decide_a_no : ∃ nu : ℝ, ¬ ((esq_fromm nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 1)) := by
  sorry

/-- La región de decidir exacta fromm/a no es vacía. -/
theorem esq_fromm_region_decide_a : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 := by
  sorry

/-- **Decidir exacta fromm/b, sí.** `esq_fromm` cumple von Neumann exactamente en la región. -/
theorem esq_fromm_decide_b_si : ∀ nu : ℝ, ((esq_fromm nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 2)) := by
  sorry

/-- **Decidir exacta fromm/b, no.** Hay un punto donde von Neumann y la región no coinciden. -/
theorem esq_fromm_decide_b_no : ∃ nu : ℝ, ¬ ((esq_fromm nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 2)) := by
  sorry

/-- La región de decidir exacta fromm/b no es vacía. -/
theorem esq_fromm_region_decide_b : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 2 := by
  sorry

/-- **c2s_lax_wendroff_difusivo_5.** Lax-Wendroff con difusión física añadida (segundo derivado centrado con coeficiente (nu^2+2r)/2), un subpaso Origen: proponente claude-sonnet-5-5, muestra 5, 20261025-132247. -/
noncomputable def esq_c2s_lax_wendroff_difusivo_5 (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then (nu^2+2*r+nu)/2 else if k = 0 then 1-nu^2-2*r else if k = 1 then (nu^2+2*r-nu)/2 else 0

/-- Momentos 0, 1 y 2 de `esq_c2s_lax_wendroff_difusivo_5`. -/
theorem esq_c2s_lax_wendroff_difusivo_5_momentos (r : ℝ) (nu : ℝ) :
    (esq_c2s_lax_wendroff_difusivo_5 r nu).momento 0 = 1 ∧ (esq_c2s_lax_wendroff_difusivo_5 r nu).momento 1 = -nu ∧ (esq_c2s_lax_wendroff_difusivo_5 r nu).momento 2 = nu^2+2*r := by
  sorry

/-- **Decidir c2s_lax_wendroff_difusivo_5/lazo, sí.** En toda la región, `esq_c2s_lax_wendroff_difusivo_5` cumple von Neumann. -/
theorem esq_c2s_lax_wendroff_difusivo_5_decide_lazo_si : ∀ r nu : ℝ, (0 ≤ r ∧ (nu^2+2*r)^2 - nu^2 ≤ 2*r) → (esq_c2s_lax_wendroff_difusivo_5 r nu).vonNeumann := by
  sorry

/-- **Decidir c2s_lax_wendroff_difusivo_5/lazo, no.** Hay un punto de la región donde `esq_c2s_lax_wendroff_difusivo_5` no cumple von Neumann. -/
theorem esq_c2s_lax_wendroff_difusivo_5_decide_lazo_no : ∃ r nu : ℝ, (0 ≤ r ∧ (nu^2+2*r)^2 - nu^2 ≤ 2*r) ∧ ¬ (esq_c2s_lax_wendroff_difusivo_5 r nu).vonNeumann := by
  sorry

/-- La región de decidir c2s_lax_wendroff_difusivo_5/lazo no es vacía. -/
theorem esq_c2s_lax_wendroff_difusivo_5_region_decide_lazo : ∃ r nu : ℝ, 0 ≤ r ∧ (nu^2+2*r)^2 - nu^2 ≤ 2*r := by
  sorry

/-- **c2h_lax_wendroff_difusivo_1.** Lax-Wendroff para la advección más difusión centrada explícita, un subpaso por paso de datos Origen: proponente claude-haiku-5-5, muestra 1, 20261025-132547. -/
noncomputable def esq_c2h_lax_wendroff_difusivo_1 (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then (nu + nu^2)/2 + r else if k = 0 then 1 - nu^2 - 2*r else if k = 1 then (nu^2 - nu)/2 + r else 0

/-- Momentos 0, 1 y 2 de `esq_c2h_lax_wendroff_difusivo_1`. -/
theorem esq_c2h_lax_wendroff_difusivo_1_momentos (r : ℝ) (nu : ℝ) :
    (esq_c2h_lax_wendroff_difusivo_1 r nu).momento 0 = 1 ∧ (esq_c2h_lax_wendroff_difusivo_1 r nu).momento 1 = -nu ∧ (esq_c2h_lax_wendroff_difusivo_1 r nu).momento 2 = nu^2 + 2*r := by
  sorry

/-- **Decidir c2h_lax_wendroff_difusivo_1/lazo, sí.** En toda la región, `esq_c2h_lax_wendroff_difusivo_1` cumple von Neumann. -/
theorem esq_c2h_lax_wendroff_difusivo_1_decide_lazo_si : ∀ r nu : ℝ, (0 ≤ r ∧ nu^4 + 4*r*nu^2 + 4*r^2 - nu^2 ≤ 2*r) → (esq_c2h_lax_wendroff_difusivo_1 r nu).vonNeumann := by
  sorry

/-- **Decidir c2h_lax_wendroff_difusivo_1/lazo, no.** Hay un punto de la región donde `esq_c2h_lax_wendroff_difusivo_1` no cumple von Neumann. -/
theorem esq_c2h_lax_wendroff_difusivo_1_decide_lazo_no : ∃ r nu : ℝ, (0 ≤ r ∧ nu^4 + 4*r*nu^2 + 4*r^2 - nu^2 ≤ 2*r) ∧ ¬ (esq_c2h_lax_wendroff_difusivo_1 r nu).vonNeumann := by
  sorry

/-- La región de decidir c2h_lax_wendroff_difusivo_1/lazo no es vacía. -/
theorem esq_c2h_lax_wendroff_difusivo_1_region_decide_lazo : ∃ r nu : ℝ, 0 ≤ r ∧ nu^4 + 4*r*nu^2 + 4*r^2 - nu^2 ≤ 2*r := by
  sorry

/-- **c2h_lax_wendroff_difusion_2.** Lax-Wendroff mas termino difusivo FTCS; 1 subpaso por paso de datos (h = dt = 0.02, nu ≈ 0.79984, r ≈ 0.160032). Origen: proponente claude-haiku-5-5, muestra 2, 20261025-132547. -/
noncomputable def esq_c2h_lax_wendroff_difusion_2 (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then nu^2/2+r+nu/2 else if k = 0 then 1-nu^2-2*r else if k = 1 then nu^2/2+r-nu/2 else 0

/-- Momentos 0, 1 y 2 de `esq_c2h_lax_wendroff_difusion_2`. -/
theorem esq_c2h_lax_wendroff_difusion_2_momentos (r : ℝ) (nu : ℝ) :
    (esq_c2h_lax_wendroff_difusion_2 r nu).momento 0 = 1 ∧ (esq_c2h_lax_wendroff_difusion_2 r nu).momento 1 = -nu ∧ (esq_c2h_lax_wendroff_difusion_2 r nu).momento 2 = nu^2+2*r := by
  sorry

/-- **Decidir c2h_lax_wendroff_difusion_2/lazo, sí.** En toda la región, `esq_c2h_lax_wendroff_difusion_2` cumple von Neumann. -/
theorem esq_c2h_lax_wendroff_difusion_2_decide_lazo_si : ∀ r nu : ℝ, (0≤r ∧ (nu^2+2*r)^2-nu^2-2*r≤0) → (esq_c2h_lax_wendroff_difusion_2 r nu).vonNeumann := by
  sorry

/-- **Decidir c2h_lax_wendroff_difusion_2/lazo, no.** Hay un punto de la región donde `esq_c2h_lax_wendroff_difusion_2` no cumple von Neumann. -/
theorem esq_c2h_lax_wendroff_difusion_2_decide_lazo_no : ∃ r nu : ℝ, (0≤r ∧ (nu^2+2*r)^2-nu^2-2*r≤0) ∧ ¬ (esq_c2h_lax_wendroff_difusion_2 r nu).vonNeumann := by
  sorry

/-- La región de decidir c2h_lax_wendroff_difusion_2/lazo no es vacía. -/
theorem esq_c2h_lax_wendroff_difusion_2_region_decide_lazo : ∃ r nu : ℝ, 0≤r ∧ (nu^2+2*r)^2-nu^2-2*r≤0 := by
  sorry

/-- **c2h_lax_wendroff_adv_dif_3.** Lax-Wendroff para advección-difusión: un solo subpaso por paso de datos, sin difusión numérica extra de orden h. Origen: proponente claude-haiku-5-5, muestra 3, 20261025-132547. -/
noncomputable def esq_c2h_lax_wendroff_adv_dif_3 (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then (nu^2 + nu)/2 + r else if k = 0 then 1 - nu^2 - 2*r else if k = 1 then (nu^2 - nu)/2 + r else 0

/-- Momentos 0, 1 y 2 de `esq_c2h_lax_wendroff_adv_dif_3`. -/
theorem esq_c2h_lax_wendroff_adv_dif_3_momentos (r : ℝ) (nu : ℝ) :
    (esq_c2h_lax_wendroff_adv_dif_3 r nu).momento 0 = 1 ∧ (esq_c2h_lax_wendroff_adv_dif_3 r nu).momento 1 = -nu ∧ (esq_c2h_lax_wendroff_adv_dif_3 r nu).momento 2 = nu^2 + 2*r := by
  sorry

/-- **Decidir c2h_lax_wendroff_adv_dif_3/lazo, sí.** En toda la región, `esq_c2h_lax_wendroff_adv_dif_3` cumple von Neumann. -/
theorem esq_c2h_lax_wendroff_adv_dif_3_decide_lazo_si : ∀ r nu : ℝ, (0 ≤ r ∧ nu^4 - nu^2 + 4*r*nu^2 + 4*r^2 - 2*r ≤ 0) → (esq_c2h_lax_wendroff_adv_dif_3 r nu).vonNeumann := by
  sorry

/-- **Decidir c2h_lax_wendroff_adv_dif_3/lazo, no.** Hay un punto de la región donde `esq_c2h_lax_wendroff_adv_dif_3` no cumple von Neumann. -/
theorem esq_c2h_lax_wendroff_adv_dif_3_decide_lazo_no : ∃ r nu : ℝ, (0 ≤ r ∧ nu^4 - nu^2 + 4*r*nu^2 + 4*r^2 - 2*r ≤ 0) ∧ ¬ (esq_c2h_lax_wendroff_adv_dif_3 r nu).vonNeumann := by
  sorry

/-- La región de decidir c2h_lax_wendroff_adv_dif_3/lazo no es vacía. -/
theorem esq_c2h_lax_wendroff_adv_dif_3_region_decide_lazo : ∃ r nu : ℝ, 0 ≤ r ∧ nu^4 - nu^2 + 4*r*nu^2 + 4*r^2 - 2*r ≤ 0 := by
  sorry

end PrometeoLean.Esquemas

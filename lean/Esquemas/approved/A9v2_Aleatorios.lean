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

/-! ## A9 v2. Stencils aleatorios de cinco puntos (semilla 20261027): 24 esquemas, una tarea de decidir cada uno

Enunciados generados mecánicamente desde `esquemas_aleatorios_A9v2.json`; no se escriben a mano. -/

/-- **aleat_01.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (-1/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_01 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/64 - 9*t/32 else if k = -1 then 11*t^2/128 + 19*t/16 else if k = 0 then -17*t^2/128 - 3*t/2 + 1 else if k = 1 then 9*t^2/128 + 5*t/16 else if k = 2 then -t^2/128 + 9*t/32 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_01`. -/
theorem esq_aleat_01_momentos (t : ℝ) :
    (esq_aleat_01 t).momento 0 = 1 ∧ (esq_aleat_01 t).momento 1 = t/4 ∧ (esq_aleat_01 t).momento 2 = t^2/16 + 3*t/2 := by
  sorry

/-- **Decidir aleat_01/a, sí.** En toda la región, `esq_aleat_01` cumple von Neumann. -/
theorem esq_aleat_01_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 27/31) → (esq_aleat_01 t).vonNeumann := by
  sorry

/-- **Decidir aleat_01/a, no.** Hay un punto de la región donde `esq_aleat_01` no cumple von Neumann. -/
theorem esq_aleat_01_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 27/31) ∧ ¬ (esq_aleat_01 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_01/a no es vacía. -/
theorem esq_aleat_01_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 27/31 := by
  sorry

/-- **aleat_02.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (-1)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_02 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then t^2/4 + t/16 else if k = -1 then -t^2/4 + 5*t/32 else if k = 0 then -t^2/4 - 51*t/32 + 1 else if k = 1 then t^2/4 + 47*t/32 else if k = 2 then -3*t/32 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_02`. -/
theorem esq_aleat_02_momentos (t : ℝ) :
    (esq_aleat_02 t).momento 0 = 1 ∧ (esq_aleat_02 t).momento 1 = t ∧ (esq_aleat_02 t).momento 2 = t^2 + 3*t/2 := by
  sorry

/-- **Decidir aleat_02/a, sí.** En toda la región, `esq_aleat_02` cumple von Neumann. -/
theorem esq_aleat_02_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 11/30) → (esq_aleat_02 t).vonNeumann := by
  sorry

/-- **Decidir aleat_02/a, no.** Hay un punto de la región donde `esq_aleat_02` no cumple von Neumann. -/
theorem esq_aleat_02_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 11/30) ∧ ¬ (esq_aleat_02 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_02/a no es vacía. -/
theorem esq_aleat_02_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 11/30 := by
  sorry

/-- **aleat_03.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (-1/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_03 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/64 - 11*t/48 else if k = -1 then 5*t^2/64 + 9*t/16 else if k = 0 then -7*t^2/64 - 7*t/16 + 1 else if k = 1 then 3*t^2/64 - 7*t/48 else if k = 2 then t/4 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_03`. -/
theorem esq_aleat_03_momentos (t : ℝ) :
    (esq_aleat_03 t).momento 0 = 1 ∧ (esq_aleat_03 t).momento 1 = t/4 ∧ (esq_aleat_03 t).momento 2 = t^2/16 + t/2 := by
  sorry

/-- **Decidir aleat_03/a, sí.** En toda la región, `esq_aleat_03` cumple von Neumann. -/
theorem esq_aleat_03_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 43/60) → (esq_aleat_03 t).vonNeumann := by
  sorry

/-- **Decidir aleat_03/a, no.** Hay un punto de la región donde `esq_aleat_03` no cumple von Neumann. -/
theorem esq_aleat_03_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 43/60) ∧ ¬ (esq_aleat_03 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_03/a no es vacía. -/
theorem esq_aleat_03_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 43/60 := by
  sorry

/-- **aleat_04.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/2)·t, ν = (-1/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_04 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then 3*t/16 else if k = -1 then t^2/32 - 11*t/48 else if k = 0 then -t^2/16 - 5*t/16 + 1 else if k = 1 then t^2/32 + 5*t/16 else if k = 2 then t/24 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_04`. -/
theorem esq_aleat_04_momentos (t : ℝ) :
    (esq_aleat_04 t).momento 0 = 1 ∧ (esq_aleat_04 t).momento 1 = t/4 ∧ (esq_aleat_04 t).momento 2 = t^2/16 + t := by
  sorry

/-- **Decidir aleat_04/a, sí.** En toda la región, `esq_aleat_04` cumple von Neumann. -/
theorem esq_aleat_04_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 75/47) → (esq_aleat_04 t).vonNeumann := by
  sorry

/-- **Decidir aleat_04/a, no.** Hay un punto de la región donde `esq_aleat_04` no cumple von Neumann. -/
theorem esq_aleat_04_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 75/47) ∧ ¬ (esq_aleat_04 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_04/a no es vacía. -/
theorem esq_aleat_04_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 75/47 := by
  sorry

/-- **aleat_05.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1)·t, ν = (-3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_05 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -3*t^2/32 - 3*t/32 else if k = -1 then 9*t^2/64 + 23*t/32 else if k = 0 then 27*t^2/64 - 55*t/32 + 1 else if k = 1 then -57*t^2/64 + 29*t/32 else if k = 2 then 27*t^2/64 + 3*t/16 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_05`. -/
theorem esq_aleat_05_momentos (t : ℝ) :
    (esq_aleat_05 t).momento 0 = 1 ∧ (esq_aleat_05 t).momento 1 = 3*t/4 ∧ (esq_aleat_05 t).momento 2 = 9*t^2/16 + 2*t := by
  sorry

/-- **Decidir aleat_05/a, sí.** En toda la región, `esq_aleat_05` cumple von Neumann. -/
theorem esq_aleat_05_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 53/60) → (esq_aleat_05 t).vonNeumann := by
  sorry

/-- **Decidir aleat_05/a, no.** Hay un punto de la región donde `esq_aleat_05` no cumple von Neumann. -/
theorem esq_aleat_05_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 53/60) ∧ ¬ (esq_aleat_05 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_05/a no es vacía. -/
theorem esq_aleat_05_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 53/60 := by
  sorry

/-- **aleat_06.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1)·t, ν = (-1/2)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_06 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -3*t^2/32 + 3*t/16 else if k = -1 then 3*t^2/8 - 5*t/48 else if k = 0 then -7*t^2/16 - 9*t/16 + 1 else if k = 1 then t^2/8 + 3*t/16 else if k = 2 then t^2/32 + 7*t/24 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_06`. -/
theorem esq_aleat_06_momentos (t : ℝ) :
    (esq_aleat_06 t).momento 0 = 1 ∧ (esq_aleat_06 t).momento 1 = t/2 ∧ (esq_aleat_06 t).momento 2 = t^2/4 + 2*t := by
  sorry

/-- **Decidir aleat_06/a, sí.** En toda la región, `esq_aleat_06` cumple von Neumann. -/
theorem esq_aleat_06_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 85/48) → (esq_aleat_06 t).vonNeumann := by
  sorry

/-- **Decidir aleat_06/a, no.** Hay un punto de la región donde `esq_aleat_06` no cumple von Neumann. -/
theorem esq_aleat_06_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 85/48) ∧ ¬ (esq_aleat_06 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_06/a no es vacía. -/
theorem esq_aleat_06_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 85/48 := by
  sorry

/-- **aleat_07.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (-1/2)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_07 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then t^2/32 + t/16 else if k = -1 then 5*t^2/32 - 3*t/16 else if k = 0 then -17*t^2/32 - 5*t/16 + 1 else if k = 1 then 15*t^2/32 + 7*t/16 else if k = 2 then -t^2/8 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_07`. -/
theorem esq_aleat_07_momentos (t : ℝ) :
    (esq_aleat_07 t).momento 0 = 1 ∧ (esq_aleat_07 t).momento 1 = t/2 ∧ (esq_aleat_07 t).momento 2 = t^2/4 + t/2 := by
  sorry

/-- **Decidir aleat_07/a, sí.** En toda la región, `esq_aleat_07` cumple von Neumann. -/
theorem esq_aleat_07_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 31/50) → (esq_aleat_07 t).vonNeumann := by
  sorry

/-- **Decidir aleat_07/a, no.** Hay un punto de la región donde `esq_aleat_07` no cumple von Neumann. -/
theorem esq_aleat_07_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 31/50) ∧ ¬ (esq_aleat_07 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_07/a no es vacía. -/
theorem esq_aleat_07_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 31/50 := by
  sorry

/-- **aleat_08.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/2)·t, ν = (-3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_08 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -9*t^2/32 - 13*t/48 else if k = -1 then 45*t^2/64 + 3*t/4 else if k = 0 then -9*t^2/64 - 5*t/4 + 1 else if k = 1 then -45*t^2/64 + 7*t/12 else if k = 2 then 27*t^2/64 + 3*t/16 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_08`. -/
theorem esq_aleat_08_momentos (t : ℝ) :
    (esq_aleat_08 t).momento 0 = 1 ∧ (esq_aleat_08 t).momento 1 = 3*t/4 ∧ (esq_aleat_08 t).momento 2 = 9*t^2/16 + t := by
  sorry

/-- **Decidir aleat_08/a, sí.** En toda la región, `esq_aleat_08` cumple von Neumann. -/
theorem esq_aleat_08_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 25/39) → (esq_aleat_08 t).vonNeumann := by
  sorry

/-- **Decidir aleat_08/a, no.** Hay un punto de la región donde `esq_aleat_08` no cumple von Neumann. -/
theorem esq_aleat_08_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 25/39) ∧ ¬ (esq_aleat_08 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_08/a no es vacía. -/
theorem esq_aleat_08_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 25/39 := by
  sorry

/-- **aleat_09.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/2)·t, ν = (-1/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_09 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/96 - 7*t/48 else if k = -1 then 3*t^2/64 + 19*t/32 else if k = 0 then -3*t^2/64 - 25*t/32 + 1 else if k = 1 then -t^2/192 + 11*t/96 else if k = 2 then t^2/64 + 7*t/32 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_09`. -/
theorem esq_aleat_09_momentos (t : ℝ) :
    (esq_aleat_09 t).momento 0 = 1 ∧ (esq_aleat_09 t).momento 1 = t/4 ∧ (esq_aleat_09 t).momento 2 = t^2/16 + t := by
  sorry

/-- **Decidir aleat_09/a, sí.** En toda la región, `esq_aleat_09` cumple von Neumann. -/
theorem esq_aleat_09_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 64/45) → (esq_aleat_09 t).vonNeumann := by
  sorry

/-- **Decidir aleat_09/a, no.** Hay un punto de la región donde `esq_aleat_09` no cumple von Neumann. -/
theorem esq_aleat_09_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 64/45) ∧ ¬ (esq_aleat_09 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_09/a no es vacía. -/
theorem esq_aleat_09_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 64/45 := by
  sorry

/-- **aleat_10.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (1/2)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_10 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then 5*t/16 else if k = -1 then 5*t^2/32 + 3*t/16 else if k = 0 then -11*t^2/32 - 15*t/16 + 1 else if k = 1 then 7*t^2/32 + 9*t/16 else if k = 2 then -t^2/32 - t/8 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_10`. -/
theorem esq_aleat_10_momentos (t : ℝ) :
    (esq_aleat_10 t).momento 0 = 1 ∧ (esq_aleat_10 t).momento 1 = -t/2 ∧ (esq_aleat_10 t).momento 2 = t^2/4 + 3*t/2 := by
  sorry

/-- **Decidir aleat_10/a, sí.** En toda la región, `esq_aleat_10` cumple von Neumann. -/
theorem esq_aleat_10_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 19/25) → (esq_aleat_10 t).vonNeumann := by
  sorry

/-- **Decidir aleat_10/a, no.** Hay un punto de la región donde `esq_aleat_10` no cumple von Neumann. -/
theorem esq_aleat_10_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 19/25) ∧ ¬ (esq_aleat_10 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_10/a no es vacía. -/
theorem esq_aleat_10_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 19/25 := by
  sorry

/-- **aleat_11.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (1)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_11 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -3*t^2/4 - t/24 else if k = -1 then 19*t^2/8 + 19*t/24 else if k = 0 then -17*t^2/8 - 3*t/8 + 1 else if k = 1 then t^2/8 - 11*t/24 else if k = 2 then 3*t^2/8 + t/12 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_11`. -/
theorem esq_aleat_11_momentos (t : ℝ) :
    (esq_aleat_11 t).momento 0 = 1 ∧ (esq_aleat_11 t).momento 1 = -t ∧ (esq_aleat_11 t).momento 2 = t^2 + t/2 := by
  sorry

/-- **Decidir aleat_11/a, sí.** En toda la región, `esq_aleat_11` cumple von Neumann. -/
theorem esq_aleat_11_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 8/39) → (esq_aleat_11 t).vonNeumann := by
  sorry

/-- **Decidir aleat_11/a, no.** Hay un punto de la región donde `esq_aleat_11` no cumple von Neumann. -/
theorem esq_aleat_11_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 8/39) ∧ ¬ (esq_aleat_11 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_11/a no es vacía. -/
theorem esq_aleat_11_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 8/39 := by
  sorry

/-- **aleat_12.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (-1)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_12 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/6 - 9*t/16 else if k = -1 then t^2 + 67*t/48 else if k = 0 then -3*t^2/2 - 25*t/16 + 1 else if k = 1 then 2*t^2/3 + 3*t/16 else if k = 2 then 13*t/24 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_12`. -/
theorem esq_aleat_12_momentos (t : ℝ) :
    (esq_aleat_12 t).momento 0 = 1 ∧ (esq_aleat_12 t).momento 1 = t ∧ (esq_aleat_12 t).momento 2 = t^2 + 3*t/2 := by
  sorry

/-- **Decidir aleat_12/a, sí.** En toda la región, `esq_aleat_12` cumple von Neumann. -/
theorem esq_aleat_12_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 11/26) → (esq_aleat_12 t).vonNeumann := by
  sorry

/-- **Decidir aleat_12/a, no.** Hay un punto de la región donde `esq_aleat_12` no cumple von Neumann. -/
theorem esq_aleat_12_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 11/26) ∧ ¬ (esq_aleat_12 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_12/a no es vacía. -/
theorem esq_aleat_12_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 11/26 := by
  sorry

/-- **aleat_13.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1)·t, ν = (1)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_13 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/4 - t/2 else if k = -1 then t^2 + 5*t/2 else if k = 0 then -t^2 - 2*t + 1 else if k = 1 then -t/2 else if k = 2 then t^2/4 + t/2 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_13`. -/
theorem esq_aleat_13_momentos (t : ℝ) :
    (esq_aleat_13 t).momento 0 = 1 ∧ (esq_aleat_13 t).momento 1 = -t ∧ (esq_aleat_13 t).momento 2 = t^2 + 2*t := by
  sorry

/-- **Decidir aleat_13/a, sí.** En toda la región, `esq_aleat_13` cumple von Neumann. -/
theorem esq_aleat_13_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 11/32) → (esq_aleat_13 t).vonNeumann := by
  sorry

/-- **Decidir aleat_13/a, no.** Hay un punto de la región donde `esq_aleat_13` no cumple von Neumann. -/
theorem esq_aleat_13_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 11/32) ∧ ¬ (esq_aleat_13 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_13/a no es vacía. -/
theorem esq_aleat_13_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 11/32 := by
  sorry

/-- **aleat_14.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (-3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_14 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then 7*t/32 else if k = -1 then 15*t^2/64 - 5*t/8 else if k = 0 then -27*t^2/64 - 5*t/16 + 1 else if k = 1 then 9*t^2/64 + 7*t/8 else if k = 2 then 3*t^2/64 - 5*t/32 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_14`. -/
theorem esq_aleat_14_momentos (t : ℝ) :
    (esq_aleat_14 t).momento 0 = 1 ∧ (esq_aleat_14 t).momento 1 = 3*t/4 ∧ (esq_aleat_14 t).momento 2 = 9*t^2/16 + t/2 := by
  sorry

/-- **Decidir aleat_14/a, sí.** En toda la región, `esq_aleat_14` cumple von Neumann. -/
theorem esq_aleat_14_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 31/63) → (esq_aleat_14 t).vonNeumann := by
  sorry

/-- **Decidir aleat_14/a, no.** Hay un punto de la región donde `esq_aleat_14` no cumple von Neumann. -/
theorem esq_aleat_14_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 31/63) ∧ ¬ (esq_aleat_14 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_14/a no es vacía. -/
theorem esq_aleat_14_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 31/63 := by
  sorry

/-- **aleat_15.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_15 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -9*t^2/64 else if k = -1 then 9*t^2/16 + 15*t/16 else if k = 0 then -9*t^2/16 - 15*t/16 + 1 else if k = 1 then -3*t/16 else if k = 2 then 9*t^2/64 + 3*t/16 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_15`. -/
theorem esq_aleat_15_momentos (t : ℝ) :
    (esq_aleat_15 t).momento 0 = 1 ∧ (esq_aleat_15 t).momento 1 = -3*t/4 ∧ (esq_aleat_15 t).momento 2 = 9*t^2/16 + 3*t/2 := by
  sorry

/-- **Decidir aleat_15/a, sí.** En toda la región, `esq_aleat_15` cumple von Neumann. -/
theorem esq_aleat_15_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 24/55) → (esq_aleat_15 t).vonNeumann := by
  sorry

/-- **Decidir aleat_15/a, no.** Hay un punto de la región donde `esq_aleat_15` no cumple von Neumann. -/
theorem esq_aleat_15_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 24/55) ∧ ¬ (esq_aleat_15 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_15/a no es vacía. -/
theorem esq_aleat_15_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 24/55 := by
  sorry

/-- **aleat_16.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/2)·t, ν = (1)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_16 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -3*t^2/8 - 3*t/4 else if k = -1 then 37*t^2/24 + 8*t/3 else if k = 0 then -15*t^2/8 - 3*t/2 + 1 else if k = 1 then 5*t^2/8 - t else if k = 2 then t^2/12 + 7*t/12 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_16`. -/
theorem esq_aleat_16_momentos (t : ℝ) :
    (esq_aleat_16 t).momento 0 = 1 ∧ (esq_aleat_16 t).momento 1 = -t ∧ (esq_aleat_16 t).momento 2 = t^2 + t := by
  sorry

/-- **Decidir aleat_16/a, sí.** En toda la región, `esq_aleat_16` cumple von Neumann. -/
theorem esq_aleat_16_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 1/6) → (esq_aleat_16 t).vonNeumann := by
  sorry

/-- **Decidir aleat_16/a, no.** Hay un punto de la región donde `esq_aleat_16` no cumple von Neumann. -/
theorem esq_aleat_16_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1/6) ∧ ¬ (esq_aleat_16 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_16/a no es vacía. -/
theorem esq_aleat_16_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/6 := by
  sorry

/-- **aleat_17.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (-1/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_17 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -3*t^2/128 + t/6 else if k = -1 then 41*t^2/384 + t/12 else if k = 0 then -19*t^2/128 - 7*t/8 + 1 else if k = 1 then 9*t^2/128 + 7*t/12 else if k = 2 then -t^2/192 + t/24 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_17`. -/
theorem esq_aleat_17_momentos (t : ℝ) :
    (esq_aleat_17 t).momento 0 = 1 ∧ (esq_aleat_17 t).momento 1 = t/4 ∧ (esq_aleat_17 t).momento 2 = t^2/16 + 3*t/2 := by
  sorry

/-- **Decidir aleat_17/a, sí.** En toda la región, `esq_aleat_17` cumple von Neumann. -/
theorem esq_aleat_17_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 4/5) → (esq_aleat_17 t).vonNeumann := by
  sorry

/-- **Decidir aleat_17/a, no.** Hay un punto de la región donde `esq_aleat_17` no cumple von Neumann. -/
theorem esq_aleat_17_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 4/5) ∧ ¬ (esq_aleat_17 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_17/a no es vacía. -/
theorem esq_aleat_17_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 4/5 := by
  sorry

/-- **aleat_18.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (1)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_18 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/2 - 15*t/32 else if k = -1 then 5*t^2/4 + 51*t/32 else if k = 0 then -t^2/4 - 7*t/32 + 1 else if k = 1 then -5*t^2/4 - 47*t/32 else if k = 2 then 3*t^2/4 + 9*t/16 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_18`. -/
theorem esq_aleat_18_momentos (t : ℝ) :
    (esq_aleat_18 t).momento 0 = 1 ∧ (esq_aleat_18 t).momento 1 = -t ∧ (esq_aleat_18 t).momento 2 = t^2 + t/2 := by
  sorry

/-- **Decidir aleat_18/a, sí.** En toda la región, `esq_aleat_18` cumple von Neumann. -/
theorem esq_aleat_18_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 1/14) → (esq_aleat_18 t).vonNeumann := by
  sorry

/-- **Decidir aleat_18/a, no.** Hay un punto de la región donde `esq_aleat_18` no cumple von Neumann. -/
theorem esq_aleat_18_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1/14) ∧ ¬ (esq_aleat_18 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_18/a no es vacía. -/
theorem esq_aleat_18_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1/14 := by
  sorry

/-- **aleat_19.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (-3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_19 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then 3*t^2/32 + 3*t/32 else if k = -1 then 3*t^2/32 - 5*t/48 else if k = 0 then -9*t^2/16 - 9*t/8 + 1 else if k = 1 then 15*t^2/32 + 23*t/16 else if k = 2 then -3*t^2/32 - 29*t/96 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_19`. -/
theorem esq_aleat_19_momentos (t : ℝ) :
    (esq_aleat_19 t).momento 0 = 1 ∧ (esq_aleat_19 t).momento 1 = 3*t/4 ∧ (esq_aleat_19 t).momento 2 = 9*t^2/16 + t/2 := by
  sorry

/-- **Decidir aleat_19/a, sí.** En toda la región, `esq_aleat_19` cumple von Neumann. -/
theorem esq_aleat_19_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 27/40) → (esq_aleat_19 t).vonNeumann := by
  sorry

/-- **Decidir aleat_19/a, no.** Hay un punto de la región donde `esq_aleat_19` no cumple von Neumann. -/
theorem esq_aleat_19_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 27/40) ∧ ¬ (esq_aleat_19 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_19/a no es vacía. -/
theorem esq_aleat_19_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 27/40 := by
  sorry

/-- **aleat_20.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1)·t, ν = (-1/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_20 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then t^2/64 + 5*t/24 else if k = -1 then -t^2/64 + 3*t/16 else if k = 0 then -t^2/64 - 19*t/16 + 1 else if k = 1 then t^2/64 + 35*t/48 else if k = 2 then t/16 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_20`. -/
theorem esq_aleat_20_momentos (t : ℝ) :
    (esq_aleat_20 t).momento 0 = 1 ∧ (esq_aleat_20 t).momento 1 = t/4 ∧ (esq_aleat_20 t).momento 2 = t^2/16 + 2*t := by
  sorry

/-- **Decidir aleat_20/a, sí.** En toda la región, `esq_aleat_20` cumple von Neumann. -/
theorem esq_aleat_20_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 46/41) → (esq_aleat_20 t).vonNeumann := by
  sorry

/-- **Decidir aleat_20/a, no.** Hay un punto de la región donde `esq_aleat_20` no cumple von Neumann. -/
theorem esq_aleat_20_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 46/41) ∧ ¬ (esq_aleat_20 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_20/a no es vacía. -/
theorem esq_aleat_20_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 46/41 := by
  sorry

/-- **aleat_21.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1)·t, ν = (1/2)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_21 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/8 - 3*t/8 else if k = -1 then 19*t^2/32 + 15*t/8 else if k = 0 then -29*t^2/32 - 13*t/8 + 1 else if k = 1 then 17*t^2/32 - 3*t/8 else if k = 2 then -3*t^2/32 + t/2 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_21`. -/
theorem esq_aleat_21_momentos (t : ℝ) :
    (esq_aleat_21 t).momento 0 = 1 ∧ (esq_aleat_21 t).momento 1 = -t/2 ∧ (esq_aleat_21 t).momento 2 = t^2/4 + 2*t := by
  sorry

/-- **Decidir aleat_21/a, sí.** En toda la región, `esq_aleat_21` cumple von Neumann. -/
theorem esq_aleat_21_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 3/10) → (esq_aleat_21 t).vonNeumann := by
  sorry

/-- **Decidir aleat_21/a, no.** Hay un punto de la región donde `esq_aleat_21` no cumple von Neumann. -/
theorem esq_aleat_21_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 3/10) ∧ ¬ (esq_aleat_21 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_21/a no es vacía. -/
theorem esq_aleat_21_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 3/10 := by
  sorry

/-- **aleat_22.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (-1/2)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_22 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then -t^2/24 + 7*t/48 else if k = -1 then 11*t^2/32 - 37*t/96 else if k = 0 then -21*t^2/32 - 7*t/32 + 1 else if k = 1 then 43*t^2/96 + 49*t/96 else if k = 2 then -3*t^2/32 - 5*t/96 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_22`. -/
theorem esq_aleat_22_momentos (t : ℝ) :
    (esq_aleat_22 t).momento 0 = 1 ∧ (esq_aleat_22 t).momento 1 = t/2 ∧ (esq_aleat_22 t).momento 2 = t^2/4 + t/2 := by
  sorry

/-- **Decidir aleat_22/a, sí.** En toda la región, `esq_aleat_22` cumple von Neumann. -/
theorem esq_aleat_22_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 42/41) → (esq_aleat_22 t).vonNeumann := by
  sorry

/-- **Decidir aleat_22/a, no.** Hay un punto de la región donde `esq_aleat_22` no cumple von Neumann. -/
theorem esq_aleat_22_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 42/41) ∧ ¬ (esq_aleat_22 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_22/a no es vacía. -/
theorem esq_aleat_22_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 42/41 := by
  sorry

/-- **aleat_23.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (1/4)·t, ν = (3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_23 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then 27*t^2/128 - 3*t/16 else if k = -1 then -27*t^2/128 + 29*t/32 else if k = 0 then -45*t^2/128 - 7*t/32 + 1 else if k = 1 then 63*t^2/128 - 25*t/32 else if k = 2 then -9*t^2/64 + 9*t/32 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_23`. -/
theorem esq_aleat_23_momentos (t : ℝ) :
    (esq_aleat_23 t).momento 0 = 1 ∧ (esq_aleat_23 t).momento 1 = -3*t/4 ∧ (esq_aleat_23 t).momento 2 = 9*t^2/16 + t/2 := by
  sorry

/-- **Decidir aleat_23/a, sí.** En toda la región, `esq_aleat_23` cumple von Neumann. -/
theorem esq_aleat_23_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 9/23) → (esq_aleat_23 t).vonNeumann := by
  sorry

/-- **Decidir aleat_23/a, no.** Hay un punto de la región donde `esq_aleat_23` no cumple von Neumann. -/
theorem esq_aleat_23_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 9/23) ∧ ¬ (esq_aleat_23 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_23/a no es vacía. -/
theorem esq_aleat_23_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 9/23 := by
  sorry

/-- **aleat_24.** Esquema explícito de cinco puntos generado al azar (semilla 20261027), consistente con u_t + c·u_x = α·u_xx (momentos 0, 1 y 2); el parámetro t escala el paso de tiempo con número de Péclet de malla fijo: r = (3/4)·t, ν = (3/4)·t. Origen: A9 v2, stencils aleatorios, semilla 20261027. -/
noncomputable def esq_aleat_24 (t : ℝ) : Esquema where
  S := {-2, -1, 0, 1, 2}
  a := fun k => if k = -2 then 3*t^2/32 + 9*t/16 else if k = -1 then 0 else if k = 0 then -9*t^2/32 - 3*t/2 + 1 else if k = 1 then 3*t^2/16 + 3*t/2 else if k = 2 then -9*t/16 else 0

/-- Momentos 0, 1 y 2 de `esq_aleat_24`. -/
theorem esq_aleat_24_momentos (t : ℝ) :
    (esq_aleat_24 t).momento 0 = 1 ∧ (esq_aleat_24 t).momento 1 = -3*t/4 ∧ (esq_aleat_24 t).momento 2 = 9*t^2/16 + 3*t/2 := by
  sorry

/-- **Decidir aleat_24/a, sí.** En toda la región, `esq_aleat_24` cumple von Neumann. -/
theorem esq_aleat_24_decide_a_si : ∀ t : ℝ, (0 ≤ t ∧ t ≤ 8/31) → (esq_aleat_24 t).vonNeumann := by
  sorry

/-- **Decidir aleat_24/a, no.** Hay un punto de la región donde `esq_aleat_24` no cumple von Neumann. -/
theorem esq_aleat_24_decide_a_no : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 8/31) ∧ ¬ (esq_aleat_24 t).vonNeumann := by
  sorry

/-- La región de decidir aleat_24/a no es vacía. -/
theorem esq_aleat_24_region_decide_a : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 8/31 := by
  sorry

end PrometeoLean.Esquemas

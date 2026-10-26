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

/-! ## A6. El lazo: esquemas propuestos por claude-opus-5-5 (claude -p) para dos modelos descubiertos. Caso 1: adv_dif_1d con α = 2·10⁻³, descubierto u_t = -0.9998·u_x (FTCS no simula); propuestas 20261025-120942, 5 muestras, 2 afirmaciones distintas. Caso 2: α = 5·10⁻³, descubierto u_t = -0.9998·u_x + 0.005001·u_xx (FTCS necesita 5 subpasos); propuestas 20261025-123211, 5 muestras, 1 afirmación distinta

Enunciados generados mecánicamente desde `esquemas_lazo_A6.json`; no se escriben a mano. -/

/-- **c1_lax_wendroff_1.** Lax-Wendroff explicito de segundo orden para adveccion pura, estable para |nu| <= 1 Origen: proponente claude-opus-5-5, muestra 1, 20261025-120942; también lax_wendroff_2 (proponente claude-opus-5-5, muestra 2, 20261025-120942); también lax_wendroff_4 (proponente claude-opus-5-5, muestra 4, 20261025-120942); también lax_wendroff_5 (proponente claude-opus-5-5, muestra 5, 20261025-120942). -/
noncomputable def esq_c1_lax_wendroff_1 (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then nu/2 + nu^2/2 else if k = 0 then 1 - nu^2 else if k = 1 then -nu/2 + nu^2/2 else 0

/-- Momentos 0, 1 y 2 de `esq_c1_lax_wendroff_1`. -/
theorem esq_c1_lax_wendroff_1_momentos (nu : ℝ) :
    (esq_c1_lax_wendroff_1 nu).momento 0 = 1 ∧ (esq_c1_lax_wendroff_1 nu).momento 1 = -nu ∧ (esq_c1_lax_wendroff_1 nu).momento 2 = nu^2 := by
  sorry

/-- **Decidir c1_lax_wendroff_1/lazo, sí.** En toda la región, `esq_c1_lax_wendroff_1` cumple von Neumann. -/
theorem esq_c1_lax_wendroff_1_decide_lazo_si : ∀ nu : ℝ, (-1 ≤ nu ∧ nu ≤ 1) → (esq_c1_lax_wendroff_1 nu).vonNeumann := by
  sorry

/-- **Decidir c1_lax_wendroff_1/lazo, no.** Hay un punto de la región donde `esq_c1_lax_wendroff_1` no cumple von Neumann. -/
theorem esq_c1_lax_wendroff_1_decide_lazo_no : ∃ nu : ℝ, (-1 ≤ nu ∧ nu ≤ 1) ∧ ¬ (esq_c1_lax_wendroff_1 nu).vonNeumann := by
  sorry

/-- La región de decidir c1_lax_wendroff_1/lazo no es vacía. -/
theorem esq_c1_lax_wendroff_1_region_decide_lazo : ∃ nu : ℝ, -1 ≤ nu ∧ nu ≤ 1 := by
  sorry

/-- **Instancia c1_lax_wendroff_1/corrida, sí.** Corrida del lazo sobre adv_dif_1d; modelo descubierto u_t = -0.9998·u_x. Subpasos n = 1; dx = 0.025, dt = 0.02, α = 0.0, v = 0.9998264460438153. -/
theorem esq_c1_lax_wendroff_1_decide_corrida_si : (esq_c1_lax_wendroff_1 (12978489287183359329473984574045/16225927682921337239877726502912)).vonNeumann := by
  sorry

/-- **Instancia c1_lax_wendroff_1/corrida, no.** -/
theorem esq_c1_lax_wendroff_1_decide_corrida_no : ¬ (esq_c1_lax_wendroff_1 (12978489287183359329473984574045/16225927682921337239877726502912)).vonNeumann := by
  sorry

/-- **c1_lax_wendroff_3.** Lax-Wendroff explicito de segundo orden para adveccion pura, estable para CFL |nu| <= 1 Origen: proponente claude-opus-5-5, muestra 3, 20261025-120942. -/
noncomputable def esq_c1_lax_wendroff_3 (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then (nu^2 + nu)/2 else if k = 0 then 1 - nu^2 else if k = 1 then (nu^2 - nu)/2 else 0

/-- Momentos 0, 1 y 2 de `esq_c1_lax_wendroff_3`. -/
theorem esq_c1_lax_wendroff_3_momentos (nu : ℝ) :
    (esq_c1_lax_wendroff_3 nu).momento 0 = 1 ∧ (esq_c1_lax_wendroff_3 nu).momento 1 = -nu ∧ (esq_c1_lax_wendroff_3 nu).momento 2 = nu^2 := by
  sorry

/-- **Decidir c1_lax_wendroff_3/lazo, sí.** En toda la región, `esq_c1_lax_wendroff_3` cumple von Neumann. -/
theorem esq_c1_lax_wendroff_3_decide_lazo_si : ∀ nu : ℝ, (nu^2 ≤ 1) → (esq_c1_lax_wendroff_3 nu).vonNeumann := by
  sorry

/-- **Decidir c1_lax_wendroff_3/lazo, no.** Hay un punto de la región donde `esq_c1_lax_wendroff_3` no cumple von Neumann. -/
theorem esq_c1_lax_wendroff_3_decide_lazo_no : ∃ nu : ℝ, (nu^2 ≤ 1) ∧ ¬ (esq_c1_lax_wendroff_3 nu).vonNeumann := by
  sorry

/-- La región de decidir c1_lax_wendroff_3/lazo no es vacía. -/
theorem esq_c1_lax_wendroff_3_region_decide_lazo : ∃ nu : ℝ, nu^2 ≤ 1 := by
  sorry

/-- **Instancia c1_lax_wendroff_3/corrida, sí.** Corrida del lazo sobre adv_dif_1d; modelo descubierto u_t = -0.9998·u_x. Subpasos n = 1; dx = 0.025, dt = 0.02, α = 0.0, v = 0.9998264460438153. -/
theorem esq_c1_lax_wendroff_3_decide_corrida_si : (esq_c1_lax_wendroff_3 (12978489287183359329473984574045/16225927682921337239877726502912)).vonNeumann := by
  sorry

/-- **Instancia c1_lax_wendroff_3/corrida, no.** -/
theorem esq_c1_lax_wendroff_3_decide_corrida_no : ¬ (esq_c1_lax_wendroff_3 (12978489287183359329473984574045/16225927682921337239877726502912)).vonNeumann := by
  sorry

/-- **c2_lax_wendroff_difusivo_1.** Lax-Wendroff para advección más difusión explícita centrada (FTCS con r efectivo r+nu^2/2), segundo orden Origen: proponente claude-opus-5-5, muestra 1, 20261025-123211; también lax_wendroff_difusivo_2 (proponente claude-opus-5-5, muestra 2, 20261025-123211); también lax_wendroff_difusivo_3 (proponente claude-opus-5-5, muestra 3, 20261025-123211); también lax_wendroff_adveccion_difusion_4 (proponente claude-opus-5-5, muestra 4, 20261025-123211); también lax_wendroff_difusivo_5 (proponente claude-opus-5-5, muestra 5, 20261025-123211). -/
noncomputable def esq_c2_lax_wendroff_difusivo_1 (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu/2 + nu^2/2 else if k = 0 then 1 - 2*r - nu^2 else if k = 1 then r - nu/2 + nu^2/2 else 0

/-- Momentos 0, 1 y 2 de `esq_c2_lax_wendroff_difusivo_1`. -/
theorem esq_c2_lax_wendroff_difusivo_1_momentos (r : ℝ) (nu : ℝ) :
    (esq_c2_lax_wendroff_difusivo_1 r nu).momento 0 = 1 ∧ (esq_c2_lax_wendroff_difusivo_1 r nu).momento 1 = -nu ∧ (esq_c2_lax_wendroff_difusivo_1 r nu).momento 2 = 2*r + nu^2 := by
  sorry

/-- **Decidir c2_lax_wendroff_difusivo_1/lazo, sí.** En toda la región, `esq_c2_lax_wendroff_difusivo_1` cumple von Neumann. -/
theorem esq_c2_lax_wendroff_difusivo_1_decide_lazo_si : ∀ r nu : ℝ, (0 ≤ r ∧ 2*r + nu^2 ≤ 1) → (esq_c2_lax_wendroff_difusivo_1 r nu).vonNeumann := by
  sorry

/-- **Decidir c2_lax_wendroff_difusivo_1/lazo, no.** Hay un punto de la región donde `esq_c2_lax_wendroff_difusivo_1` no cumple von Neumann. -/
theorem esq_c2_lax_wendroff_difusivo_1_decide_lazo_no : ∃ r nu : ℝ, (0 ≤ r ∧ 2*r + nu^2 ≤ 1) ∧ ¬ (esq_c2_lax_wendroff_difusivo_1 r nu).vonNeumann := by
  sorry

/-- La región de decidir c2_lax_wendroff_difusivo_1/lazo no es vacía. -/
theorem esq_c2_lax_wendroff_difusivo_1_region_decide_lazo : ∃ r nu : ℝ, 0 ≤ r ∧ 2*r + nu^2 ≤ 1 := by
  sorry

/-- **Instancia c2_lax_wendroff_difusivo_1/corrida, sí.** Corrida del lazo sobre adv_dif_1d (α del dato 0.005); modelo descubierto u_t = -0.9998·u_x +0.005001·u_xx. Subpasos n = 1; dx = 0.025, dt = 0.02, α = 0.005001105682158389, v = 0.9998162087847897. -/
theorem esq_c2_lax_wendroff_difusivo_1_decide_corrida_si : (esq_c2_lax_wendroff_difusivo_1 (16619024206509876078670308532485/103845937170696564099824972652872) (25956712799927325435395907181835/32451855365842674479755453005824)).vonNeumann := by
  sorry

/-- **Instancia c2_lax_wendroff_difusivo_1/corrida, no.** -/
theorem esq_c2_lax_wendroff_difusivo_1_decide_corrida_no : ¬ (esq_c2_lax_wendroff_difusivo_1 (16619024206509876078670308532485/103845937170696564099824972652872) (25956712799927325435395907181835/32451855365842674479755453005824)).vonNeumann := by
  sorry

end PrometeoLean.Esquemas

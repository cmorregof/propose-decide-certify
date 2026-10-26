import Mathlib

/-!
# A1. Von Neumann para FTCS (núcleo del diseño A)

PROPUESTA, no aprobada. Las pruebas van con `sorry` hasta que Carlos apruebe los enunciados.

Esquema FTCS para `u_t = α·u_xx` en la malla infinita `ℤ`, con `r = α·Δt/Δx²`:
`uⁿ⁺¹_j = uⁿ_j + r·(uⁿ_{j+1} - 2·uⁿ_j + uⁿ_{j-1})`.

Alcance (para que nadie lea de más):
- `ftcs_modo` liga el esquema con su factor de amplificación: los modos de Fourier son autovectores.
- `ftcs_vonNeumann` es la condición de von Neumann `|g(θ)| ≤ 1 ∀θ ⇔ r ≤ 1/2`.
- NO se prueba aquí que von Neumann implique estabilidad en ℓ² (eso pide Parseval discreto), ni
  nada sobre fronteras Dirichlet o coeficientes variables (Burgers, Fisher-KPP).
- Los dos controles son enunciados FALSOS: el juez debe rechazar cualquier «prueba» de ellos. Sus
  refutaciones (`..._falso`) sí son demostrables y certifican que el control es falso.
-/

namespace PrometeoLean.Esquemas

open Complex

/-- Un paso de FTCS para la ecuación del calor, con `r = α·Δt/Δx²`. -/
noncomputable def ftcs (r : ℝ) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun j => u j + r * (u (j + 1) - 2 * u j + u (j - 1))

/-- Factor de amplificación de FTCS: `g(θ) = 1 - 4·r·sin²(θ/2)`. -/
noncomputable def gFTCS (r θ : ℝ) : ℝ := 1 - 4 * r * Real.sin (θ / 2) ^ 2

/-- **A1.0 (símbolo).** El modo de Fourier `j ↦ exp(i·j·θ)` es autovector de FTCS con autovalor
`gFTCS r θ`. -/
theorem ftcs_modo (r θ : ℝ) (j : ℤ) :
    ftcs r (fun k => Complex.exp (((k : ℝ) * θ : ℝ) * I)) j
      = (gFTCS r θ : ℂ) * Complex.exp (((j : ℝ) * θ : ℝ) * I) := by
  sorry

/-- **A1.1 (von Neumann, directo y recíproco).** Para `r ≥ 0`, el factor de amplificación cumple
`|g(θ)| ≤ 1` para todo `θ` si y solo si `r ≤ 1/2`. -/
theorem ftcs_vonNeumann (r : ℝ) (hr : 0 ≤ r) :
    (∀ θ : ℝ, |gFTCS r θ| ≤ 1) ↔ r ≤ 1 / 2 := by
  sorry

/-- **Control falso F1.** «FTCS cumple von Neumann para todo `0 ≤ r ≤ 1`». Falso: con `r = 1` y
`θ = π`, `g = -3`. -/
def controlF1 : Prop := ∀ r θ : ℝ, 0 ≤ r → r ≤ 1 → |gFTCS r θ| ≤ 1

/-- Refutación de F1. -/
theorem controlF1_falso : ¬ controlF1 := by
  sorry

/-- Factor de amplificación de FTCS para la advección `u_t + a·u_x = 0`, con `ν = a·Δt/Δx`:
`g(θ) = 1 - i·ν·sin θ`. -/
noncomputable def gFTCSadv (ν θ : ℝ) : ℂ := 1 - ν * Real.sin θ * I

/-- **Control falso F2.** «Hay un `ν ≠ 0` con el que FTCS para advección cumple von Neumann». Falso:
`‖g(θ)‖² = 1 + ν²·sin²θ`. Es la razón por la que el FD del cuaderno rechaza advección centrada sin
difusión. -/
def controlF2 : Prop := ∃ ν : ℝ, ν ≠ 0 ∧ ∀ θ : ℝ, ‖gFTCSadv ν θ‖ ≤ 1

/-- Refutación de F2. -/
theorem controlF2_falso : ¬ controlF2 := by
  sorry

end PrometeoLean.Esquemas

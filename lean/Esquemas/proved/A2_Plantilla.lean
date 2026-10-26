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
  unfold paso simbolo
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  beta_reduce
  have e : Complex.exp ((((j + k : ℤ) : ℝ) * θ : ℝ) * I)
      = Complex.exp (((k : ℝ) * θ : ℝ) * I) * Complex.exp (((j : ℝ) * θ : ℝ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

/-- **A2.1.** El símbolo en partes real e imaginaria. -/
theorem simbolo_eq (E : Esquema) (θ : ℝ) :
    E.simbolo θ = ((∑ k ∈ E.S, E.a k * Real.cos ((k : ℝ) * θ) : ℝ) : ℂ)
      + ((∑ k ∈ E.S, E.a k * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * I := by
  rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  unfold simbolo
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.exp_mul_I]
  push_cast
  ring

/-- **A2.2′ (forma polinomial).** Von Neumann equivale a una desigualdad en senos y cosenos:
`(Σ a_k cos kθ)² + (Σ a_k sin kθ)² ≤ 1` para todo `θ`. -/
theorem vonNeumann_iff_sq (E : Esquema) :
    E.vonNeumann ↔ ∀ θ : ℝ, (∑ k ∈ E.S, E.a k * Real.cos ((k : ℝ) * θ)) ^ 2
      + (∑ k ∈ E.S, E.a k * Real.sin ((k : ℝ) * θ)) ^ 2 ≤ 1 := by
  unfold vonNeumann
  refine forall_congr' (fun θ => ?_)
  rw [simbolo_eq, Complex.norm_add_mul_I, Real.sqrt_le_one]

/-- **A2.2 (necesaria).** Si el esquema cumple von Neumann, entonces `|Σ a_k| ≤ 1`. -/
theorem vonNeumann_momento_cero (E : Esquema) (h : E.vonNeumann) : |E.momento 0| ≤ 1 := by
  have h0 : ‖E.simbolo 0‖ ≤ 1 := h 0
  have e : E.simbolo 0 = ((E.momento 0 : ℝ) : ℂ) := by
    unfold simbolo momento
    push_cast
    simp
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h0
  exact h0

/-- **A2.3.** Un esquema positivo cumple von Neumann. -/
theorem vonNeumann_de_positivo (E : Esquema) (h : E.Positivo) : E.vonNeumann := by
  intro θ
  obtain ⟨hpos, h1⟩ := h
  have h1' : ∑ k ∈ E.S, E.a k = 1 := by simpa [momento] using h1
  calc ‖E.simbolo θ‖ ≤ ∑ k ∈ E.S, ‖(E.a k : ℂ) * Complex.exp (((k : ℝ) * θ : ℝ) * I)‖ := by
        unfold simbolo; exact norm_sum_le _ _
    _ = ∑ k ∈ E.S, E.a k := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hpos k hk)]
    _ = 1 := h1'

/-- **A2.4 (principio del máximo, un paso).** Si `E` es positivo y `|u_j| ≤ M` para todo `j`,
entonces `|(E u)_j| ≤ M` para todo `j`. -/
theorem pasoR_acotado (E : Esquema) (h : E.Positivo) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |E.pasoR u j| ≤ M := by
  obtain ⟨hpos, h1⟩ := h
  have h1' : ∑ k ∈ E.S, E.a k = 1 := by simpa [momento] using h1
  calc |E.pasoR u j| ≤ ∑ k ∈ E.S, |E.a k * u (j + k)| := by
        unfold pasoR; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ E.S, E.a k * M := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [abs_mul, abs_of_nonneg (hpos k hk)]
        exact mul_le_mul_of_nonneg_left (hu _) (hpos k hk)
    _ = M := by rw [← Finset.sum_mul, h1', one_mul]

/-- **A2.5 (estabilidad en norma del supremo).** Lo mismo para `n` pasos, con la misma cota. -/
theorem pasoR_iterado_acotado (E : Esquema) (h : E.Positivo) (u : ℤ → ℝ) (M : ℝ)
    (hu : ∀ j, |u j| ≤ M) (n : ℕ) (j : ℤ) : |(E.pasoR)^[n] u j| ≤ M := by
  have key : ∀ m : ℕ, ∀ v : ℤ → ℝ, (∀ i, |v i| ≤ M) → ∀ i, |(E.pasoR)^[m] v i| ≤ M := by
    intro m
    induction m with
    | zero => intro v hv i; exact hv i
    | succ m ih =>
      intro v hv i
      show |(E.pasoR)^[m] (E.pasoR v) i| ≤ M
      exact ih (E.pasoR v) (fun i' => pasoR_acotado E h v M hv i') i
  exact key n u hu j

end Esquema

/-- Lax-Wendroff para `u_t + c·u_x = 0`, con `ν = c·Δt/Δx`:
`uⁿ⁺¹_j = uⁿ_j - (ν/2)(uⁿ_{j+1} - uⁿ_{j-1}) + (ν²/2)(uⁿ_{j+1} - 2uⁿ_j + uⁿ_{j-1})`. -/
noncomputable def laxWendroff (ν : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then ν * (1 + ν) / 2 else if k = 0 then 1 - ν ^ 2
    else if k = 1 then -(ν * (1 - ν)) / 2 else 0

/-- Parte real del símbolo de Lax-Wendroff. -/
theorem laxWendroff_re (ν θ : ℝ) :
    ∑ k ∈ (laxWendroff ν).S, (laxWendroff ν).a k * Real.cos ((k : ℝ) * θ)
      = ν ^ 2 * Real.cos θ + (1 - ν ^ 2) := by
  simp [laxWendroff, Finset.sum_insert, Real.cos_neg]
  ring

/-- Parte imaginaria del símbolo de Lax-Wendroff. -/
theorem laxWendroff_im (ν θ : ℝ) :
    ∑ k ∈ (laxWendroff ν).S, (laxWendroff ν).a k * Real.sin ((k : ℝ) * θ) = -ν * Real.sin θ := by
  simp [laxWendroff, Finset.sum_insert, Real.sin_neg]
  ring

/-- **A2.6.** Lax-Wendroff cumple von Neumann si y solo si `|ν| ≤ 1`. -/
theorem laxWendroff_vonNeumann_iff (ν : ℝ) : (laxWendroff ν).vonNeumann ↔ |ν| ≤ 1 := by
  constructor
  · intro h
    have hπ : ‖(laxWendroff ν).simbolo Real.pi‖ ≤ 1 := h Real.pi
    rw [Esquema.simbolo_eq, laxWendroff_re, laxWendroff_im, Complex.norm_add_mul_I,
      Real.sqrt_le_one, Real.cos_pi, Real.sin_pi] at hπ
    have h2 : ν ^ 2 ≤ 1 := by nlinarith [sq_nonneg ν, sq_nonneg (ν ^ 2 - 1)]
    exact (sq_le_one_iff_abs_le_one ν).mp h2
  · intro hν θ
    have h1 : 0 ≤ 1 - ν ^ 2 := by
      have := (sq_le_one_iff_abs_le_one ν).mpr hν
      linarith
    have hP : 0 ≤ ν ^ 2 * (1 - ν ^ 2) * (1 - Real.cos θ) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg ν) h1) (sq_nonneg _)
    have hsc : ν ^ 2 * Real.sin θ ^ 2 = ν ^ 2 - ν ^ 2 * Real.cos θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linear_combination ν ^ 2 * this
    rw [Esquema.simbolo_eq, laxWendroff_re, laxWendroff_im, Complex.norm_add_mul_I, Real.sqrt_le_one]
    nlinarith [hP, hsc]

/-- **Control falso P.** «Todo esquema que cumple von Neumann es positivo». Falso: Lax-Wendroff con
`ν = 1/2` cumple von Neumann y tiene `a_1 = -1/8`. -/
def controlPositividad : Prop :=
  ∀ E : Esquema, E.vonNeumann → E.Positivo

/-- Refutación del control P. -/
theorem controlPositividad_falso : ¬ controlPositividad := by
  intro h
  unfold controlPositividad at h
  have hv : (laxWendroff (1 / 2)).vonNeumann :=
    (laxWendroff_vonNeumann_iff (1 / 2)).mpr (by rw [abs_le]; constructor <;> norm_num)
  obtain ⟨hpos, _⟩ := h _ hv
  have h1 := hpos 1 (by simp [laxWendroff])
  norm_num [laxWendroff] at h1

end PrometeoLean.Esquemas

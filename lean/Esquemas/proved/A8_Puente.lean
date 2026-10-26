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

/-! ## A3. Corpus inicial de esquemas (diseño A)

Enunciados generados mecánicamente desde `esquemas_corpus_A3.json`; no se escriben a mano. -/

/-- **ftcs_calor.** FTCS para u_t = α·u_xx, con r = α·Δt/Δx². Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_ftcs_calor (r : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r else if k = 0 then 1 - 2 * r else if k = 1 then r else 0

/-- Parte real del símbolo de `esq_ftcs_calor`. -/
theorem esq_ftcs_calor_re (r : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * Real.cos ((k : ℝ) * θ) = 1 - 2 * r + 2 * r * Real.cos θ := by
  simp [esq_ftcs_calor, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Parte imaginaria del símbolo de `esq_ftcs_calor`. -/
theorem esq_ftcs_calor_im (r : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * Real.sin ((k : ℝ) * θ) = 0 := by
  simp [esq_ftcs_calor, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Momentos 0, 1 y 2 de `esq_ftcs_calor`. -/
theorem esq_ftcs_calor_momentos (r : ℝ) :
    (esq_ftcs_calor r).momento 0 = 1 ∧ (esq_ftcs_calor r).momento 1 = 0 ∧ (esq_ftcs_calor r).momento 2 = 2 * r := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_ftcs_calor, Esquema.momento, Finset.sum_insert] <;> ring

/-- Región exacta de von Neumann de `esq_ftcs_calor`. -/
theorem esq_ftcs_calor_vonNeumann_iff (r : ℝ) : (esq_ftcs_calor r).vonNeumann ↔ (0 ≤ r ∧ r ≤ 1 / 2) := by
  rw [Esquema.vonNeumann_iff_sq]
  simp only [esq_ftcs_calor_re, esq_ftcs_calor_im]
  constructor
  · intro h
    have hπ := h Real.pi
    rw [Real.cos_pi] at hπ
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩ θ
    have hc1 := Real.cos_le_one θ
    have hc0 := Real.neg_one_le_cos θ
    have hw : 0 ≤ 1 - Real.cos θ := by linarith
    have hrw : 0 ≤ 1 - r * (1 - Real.cos θ) := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg h0 hw) hrw]

/-- `esq_ftcs_calor` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_ftcs_calor_positivo (r : ℝ) (h : 0 ≤ r ∧ r ≤ 1 / 2) : (esq_ftcs_calor r).Positivo := by
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [esq_ftcs_calor, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> simp [esq_ftcs_calor] <;> (try obtain ⟨_, _, _⟩ := h) <;> (try obtain ⟨_, _⟩ := h) <;> linarith
  · simp [esq_ftcs_calor, Esquema.momento, Finset.sum_insert]; ring

/-- La región «estable_sii» de `esq_ftcs_calor` no es vacía. -/
theorem esq_ftcs_calor_region_estable : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 := by
  exact ⟨(1/4 : ℝ), by norm_num⟩

/-- La región «positivo_si» de `esq_ftcs_calor` no es vacía. -/
theorem esq_ftcs_calor_region_positivo : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 := by
  exact ⟨(1/4 : ℝ), by norm_num⟩

/-- **upwind.** Upwind para u_t + c·u_x = 0 con c > 0, ν = c·Δt/Δx. Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_upwind (nu : ℝ) : Esquema where
  S := {-1, 0}
  a := fun k => if k = -1 then nu else if k = 0 then 1 - nu else 0

/-- Parte real del símbolo de `esq_upwind`. -/
theorem esq_upwind_re (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_upwind nu).S, (esq_upwind nu).a k * Real.cos ((k : ℝ) * θ) = nu * Real.cos θ + (1 - nu) := by
  simp [esq_upwind, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Parte imaginaria del símbolo de `esq_upwind`. -/
theorem esq_upwind_im (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_upwind nu).S, (esq_upwind nu).a k * Real.sin ((k : ℝ) * θ) = -nu * Real.sin θ := by
  simp [esq_upwind, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Momentos 0, 1 y 2 de `esq_upwind`. -/
theorem esq_upwind_momentos (nu : ℝ) :
    (esq_upwind nu).momento 0 = 1 ∧ (esq_upwind nu).momento 1 = -nu ∧ (esq_upwind nu).momento 2 = nu := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_upwind, Esquema.momento, Finset.sum_insert] <;> ring

/-- Región exacta de von Neumann de `esq_upwind`. -/
theorem esq_upwind_vonNeumann_iff (nu : ℝ) : (esq_upwind nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 1) := by
  rw [Esquema.vonNeumann_iff_sq]
  simp only [esq_upwind_re, esq_upwind_im]
  constructor
  · intro h
    have hπ := h Real.pi
    rw [Real.cos_pi, Real.sin_pi] at hπ
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩ θ
    have hw : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    have hsc : nu ^ 2 * Real.sin θ ^ 2 = nu ^ 2 * (1 - Real.cos θ ^ 2) := by rw [Real.sin_sq]
    nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) hw]

/-- `esq_upwind` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_upwind_positivo (nu : ℝ) (h : 0 ≤ nu ∧ nu ≤ 1) : (esq_upwind nu).Positivo := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [esq_upwind, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [esq_upwind] <;> linarith
  · simp [esq_upwind, Esquema.momento, Finset.sum_insert]

/-- La región «estable_sii» de `esq_upwind` no es vacía. -/
theorem esq_upwind_region_estable : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 := by
  exact ⟨(1/2 : ℝ), by norm_num⟩

/-- La región «positivo_si» de `esq_upwind` no es vacía. -/
theorem esq_upwind_region_positivo : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 := by
  exact ⟨(1/2 : ℝ), by norm_num⟩

/-- **downwind.** Downwind (diferencia hacia adelante) para u_t + c·u_x = 0. Origen: control falso. -/
noncomputable def esq_downwind (nu : ℝ) : Esquema where
  S := {0, 1}
  a := fun k => if k = 0 then 1 + nu else if k = 1 then -nu else 0

/-- Momentos 0, 1 y 2 de `esq_downwind`. -/
theorem esq_downwind_momentos (nu : ℝ) :
    (esq_downwind nu).momento 0 = 1 ∧ (esq_downwind nu).momento 1 = -nu ∧ (esq_downwind nu).momento 2 = -nu := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_downwind, Esquema.momento, Finset.sum_insert] <;> ring

/-- **Control.** `esq_downwind` no cumple von Neumann si 0 < nu. -/
theorem esq_downwind_inestable (nu : ℝ) (h : 0 < nu) : ¬ (esq_downwind nu).vonNeumann := by
  rw [Esquema.vonNeumann_iff_sq]
  intro hv
  have h1 := hv Real.pi
  have h2 := hv (Real.pi / 2)
  simp only [esq_downwind, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  norm_num [Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg] at h1 h2
  nlinarith [sq_nonneg nu]

/-- La región «inestable_si» de `esq_downwind` no es vacía. -/
theorem esq_downwind_region_inestable : ∃ nu : ℝ, 0 < nu := by
  exact ⟨(1/2 : ℝ), by norm_num⟩

/-- **ftcs_adveccion.** FTCS centrado para u_t + c·u_x = 0. Origen: control falso. -/
noncomputable def esq_ftcs_adveccion (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then nu / 2 else if k = 0 then 1 else if k = 1 then -nu / 2 else 0

/-- Parte real del símbolo de `esq_ftcs_adveccion`. -/
theorem esq_ftcs_adveccion_re (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_ftcs_adveccion nu).S, (esq_ftcs_adveccion nu).a k * Real.cos ((k : ℝ) * θ) = 1 := by
  simp [esq_ftcs_adveccion, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Parte imaginaria del símbolo de `esq_ftcs_adveccion`. -/
theorem esq_ftcs_adveccion_im (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_ftcs_adveccion nu).S, (esq_ftcs_adveccion nu).a k * Real.sin ((k : ℝ) * θ) = -nu * Real.sin θ := by
  simp [esq_ftcs_adveccion, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Momentos 0, 1 y 2 de `esq_ftcs_adveccion`. -/
theorem esq_ftcs_adveccion_momentos (nu : ℝ) :
    (esq_ftcs_adveccion nu).momento 0 = 1 ∧ (esq_ftcs_adveccion nu).momento 1 = -nu ∧ (esq_ftcs_adveccion nu).momento 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_ftcs_adveccion, Esquema.momento, Finset.sum_insert] <;> ring

/-- **Control.** `esq_ftcs_adveccion` no cumple von Neumann si nu ≠ 0. -/
theorem esq_ftcs_adveccion_inestable (nu : ℝ) (h : nu ≠ 0) : ¬ (esq_ftcs_adveccion nu).vonNeumann := by
  rw [Esquema.vonNeumann_iff_sq]
  intro hv
  have h2 := hv (Real.pi / 2)
  rw [esq_ftcs_adveccion_re, esq_ftcs_adveccion_im, Real.sin_pi_div_two] at h2
  have : 0 < nu ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 h).symm
  nlinarith

/-- La región «inestable_si» de `esq_ftcs_adveccion` no es vacía. -/
theorem esq_ftcs_adveccion_region_inestable : ∃ nu : ℝ, nu ≠ 0 := by
  exact ⟨(1/2 : ℝ), by norm_num⟩

/-- **lax_friedrichs.** Lax-Friedrichs para u_t + c·u_x = 0. Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_lax_friedrichs (nu : ℝ) : Esquema where
  S := {-1, 1}
  a := fun k => if k = -1 then (1 + nu) / 2 else if k = 1 then (1 - nu) / 2 else 0

/-- Parte real del símbolo de `esq_lax_friedrichs`. -/
theorem esq_lax_friedrichs_re (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_lax_friedrichs nu).S, (esq_lax_friedrichs nu).a k * Real.cos ((k : ℝ) * θ) = Real.cos θ := by
  simp [esq_lax_friedrichs, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Parte imaginaria del símbolo de `esq_lax_friedrichs`. -/
theorem esq_lax_friedrichs_im (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_lax_friedrichs nu).S, (esq_lax_friedrichs nu).a k * Real.sin ((k : ℝ) * θ) = -nu * Real.sin θ := by
  simp [esq_lax_friedrichs, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Momentos 0, 1 y 2 de `esq_lax_friedrichs`. -/
theorem esq_lax_friedrichs_momentos (nu : ℝ) :
    (esq_lax_friedrichs nu).momento 0 = 1 ∧ (esq_lax_friedrichs nu).momento 1 = -nu ∧ (esq_lax_friedrichs nu).momento 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_lax_friedrichs, Esquema.momento, Finset.sum_insert] <;> ring

/-- Región exacta de von Neumann de `esq_lax_friedrichs`. -/
theorem esq_lax_friedrichs_vonNeumann_iff (nu : ℝ) : (esq_lax_friedrichs nu).vonNeumann ↔ (-1 ≤ nu ∧ nu ≤ 1) := by
  rw [Esquema.vonNeumann_iff_sq]
  simp only [esq_lax_friedrichs_re, esq_lax_friedrichs_im]
  constructor
  · intro h
    have h2 := h (Real.pi / 2)
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at h2
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩ θ
    have hsc := Real.sin_sq_add_cos_sq θ
    have hP : 0 ≤ (1 - nu ^ 2) * Real.sin θ ^ 2 :=
      mul_nonneg (by nlinarith) (sq_nonneg _)
    nlinarith

/-- `esq_lax_friedrichs` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_lax_friedrichs_positivo (nu : ℝ) (h : -1 ≤ nu ∧ nu ≤ 1) : (esq_lax_friedrichs nu).Positivo := by
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [esq_lax_friedrichs, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> simp [esq_lax_friedrichs] <;> (try obtain ⟨_, _, _⟩ := h) <;> (try obtain ⟨_, _⟩ := h) <;> linarith
  · simp [esq_lax_friedrichs, Esquema.momento, Finset.sum_insert]; ring

/-- La región «estable_sii» de `esq_lax_friedrichs` no es vacía. -/
theorem esq_lax_friedrichs_region_estable : ∃ nu : ℝ, -1 ≤ nu ∧ nu ≤ 1 := by
  exact ⟨(1/2 : ℝ), by norm_num⟩

/-- La región «positivo_si» de `esq_lax_friedrichs` no es vacía. -/
theorem esq_lax_friedrichs_region_positivo : ∃ nu : ℝ, -1 ≤ nu ∧ nu ≤ 1 := by
  exact ⟨(1/2 : ℝ), by norm_num⟩

/-- **beam_warming.** Beam-Warming (upwind de segundo orden) para u_t + c·u_x = 0. Origen: corpus de calibración (libro de texto). -/
noncomputable def esq_beam_warming (nu : ℝ) : Esquema where
  S := {-2, -1, 0}
  a := fun k => if k = -2 then nu * (nu - 1) / 2 else if k = -1 then nu * (2 - nu) else if k = 0 then (1 - nu) * (2 - nu) / 2 else 0

/-- Parte real del símbolo de `esq_beam_warming`. -/
theorem esq_beam_warming_re (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_beam_warming nu).S, (esq_beam_warming nu).a k * Real.cos ((k : ℝ) * θ) = nu * (nu - 1) / 2 * (2 * Real.cos θ ^ 2 - 1) + nu * (2 - nu) * Real.cos θ + (1 - nu) * (2 - nu) / 2 := by
  simp [esq_beam_warming, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Parte imaginaria del símbolo de `esq_beam_warming`. -/
theorem esq_beam_warming_im (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_beam_warming nu).S, (esq_beam_warming nu).a k * Real.sin ((k : ℝ) * θ) = -(nu * (nu - 1) / 2) * (2 * Real.sin θ * Real.cos θ) - nu * (2 - nu) * Real.sin θ := by
  simp [esq_beam_warming, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Momentos 0, 1 y 2 de `esq_beam_warming`. -/
theorem esq_beam_warming_momentos (nu : ℝ) :
    (esq_beam_warming nu).momento 0 = 1 ∧ (esq_beam_warming nu).momento 1 = -nu ∧ (esq_beam_warming nu).momento 2 = nu ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_beam_warming, Esquema.momento, Finset.sum_insert] <;> ring

/-- Región exacta de von Neumann de `esq_beam_warming`. -/
theorem esq_beam_warming_vonNeumann_iff (nu : ℝ) : (esq_beam_warming nu).vonNeumann ↔ (0 ≤ nu ∧ nu ≤ 2) := by
  rw [Esquema.vonNeumann_iff_sq]
  simp only [esq_beam_warming_re, esq_beam_warming_im]
  constructor
  · intro h
    have hπ := h Real.pi
    rw [Real.cos_pi, Real.sin_pi] at hπ
    have hf : 4 * nu * (nu - 2) * (nu - 1) ^ 2 ≤ 0 := by nlinarith
    constructor
    · by_contra hn
      push_neg at hn
      have h1 : 0 < nu * (nu - 2) := by nlinarith
      have h2 : 0 < (nu - 1) ^ 2 := by nlinarith
      nlinarith [mul_pos h1 h2]
    · by_contra hn
      push_neg at hn
      have h1 : 0 < nu * (nu - 2) := by nlinarith
      have h2 : 0 < (nu - 1) ^ 2 := by nlinarith
      nlinarith [mul_pos h1 h2]
  · rintro ⟨h0, h1⟩ θ
    have hsc : nu ^ 2 * (Real.cos θ * nu - Real.cos θ - nu + 2) ^ 2 * Real.sin θ ^ 2
        = nu ^ 2 * (Real.cos θ * nu - Real.cos θ - nu + 2) ^ 2 * (1 - Real.cos θ ^ 2) := by
      rw [Real.sin_sq]
    have hP : 0 ≤ nu * (2 - nu) * (nu - 1) ^ 2 * (1 - Real.cos θ) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)) (sq_nonneg _)
    nlinarith [hP, hsc]

/-- La región «estable_sii» de `esq_beam_warming` no es vacía. -/
theorem esq_beam_warming_region_estable : ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 2 := by
  exact ⟨(1 : ℝ), by norm_num⟩

/-- **ftcs_conv_dif.** FTCS para u_t + c·u_x = α·u_xx (advección centrada), con r = α·Δt/Δx² y ν = c·Δt/Δx; es el esquema del FD del cuaderno de PINNs. Origen: cuaderno Framework_PINN_EspacioTemporal (tarea 0). -/
noncomputable def esq_ftcs_conv_dif (r : ℝ) (nu : ℝ) : Esquema where
  S := {-1, 0, 1}
  a := fun k => if k = -1 then r + nu / 2 else if k = 0 then 1 - 2 * r else if k = 1 then r - nu / 2 else 0

/-- Parte real del símbolo de `esq_ftcs_conv_dif`. -/
theorem esq_ftcs_conv_dif_re (r : ℝ) (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_ftcs_conv_dif r nu).S, (esq_ftcs_conv_dif r nu).a k * Real.cos ((k : ℝ) * θ) = 1 - 2 * r + 2 * r * Real.cos θ := by
  simp [esq_ftcs_conv_dif, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Parte imaginaria del símbolo de `esq_ftcs_conv_dif`. -/
theorem esq_ftcs_conv_dif_im (r : ℝ) (nu : ℝ) (θ : ℝ) :
    ∑ k ∈ (esq_ftcs_conv_dif r nu).S, (esq_ftcs_conv_dif r nu).a k * Real.sin ((k : ℝ) * θ) = -nu * Real.sin θ := by
  simp [esq_ftcs_conv_dif, Finset.sum_insert, Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
  try ring

/-- Momentos 0, 1 y 2 de `esq_ftcs_conv_dif`. -/
theorem esq_ftcs_conv_dif_momentos (r : ℝ) (nu : ℝ) :
    (esq_ftcs_conv_dif r nu).momento 0 = 1 ∧ (esq_ftcs_conv_dif r nu).momento 1 = -nu ∧ (esq_ftcs_conv_dif r nu).momento 2 = 2 * r := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [esq_ftcs_conv_dif, Esquema.momento, Finset.sum_insert] <;> ring

/-- Región exacta de von Neumann de `esq_ftcs_conv_dif`. -/
theorem esq_ftcs_conv_dif_vonNeumann_iff (r : ℝ) (nu : ℝ) : (esq_ftcs_conv_dif r nu).vonNeumann ↔ (nu ^ 2 ≤ 2 * r ∧ 2 * r ≤ 1) := by
  rw [Esquema.vonNeumann_iff_sq]
  simp only [esq_ftcs_conv_dif_re, esq_ftcs_conv_dif_im]
  constructor
  · intro h
    have hπ := h Real.pi
    rw [Real.cos_pi, Real.sin_pi] at hπ
    have hr : 2 * r ≤ 1 := by nlinarith
    refine ⟨?_, hr⟩
    by_contra hA
    push_neg at hA
    -- A = 4r - 2ν² < 0: con w = -A / (-A + 2(B² + 1)) y cos θ = 1 - w, |g(θ)| > 1
    set A := 4 * r - 2 * nu ^ 2 with hAdef
    set B := 4 * r ^ 2 - nu ^ 2 with hBdef
    have hAneg : A < 0 := by rw [hAdef]; linarith
    set D := -A + 2 * (B ^ 2 + 1) with hDdef
    have hD : 0 < D := by rw [hDdef]; nlinarith [sq_nonneg B]
    set w := -A / D with hwdef
    have hw0 : 0 < w := div_pos (by linarith) hD
    have hw1 : w ≤ 1 := by
      rw [hwdef, div_le_one hD, hDdef]; nlinarith [sq_nonneg B]
    have hθ := h (Real.arccos (1 - w))
    rw [Real.cos_arccos (by linarith) (by linarith), Real.sin_arccos] at hθ
    have hs2 : Real.sqrt (1 - (1 - w) ^ 2) ^ 2 = 1 - (1 - w) ^ 2 :=
      Real.sq_sqrt (by nlinarith)
    have hid : (1 - 2 * r + 2 * r * (1 - w)) ^ 2 + (-nu * Real.sqrt (1 - (1 - w) ^ 2)) ^ 2
        = 1 - w * (A - w * B) := by
      rw [mul_pow, hs2, hAdef, hBdef]; ring
    rw [hid] at hθ
    have hneg : w * (A - w * B) < 0 := by
      have e : w * (A - w * B) = -(A ^ 2 * (D + B)) / D ^ 2 := by
        rw [hwdef]; field_simp; ring
      rw [e]
      apply div_neg_of_neg_of_pos _ (pow_pos hD 2)
      have hDB : 0 < D + B := by rw [hDdef]; nlinarith [sq_nonneg (2 * B + 1 / 2)]
      have hA2 : 0 < A ^ 2 := lt_of_le_of_ne (sq_nonneg A) (pow_ne_zero 2 hAneg.ne).symm
      nlinarith [mul_pos hA2 hDB]
    linarith
  · rintro ⟨h0, h1⟩ θ
    have hc1 := Real.cos_le_one θ
    have hc0 := Real.neg_one_le_cos θ
    have hr0 : 0 ≤ r := by nlinarith [sq_nonneg nu]
    have hw : 0 ≤ 1 - Real.cos θ := by linarith
    have hw2 : 0 ≤ 1 - (1 - Real.cos θ) / 2 := by linarith
    have hA : 0 ≤ 4 * r - 2 * nu ^ 2 := by linarith
    have hA2 : 0 ≤ 4 * r * (1 - 2 * r) := mul_nonneg (by linarith) (by linarith)
    have hsc : nu ^ 2 * Real.sin θ ^ 2 = nu ^ 2 * (1 - Real.cos θ ^ 2) := by rw [Real.sin_sq]
    nlinarith [mul_nonneg (mul_nonneg hw hw2) hA, mul_nonneg (mul_nonneg hw (div_nonneg hw (by norm_num : (0:ℝ) ≤ 2))) hA2]

/-- `esq_ftcs_conv_dif` es positivo (y cumple el principio del máximo, A2.5) en esta región. -/
theorem esq_ftcs_conv_dif_positivo (r : ℝ) (nu : ℝ) (h : nu ≤ 2 * r ∧ -nu ≤ 2 * r ∧ r ≤ 1 / 2) : (esq_ftcs_conv_dif r nu).Positivo := by
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [esq_ftcs_conv_dif, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> simp [esq_ftcs_conv_dif] <;> (try obtain ⟨_, _, _⟩ := h) <;> (try obtain ⟨_, _⟩ := h) <;> linarith
  · simp [esq_ftcs_conv_dif, Esquema.momento, Finset.sum_insert]; ring

/-- La región «estable_sii» de `esq_ftcs_conv_dif` no es vacía. -/
theorem esq_ftcs_conv_dif_region_estable : ∃ r nu : ℝ, nu ^ 2 ≤ 2 * r ∧ 2 * r ≤ 1 := by
  exact ⟨(1/4 : ℝ), (1/2 : ℝ), by norm_num⟩

/-- La región «positivo_si» de `esq_ftcs_conv_dif` no es vacía. -/
theorem esq_ftcs_conv_dif_region_positivo : ∃ r nu : ℝ, nu ≤ 2 * r ∧ -nu ≤ 2 * r ∧ r ≤ 1 / 2 := by
  exact ⟨(1/4 : ℝ), (1/2 : ℝ), by norm_num⟩


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

/-- Taylor de orden `n` con resto de Lagrange en un punto (a ambos lados de `x`). -/
theorem taylor_punto (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1) f) (K : ℝ) (x d : ℝ)
    (hK : ∀ y ∈ Set.uIcc x (x + d), |iteratedDeriv (n + 1) f y| ≤ K) :
    |f (x + d) - ∑ m ∈ Finset.range (n + 1), d ^ m / (Nat.factorial m : ℝ) * iteratedDeriv m f x|
      ≤ K * |d| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [Finset.sum_range_succ']
  · have hx : x ≠ x + d := by intro h; apply hd; linarith
    obtain ⟨x', hx', h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hf.contDiffOn
    have hu := uniqueDiffOn_uIcc hx
    have hpoly : taylorWithinEval f n (Set.uIcc x (x + d)) x (x + d)
        = ∑ m ∈ Finset.range (n + 1), d ^ m / (Nat.factorial m : ℝ) * iteratedDeriv m f x := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm' : m ≤ n + 1 := by have := Finset.mem_range.mp hm; omega
      rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
        iteratedFDerivWithin_eq_iteratedFDeriv hu (hf.contDiffAt.of_le (by exact_mod_cast hm'))
          Set.left_mem_uIcc, ← iteratedDeriv_eq_iteratedFDeriv]
      simp only [smul_eq_mul, add_sub_cancel_left]
      ring
    rw [← hpoly, h, add_sub_cancel_left, abs_div, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ))]
    gcongr
    exact hK x' (Set.uIoo_subset_uIcc_self hx')

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
  have e : ∑ m ∈ Finset.range (n + 1), E.momento m * h ^ m / (m ! : ℝ) * iteratedDeriv m f x
      = ∑ k ∈ E.S, E.a k * ∑ m ∈ Finset.range (n + 1),
          ((k : ℝ) * h) ^ m / (m ! : ℝ) * iteratedDeriv m f x := by
    simp only [momento, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [mul_pow]; ring
  rw [e, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ E.S, |E.a k * f (x + k * h) - E.a k * ∑ m ∈ Finset.range (n + 1),
          ((k : ℝ) * h) ^ m / (m ! : ℝ) * iteratedDeriv m f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ E.S, |E.a k| * (K * |(k : ℝ) * h| ^ (n + 1) / ((n + 1) ! : ℝ)) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (taylor_punto n f hf K x _ (fun y _ => hK y)) (abs_nonneg _)
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [abs_mul, mul_pow]; ring

/-- **A4.2 (Lax para esquemas positivos).** Si `E` es positivo y el error cumple
`eⁿ⁺¹_j = (E eⁿ)_j + δⁿ_j` con `|e⁰_j| ≤ ε₀` y `|δⁿ_j| ≤ ε`, entonces `|eⁿ_j| ≤ ε₀ + n·ε`. -/
theorem error_positivo (E : Esquema) (hE : E.Positivo) (e δ : ℕ → ℤ → ℝ) (ε₀ ε : ℝ)
    (he : ∀ n j, e (n + 1) j = E.pasoR (e n) j + δ n j)
    (h0 : ∀ j, |e 0 j| ≤ ε₀) (hδ : ∀ n j, |δ n j| ≤ ε) (n : ℕ) (j : ℤ) :
    |e n j| ≤ ε₀ + n * ε := by
  induction n generalizing j with
  | zero => simpa using h0 j
  | succ n ih =>
    rw [he]
    have h1 : |E.pasoR (e n) j| ≤ ε₀ + n * ε := pasoR_acotado E hE (e n) _ ih j
    calc |E.pasoR (e n) j + δ n j| ≤ |E.pasoR (e n) j| + |δ n j| := abs_add_le _ _
      _ ≤ ε₀ + n * ε + ε := add_le_add h1 (hδ n j)
      _ = ε₀ + ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

end Esquema

/-- **A4.3.** FTCS es consistente de orden 2 en espacio: si `f` es `C⁴` con `|f⁗| ≤ K` y `r ≥ 0`,
`|(E f)(x) − f(x) − r·h²·f''(x)| ≤ r·h⁴·K/12`. -/
theorem esq_ftcs_calor_consistencia (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (K : ℝ)
    (hK : ∀ y, |iteratedDeriv 4 f y| ≤ K) (x h : ℝ) :
    |∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * f (x + k * h)
        - (f x + r * h ^ 2 * iteratedDeriv 2 f x)| ≤ r * h ^ 4 * K / 12 := by
  have hT := (esq_ftcs_calor r).taylor 3 f (by exact_mod_cast hf) K hK x h
  obtain ⟨m0, m1, m2⟩ := esq_ftcs_calor_momentos r
  have m3 : (esq_ftcs_calor r).momento 3 = 0 := by
    simp [esq_ftcs_calor, Esquema.momento, Finset.sum_insert]
    ring
  have hsum : ∑ m ∈ Finset.range (3 + 1),
      (esq_ftcs_calor r).momento m * h ^ m / (Nat.factorial m : ℝ) * iteratedDeriv m f x
      = f x + r * h ^ 2 * iteratedDeriv 2 f x := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, m0, m1, m2, m3, iteratedDeriv_zero]
    push_cast [Nat.factorial]
    ring
  have hs : ∑ k ∈ (esq_ftcs_calor r).S, |(esq_ftcs_calor r).a k| * |(k : ℝ)| ^ (3 + 1) = 2 * r := by
    simp [esq_ftcs_calor, Finset.sum_insert, abs_of_nonneg hr]
    ring
  have hh : |h| ^ (3 + 1) = h ^ 4 := by
    rw [show (3 + 1 : ℕ) = 4 from rfl, ← abs_pow]
    exact abs_of_nonneg (by positivity)
  have hf24 : (Nat.factorial (3 + 1) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hsum, hs, hh, hf24] at hT
  linarith

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
  set r := α * Δt / Δx ^ 2 with hrdef
  have hr0 : 0 ≤ r := div_nonneg (mul_nonneg hα hΔt) (sq_nonneg _)
  have hE := esq_ftcs_calor_positivo r ⟨hr0, hr⟩
  have hrh : r * Δx ^ 2 = α * Δt := by
    rw [hrdef]; field_simp
  have lin : ∀ (A B : ℤ → ℝ) (i : ℤ), (esq_ftcs_calor r).pasoR (fun l => A l - B l) i
      = (esq_ftcs_calor r).pasoR A i - (esq_ftcs_calor r).pasoR B i := by
    intro A B i
    simp only [Esquema.pasoR, mul_sub, Finset.sum_sub_distrib]
  set U : ℕ → ℤ → ℝ := fun m i => u (m * Δt) (i * Δx) with hUdef
  have hδ : ∀ m i, |U (m + 1) i - (esq_ftcs_calor r).pasoR (U m) i|
      ≤ Δt * (Δt * Kt / 2 + α * Δx ^ 2 * Kx / 12) := by
    intro m i
    have hU1 : U (m + 1) i = u ((m : ℝ) * Δt + Δt) ((i : ℝ) * Δx) := by
      simp only [hUdef]; push_cast; ring_nf
    have hEU : (esq_ftcs_calor r).pasoR (U m) i
        = ∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * u ((m : ℝ) * Δt) ((i : ℝ) * Δx + k * Δx) := by
      simp only [Esquema.pasoR, hUdef]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      push_cast; ring_nf
    have htm : 0 ≤ (m : ℝ) * Δt := mul_nonneg (Nat.cast_nonneg m) hΔt
    have hT1 := taylor_punto 1 (fun s => u s ((i : ℝ) * Δx)) (ht _) Kt ((m : ℝ) * Δt) Δt
      (fun y hy => hKt y (by
        rw [Set.uIcc_of_le (by linarith)] at hy
        exact le_trans htm hy.1) _)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero, iteratedDeriv_one,
      pow_zero, pow_one, Nat.factorial, Nat.cast_one, div_one, one_mul, zero_add, Nat.succ_eq_add_one,
      Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hT1
    rw [hEDP] at hT1
    have hX := esq_ftcs_calor_consistencia r hr0 (u ((m : ℝ) * Δt)) (hx _) Kx (hKx _ htm) ((i : ℝ) * Δx) Δx
    rw [hU1, hEU]
    have key : u ((m : ℝ) * Δt + Δt) ((i : ℝ) * Δx)
          - ∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * u ((m : ℝ) * Δt) ((i : ℝ) * Δx + k * Δx)
        = (u ((m : ℝ) * Δt + Δt) ((i : ℝ) * Δx) - (u ((m : ℝ) * Δt) ((i : ℝ) * Δx)
            + Δt * (α * iteratedDeriv 2 (u ((m : ℝ) * Δt)) ((i : ℝ) * Δx))))
          - (∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * u ((m : ℝ) * Δt) ((i : ℝ) * Δx + k * Δx)
            - (u ((m : ℝ) * Δt) ((i : ℝ) * Δx) + r * Δx ^ 2 * iteratedDeriv 2 (u ((m : ℝ) * Δt)) ((i : ℝ) * Δx))) := by
      rw [hrh]; ring
    rw [key]
    have hΔt2 : |Δt| ^ 2 = Δt ^ 2 := sq_abs Δt
    have hx4 : r * Δx ^ 4 = α * Δt * Δx ^ 2 := by
      rw [show Δx ^ 4 = Δx ^ 2 * Δx ^ 2 by ring, ← mul_assoc, hrh]
    calc _ ≤ |u ((m : ℝ) * Δt + Δt) ((i : ℝ) * Δx) - (u ((m : ℝ) * Δt) ((i : ℝ) * Δx)
            + Δt * (α * iteratedDeriv 2 (u ((m : ℝ) * Δt)) ((i : ℝ) * Δx)))|
          + |∑ k ∈ (esq_ftcs_calor r).S, (esq_ftcs_calor r).a k * u ((m : ℝ) * Δt) ((i : ℝ) * Δx + k * Δx)
            - (u ((m : ℝ) * Δt) ((i : ℝ) * Δx) + r * Δx ^ 2 * iteratedDeriv 2 (u ((m : ℝ) * Δt)) ((i : ℝ) * Δx))| :=
          abs_sub _ _
      _ ≤ Kt * Δt ^ 2 / 2 + r * Δx ^ 4 * Kx / 12 := by
          gcongr
          · have := hT1; rw [hΔt2] at this; linarith
      _ = Δt * (Δt * Kt / 2 + α * Δx ^ 2 * Kx / 12) := by rw [hx4]; ring
  have he : ∀ m i, (fun m i => U m i - V m i) (m + 1) i
      = (esq_ftcs_calor r).pasoR ((fun m i => U m i - V m i) m) i
        + (fun m i => U (m + 1) i - (esq_ftcs_calor r).pasoR (U m) i) m i := by
    intro m i
    simp only []
    rw [hV, lin]
    ring
  have h0 : ∀ i, |(fun m i => U m i - V m i) 0 i| ≤ 0 := by
    intro i
    simp [hUdef, hV0]
  have := Esquema.error_positivo (esq_ftcs_calor r) hE (fun m i => U m i - V m i)
    (fun m i => U (m + 1) i - (esq_ftcs_calor r).pasoR (U m) i) 0 _ he h0 hδ n j
  simp only [hUdef] at this
  linarith

/-- **A4.5 (A4.4 no es vacía).** Para la solución `u(t, x) = e^{-αt}·sin x` y FTCS que parte de
`V⁰_j = sin(jΔx)` con `α·Δt/Δx² ≤ 1/2`: `|u(nΔt, jΔx) − Vⁿ_j| ≤ n·Δt·(Δt·α²/2 + α·Δx²/12)`. -/
theorem esq_ftcs_calor_converge_seno (α Δt Δx : ℝ) (hα : 0 ≤ α) (hΔt : 0 ≤ Δt) (hΔx : Δx ≠ 0)
    (hr : α * Δt / Δx ^ 2 ≤ 1 / 2) (V : ℕ → ℤ → ℝ)
    (hV : ∀ n j, V (n + 1) j = (esq_ftcs_calor (α * Δt / Δx ^ 2)).pasoR (V n) j)
    (hV0 : ∀ j, V 0 j = Real.sin (j * Δx)) (n : ℕ) (j : ℤ) :
    |Real.exp (-α * (n * Δt)) * Real.sin (j * Δx) - V n j|
      ≤ n * Δt * (Δt * α ^ 2 / 2 + α * Δx ^ 2 / 12) := by
  have hsin2 : iteratedDeriv 2 Real.sin = fun x => -Real.sin x := by
    have := Real.iteratedDeriv_even_sin 1
    simpa using this
  have hsin4 : iteratedDeriv 4 Real.sin = Real.sin := by
    have := Real.iteratedDeriv_even_sin 2
    simpa using this
  have hexp : ∀ m : ℕ, iteratedDeriv m (fun s => Real.exp (-α * s)) = fun s => (-α) ^ m * Real.exp (-α * s) :=
    fun m => iteratedDeriv_exp_const_mul m (-α)
  have hx : ∀ t, ContDiff ℝ 4 (fun x => Real.exp (-α * t) * Real.sin x) :=
    fun t => contDiff_const.mul Real.contDiff_sin
  have ht : ∀ x, ContDiff ℝ 2 (fun t => Real.exp (-α * t) * Real.sin x) :=
    fun x => (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul contDiff_const
  have hEDP : ∀ t x, deriv (fun s => Real.exp (-α * s) * Real.sin x) t
      = α * iteratedDeriv 2 (fun x => Real.exp (-α * t) * Real.sin x) x := by
    intro t x
    rw [← iteratedDeriv_one, iteratedDeriv_mul_const_field, hexp, iteratedDeriv_const_mul_field, hsin2]
    ring
  have hKt : ∀ t, 0 ≤ t → ∀ x, |iteratedDeriv 2 (fun s => Real.exp (-α * s) * Real.sin x) t| ≤ α ^ 2 := by
    intro t ht0 x
    rw [iteratedDeriv_mul_const_field, hexp]
    have he : Real.exp (-α * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 := Real.exp_pos (-α * t)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (-α) ^ 2), abs_of_pos he0]
    have hs := Real.abs_sin_le_one x
    calc (-α) ^ 2 * Real.exp (-α * t) * |Real.sin x| ≤ (-α) ^ 2 * 1 * 1 := by gcongr
      _ = α ^ 2 := by ring
  have hKx : ∀ t, 0 ≤ t → ∀ x, |iteratedDeriv 4 (fun x => Real.exp (-α * t) * Real.sin x) x| ≤ 1 := by
    intro t ht0 x
    rw [iteratedDeriv_const_mul_field, hsin4]
    have he : Real.exp (-α * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-α * t) * |Real.sin x| ≤ 1 * 1 := by gcongr; exact Real.abs_sin_le_one x
      _ = 1 := by ring
  have h := esq_ftcs_calor_converge (fun t x => Real.exp (-α * t) * Real.sin x) α Δt Δx (α ^ 2) 1
    hα hΔt hΔx hr hx ht hEDP hKt hKx V hV (fun j => by simp [hV0]) n j
  simpa using h


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
  have ht := Esquema.taylor E n f hf K hK x h
  have hsum : ∑ m ∈ Finset.range (n + 1), E.momento m * h ^ m / (m ! : ℝ) * iteratedDeriv m f x
      = f x + k * P.op f x := by
    have h1 : ∀ m ∈ Finset.range (n + 1), E.momento m * h ^ m / (m ! : ℝ) * iteratedDeriv m f x
        = (if m = 0 then 1 else 0) * iteratedDeriv m f x + k * (P.coef m * iteratedDeriv m f x) := by
      intro m hm
      rw [hc m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h0; simp at h0
    · congr 1
      unfold Molde.op
      symm
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        simp [Molde.coef, show ¬ m ≤ P.orden by omega]
  rw [hsum] at ht
  exact ht

open Nat in
/-- **A8.2 (puente de consistencia, segundo orden en el tiempo).** -/
theorem consistencia2 (E : Esquema) (P : Molde) (k h : ℝ) (n : ℕ) (hc : E.Consistente2 P k h n)
    (hn : P.orden ≤ n) (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1) f) (K : ℝ)
    (hK : ∀ y, |iteratedDeriv (n + 1) f y| ≤ K) (x : ℝ) :
    |∑ j ∈ E.S, E.a j * f (x + j * h) - (f x + k * P.op f x + k ^ 2 / 2 * P.op2 n f x)|
      ≤ (∑ j ∈ E.S, |E.a j| * |(j : ℝ)| ^ (n + 1)) * |h| ^ (n + 1) * K / ((n + 1) ! : ℝ) := by
  have ht := Esquema.taylor E n f hf K hK x h
  have hsum : ∑ m ∈ Finset.range (n + 1), E.momento m * h ^ m / (m ! : ℝ) * iteratedDeriv m f x
      = f x + k * P.op f x + k ^ 2 / 2 * P.op2 n f x := by
    have h1 : ∀ m ∈ Finset.range (n + 1), E.momento m * h ^ m / (m ! : ℝ) * iteratedDeriv m f x
        = (if m = 0 then 1 else 0) * iteratedDeriv m f x + k * (P.coef m * iteratedDeriv m f x)
          + k ^ 2 / 2 * (P.coef2 m * iteratedDeriv m f x) := by
      intro m hm
      rw [hc m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    congr 1
    congr 1
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h0; simp at h0
    · congr 1
      unfold Molde.op
      symm
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        simp [Molde.coef, show ¬ m ≤ P.orden by omega]
  rw [hsum] at ht
  exact ht

end Esquema

end PrometeoLean.Esquemas


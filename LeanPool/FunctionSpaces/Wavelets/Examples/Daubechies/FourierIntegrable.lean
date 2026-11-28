/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Fourier transform of integrable functions on the line

Mathlib's Fourier transform of `f : ℝ → ℂ` is `𝓕 f(ξ) = ∫ e^(-2πixξ) f(x) dx`, its inverse is
`𝓕⁻ f(x) = ∫ e^(2πixξ) f(ξ) dξ` (`Real.fourier_real_eq`, `Real.fourierInv_eq`). This file proves
the facts about the transform that the Daubechies scaling function `φ = 𝓕⁻ Φ` needs. The
analytic hypotheses are integrability and continuity conditions. Continuity, the uniform bound,
the value at `0`, conjugation and the multiplication formula are the cases `V = ℝ` of the
lemmas of `FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels`.

* **Continuity and the uniform bound.** For integrable `f`, `𝓕 f` and `𝓕⁻ f` are continuous
  (`Real.continuous_fourier_of_integrable`), and `‖𝓕 f(ξ)‖ ≤ ∫ ‖f‖`
  (Mathlib's `Real.norm_fourier_le_integral_norm`).
* **The value at `0`**: `𝓕 f(0) = ∫ f` for every `f` (`Real.fourier_apply_zero`).
* **Linearity**: `𝓕[c f] = c 𝓕 f` for every `f` (`Real.fourier_const_mul_apply`) and finite sums
  of integrable functions (`Real.fourier_sum_apply`), each with its `𝓕⁻` version.
* **Translation, modulation, dilation, conjugation**:
  `𝓕[f(· + a)](ξ) = e^(2πiaξ) 𝓕 f(ξ)` (`Real.fourier_comp_add_right_apply`),
  `𝓕[e^(2πib·) f](ξ) = 𝓕 f(ξ - b)` (`Real.fourier_exp_mul_apply`),
  `𝓕[f(a ·)](ξ) = a⁻¹ 𝓕 f(ξ / a)` for `a > 0` (`Real.fourier_comp_mul_left_apply`) and
  `conj (𝓕 f(ξ)) = 𝓕⁻[conj ∘ f](ξ)` (`Real.conj_fourier`), each with its `𝓕⁻` version.
* **The multiplication formula** `∫ 𝓕 f · g = ∫ f · 𝓕 g` for integrable `f, g`
  (`Real.integral_fourier_mul`), by Fubini (`Rd.integral_fourier_mul`).
* **Parseval's identity** `∫ f · conj g = ∫ 𝓕 f · conj (𝓕 g)` for integrable `f` and continuous
  integrable `g` with integrable `𝓕 g` (`Real.integral_mul_conj_eq_integral_fourier`): the
  sesquilinear multiplication formula for `f` and `𝓕 g`
  (`VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`) and the inversion theorem
  `𝓕⁻ (𝓕 g) = g` (`Continuous.fourierInv_fourier_eq`). For `f = g` it is Plancherel's identity
  `∫ ‖𝓕 f‖² = ∫ ‖f‖²` (`Real.integral_norm_sq_fourier`).
* **Schwartz test functions.** `∫ f · ψ = ∫ 𝓕 f · 𝓕⁻ ψ` for integrable `f` and a Schwartz
  function `ψ` (`Real.integral_mul_schwartz_eq`), and the **fundamental lemma**
  `Real.eqOn_zero_of_integral_mul_schwartz_eq_zero`: a continuous `f` with `∫ ψ f = 0` for every
  Schwartz function `ψ` with compact support in an open set `U` vanishes on `U`. Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` tests with real smooth compactly
  supported `g`, and `x ↦ (g x : ℂ)` is a Schwartz function (`HasCompactSupport.toSchwartzMap`),
  so `f = 0` almost everywhere on `U` (`Real.ae_eq_zero_of_integral_mul_schwartz_eq_zero`);
  continuity gives `f = 0` at every point of `U` (`MeasureTheory.Measure.eqOn_open_of_ae_eq`).
-/

@[expose] public section

open MeasureTheory Complex
open scoped FourierTransform SchwartzMap ComplexConjugate ContDiff

namespace Real

variable {f g : ℝ → ℂ}

/-! ### Continuity and the uniform bound -/

/-- The Fourier transform `𝓕 f(ξ) = ∫ e^(-2πixξ) f(x) dx` of an integrable function is
continuous (`Rd.continuous_fourier_of_integrable` on `ℝ`). -/
theorem continuous_fourier_of_integrable (hf : Integrable f) : Continuous (𝓕 f) :=
  Rd.continuous_fourier_of_integrable hf

/-- The inverse Fourier transform `𝓕⁻ f(x) = ∫ e^(2πixξ) f(ξ) dξ` of an integrable function is
continuous (`Rd.continuous_fourierInv_of_integrable` on `ℝ`). -/
theorem continuous_fourierInv_of_integrable (hf : Integrable f) : Continuous (𝓕⁻ f) :=
  Rd.continuous_fourierInv_of_integrable hf

/-- The uniform bound `‖𝓕⁻ f(x)‖ ≤ ∫ ‖f‖` for the inverse transform
(`Rd.norm_fourierInv_le_integral_norm` on `ℝ`). -/
theorem norm_fourierInv_le_integral_norm (f : ℝ → ℂ) (x : ℝ) : ‖𝓕⁻ f x‖ ≤ ∫ ξ, ‖f ξ‖ :=
  Rd.norm_fourierInv_le_integral_norm f x

/-! ### The Fourier transform at `0` -/

/-- **The Fourier transform at `0` is the integral**: `𝓕 f(0) = ∫ f(x) dx` for every
`f : ℝ → ℂ` (`Rd.fourier_apply_zero` on `ℝ`). -/
theorem fourier_apply_zero (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x, f x :=
  Rd.fourier_apply_zero f

/-! ### Linearity -/

/-- The Fourier transform commutes with multiplication by a constant, `𝓕[c f] = c 𝓕 f`, for
every `f` (Mathlib's `VectorFourier.fourierIntegral_const_smul`). -/
theorem fourier_const_mul_apply (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ :=
  congrFun (VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) f c) ξ

/-- The inverse Fourier transform commutes with multiplication by a constant. -/
theorem fourierInv_const_mul_apply (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ (fun ξ => c * f ξ) x = c * 𝓕⁻ f x := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, fourier_const_mul_apply]

/-- The Fourier transform of a finite sum of integrable functions is the sum of the
transforms. -/
theorem fourier_sum_apply {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℂ}
    (hF : ∀ i ∈ s, Integrable (F i)) (ξ : ℝ) :
    𝓕 (fun x => ∑ i ∈ s, F i x) ξ = ∑ i ∈ s, 𝓕 (F i) ξ := by
  simp only [fourier_eq, Finset.smul_sum]
  exact integral_finsetSum s fun i hi => (fourierIntegral_convergent_iff ξ).2 (hF i hi)

/-- The inverse Fourier transform of a finite sum of integrable functions is the sum of the
inverse transforms. -/
theorem fourierInv_sum_apply {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℂ}
    (hF : ∀ i ∈ s, Integrable (F i)) (x : ℝ) :
    𝓕⁻ (fun ξ => ∑ i ∈ s, F i ξ) x = ∑ i ∈ s, 𝓕⁻ (F i) x := by
  rw [fourierInv_eq_fourier_neg, fourier_sum_apply s hF]
  exact Finset.sum_congr rfl fun i _ => (fourierInv_eq_fourier_neg (F i) x).symm

/-! ### Translation, modulation, dilation -/

/-- **Translation becomes modulation**: `𝓕[f(· + a)](ξ) = e^(2πiaξ) 𝓕 f(ξ)`, by the substitution
`y = x + a` (Mathlib's `VectorFourier.fourierIntegral_comp_add_right`). -/
theorem fourier_comp_add_right_apply (f : ℝ → ℂ) (a ξ : ℝ) :
    𝓕 (fun x => f (x + a)) ξ = cexp (2 * π * a * ξ * I) * 𝓕 f ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℝ) f a) ξ
  refine h.trans ?_
  rw [Circle.smul_def, fourierChar_apply, innerₗ_apply_apply, inner_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **Translation becomes modulation**, subtraction form: `𝓕[f(· - a)](ξ) = e^(-2πiaξ) 𝓕 f(ξ)`. -/
theorem fourier_comp_sub_right_apply (f : ℝ → ℂ) (a ξ : ℝ) :
    𝓕 (fun x => f (x - a)) ξ = cexp (-(2 * π * a * ξ * I)) * 𝓕 f ξ := by
  simp_rw [sub_eq_add_neg]
  rw [fourier_comp_add_right_apply]
  congr 2
  push_cast
  ring

/-- Translation for the inverse transform: `𝓕⁻[f(· + a)](x) = e^(-2πiax) 𝓕⁻ f(x)`. -/
theorem fourierInv_comp_add_right_apply (f : ℝ → ℂ) (a x : ℝ) :
    𝓕⁻ (fun ξ => f (ξ + a)) x = cexp (-(2 * π * a * x * I)) * 𝓕⁻ f x := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, fourier_comp_add_right_apply]
  congr 2
  push_cast
  ring

/-- **Modulation becomes translation**: `𝓕[e^(2πib·) f](ξ) = 𝓕 f(ξ - b)`, since
`e^(-2πixξ) e^(2πibx) = e^(-2πix(ξ - b))`. -/
theorem fourier_exp_mul_apply (f : ℝ → ℂ) (b ξ : ℝ) :
    𝓕 (fun x : ℝ => cexp (2 * π * b * x * I) * f x) ξ = 𝓕 f (ξ - b) := by
  rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul]
  congr 1 with x
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Modulation for the inverse transform: `𝓕⁻[e^(2πib·) f](x) = 𝓕⁻ f(x + b)`. -/
theorem fourierInv_exp_mul_apply (f : ℝ → ℂ) (b x : ℝ) :
    𝓕⁻ (fun ξ : ℝ => cexp (2 * π * b * ξ * I) * f ξ) x = 𝓕⁻ f (x + b) := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, fourier_exp_mul_apply, neg_add,
    sub_eq_add_neg]

/-- **Dilation** by `a ≠ 0`: `𝓕[f(a ·)](ξ) = |a|⁻¹ 𝓕 f(ξ / a)`, by the substitution `y = a x`
(Mathlib's `MeasureTheory.Measure.integral_comp_mul_left`). -/
theorem fourier_comp_mul_left_apply_of_ne_zero (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (fun x => f (a * x)) ξ = ((|a| : ℝ) : ℂ)⁻¹ * 𝓕 f (ξ / a) := by
  have h : ∀ x : ℝ, 𝐞 (-(x * ξ)) • f (a * x) =
      (fun y => 𝐞 (-(y * (ξ / a))) • f y) (a * x) := fun x => by
    simp only
    congr 3
    field_simp
  rw [fourier_real_eq, fourier_real_eq]
  simp_rw [h]
  rw [Measure.integral_comp_mul_left (fun y => 𝐞 (-(y * (ξ / a))) • f y) a, Complex.real_smul,
    abs_inv, Complex.ofReal_inv]

/-- **Dilation** by `a > 0`: `𝓕[f(a ·)](ξ) = a⁻¹ 𝓕 f(ξ / a)`. -/
theorem fourier_comp_mul_left_apply (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x => f (a * x)) ξ = (a : ℂ)⁻¹ * 𝓕 f (ξ / a) := by
  rw [fourier_comp_mul_left_apply_of_ne_zero f ha.ne', abs_of_pos ha]

/-- Dilation for the inverse transform, `a > 0`: `𝓕⁻[f(a ·)](x) = a⁻¹ 𝓕⁻ f(x / a)`. -/
theorem fourierInv_comp_mul_left_apply (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕⁻ (fun ξ => f (a * ξ)) x = (a : ℂ)⁻¹ * 𝓕⁻ f (x / a) := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, fourier_comp_mul_left_apply f ha,
    neg_div]

/-- Dilation and translation together, `a > 0`:
`𝓕[f(a · - b)](ξ) = a⁻¹ e^(-2πibξ/a) 𝓕 f(ξ / a)`. This is the form met by the cascade
`η_{n+1}(x) = ∑_k c_k η_n(2x - k)`. -/
theorem fourier_comp_mul_sub_apply (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (b ξ : ℝ) :
    𝓕 (fun x => f (a * x - b)) ξ =
      (a : ℂ)⁻¹ * (cexp (-(2 * π * b * (ξ / a) * I)) * 𝓕 f (ξ / a)) := by
  rw [fourier_comp_mul_left_apply (fun y => f (y - b)) ha, fourier_comp_sub_right_apply]
  push_cast
  rfl

/-! ### Conjugation -/

/-- **Conjugation**: `conj (𝓕 f(ξ)) = 𝓕⁻[conj ∘ f](ξ)`, since `conj e^(-2πixξ) = e^(2πixξ)`
(`Rd.conj_fourier_apply` on `ℝ`). -/
theorem conj_fourier (f : ℝ → ℂ) (ξ : ℝ) : conj (𝓕 f ξ) = 𝓕⁻ (fun x => conj (f x)) ξ :=
  Rd.conj_fourier_apply f ξ

/-- Conjugation for the inverse transform: `conj (𝓕⁻ f(x)) = 𝓕[conj ∘ f](x)`
(`Rd.conj_fourierInv_apply` on `ℝ`). -/
theorem conj_fourierInv (f : ℝ → ℂ) (x : ℝ) : conj (𝓕⁻ f x) = 𝓕 (fun ξ => conj (f ξ)) x :=
  Rd.conj_fourierInv_apply f x

/-! ### The multiplication formula and Parseval's identity -/

/-- **The multiplication formula** `∫ 𝓕 f · g = ∫ f · 𝓕 g` for integrable `f, g`
(`Rd.integral_fourier_mul` on `ℝ`). -/
theorem integral_fourier_mul (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x :=
  Rd.integral_fourier_mul hf hg

/-- The multiplication formula for the inverse transform: `∫ 𝓕⁻ f · g = ∫ f · 𝓕⁻ g` for
integrable `f, g` (`Rd.integral_fourierInv_mul` on `ℝ`). -/
theorem integral_fourierInv_mul (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x :=
  Rd.integral_fourierInv_mul hf hg

/-- **Parseval's identity** `∫ f · conj g = ∫ 𝓕 f · conj (𝓕 g)` for integrable `f` and a
continuous integrable `g` with integrable transform. The sesquilinear multiplication formula
(Mathlib's `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`) applied to `f` and `𝓕 g`
gives `∫ 𝓕 g · conj (𝓕 f) = ∫ 𝓕⁻ (𝓕 g) · conj f`, and `𝓕⁻ (𝓕 g) = g` by the inversion theorem
(Mathlib's `Continuous.fourierInv_fourier_eq`, which needs the hypotheses on `g`). -/
theorem integral_mul_conj_eq_integral_fourier (hf : Integrable f) (hg : Continuous g)
    (hgi : Integrable g) (hFg : Integrable (𝓕 g)) :
    ∫ x, f x * conj (g x) = ∫ ξ, 𝓕 f ξ * conj (𝓕 g ξ) := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ (E := ℂ))
    (L := innerₗ ℝ) continuous_fourierChar continuous_inner hf hFg
  have h' : ∫ ξ, 𝓕 g ξ * conj (𝓕 f ξ) = ∫ x, 𝓕⁻ (𝓕 g) x * conj (f x) := by
    simpa [RCLike.inner_apply] using! h
  rw [hg.fourierInv_fourier_eq hgi hFg] at h'
  have h'' := congrArg conj h'
  rw [← integral_conj, ← integral_conj] at h''
  simpa [mul_comm] using h''.symm

/-- **Plancherel's identity** `∫ ‖𝓕 f‖² = ∫ ‖f‖²` for a continuous integrable `f` with integrable
transform: Parseval's identity for `g = f`, with `z · conj z = ‖z‖²`. -/
theorem integral_norm_sq_fourier (hf : Continuous f) (hfi : Integrable f)
    (hFf : Integrable (𝓕 f)) : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := integral_mul_conj_eq_integral_fourier hfi hf hfi hFf
  have e : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h.symm

/-- **Testing against a Schwartz function** `ψ`: `∫ f · ψ = ∫ 𝓕 f · 𝓕⁻ ψ` for integrable `f`,
the multiplication formula for `f` and `𝓕⁻ ψ` together with `𝓕 (𝓕⁻ ψ) = ψ` (Fourier inversion on
the Schwartz space). Here `𝓕⁻ ψ` is the inverse transform of `ψ` as a Schwartz function. -/
theorem integral_mul_schwartz_eq (hf : Integrable f) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ x, f x * ψ x = ∫ ξ, 𝓕 f ξ * 𝓕⁻ ψ ξ := by
  rw [integral_fourier_mul hf (𝓕⁻ ψ).integrable]
  congr 1 with x
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]

/-! ### The fundamental lemma of the calculus of variations -/

/-- **Fundamental lemma, almost everywhere form**: if `f` is locally integrable on an open set `U`
and `∫ ψ f = 0` for every Schwartz function `ψ` with compact support in `U`, then `f = 0` almost
everywhere on `U`. Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` tests with
real smooth compactly supported `g`; the function `x ↦ (g x : ℂ)` is such a Schwartz function
(`HasCompactSupport.toSchwartzMap`). -/
theorem ae_eq_zero_of_integral_mul_schwartz_eq_zero {U : Set ℝ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U)
    (h : ∀ ψ : 𝓢(ℝ, ℂ), HasCompactSupport ψ → tsupport ψ ⊆ U → ∫ x, ψ x * f x = 0) :
    ∀ᵐ x, x ∈ U → f x = 0 := by
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf fun g g_smooth g_cpt g_supp => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have hg₃ : tsupport (Complex.ofRealCLM ∘ g) ⊆ U :=
    (tsupport_comp_subset (map_zero Complex.ofRealCLM) g).trans g_supp
  simpa [Complex.real_smul] using h (hg₁.toSchwartzMap hg₂) hg₁ hg₃

/-- **Fundamental lemma**: a continuous `f` with `∫ ψ f = 0` for every Schwartz function `ψ`
with compact support in an open set `U` vanishes at every point of `U`. Almost everywhere this
is `Real.ae_eq_zero_of_integral_mul_schwartz_eq_zero`; two continuous functions that agree almost
everywhere on an open set agree on it (Mathlib's `MeasureTheory.Measure.eqOn_open_of_ae_eq`,
nonempty open sets have positive Lebesgue measure). -/
theorem eqOn_zero_of_integral_mul_schwartz_eq_zero {U : Set ℝ} (hf : Continuous f)
    (hU : IsOpen U)
    (h : ∀ ψ : 𝓢(ℝ, ℂ), HasCompactSupport ψ → tsupport ψ ⊆ U → ∫ x, ψ x * f x = 0) :
    ∀ x ∈ U, f x = 0 := by
  have hae := ae_eq_zero_of_integral_mul_schwartz_eq_zero hU
    (hf.locallyIntegrable.locallyIntegrableOn U) h
  have hres : f =ᵐ[volume.restrict U] 0 := (ae_restrict_iff' hU.measurableSet).2 hae
  exact fun x hx => Measure.eqOn_open_of_ae_eq hres hU hf.continuousOn continuousOn_const hx

end Real

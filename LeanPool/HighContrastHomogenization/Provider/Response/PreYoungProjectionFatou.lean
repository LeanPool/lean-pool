/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedWeakQuantity

/-!
# High-contrast homogenization: Provider.Response.PreYoungProjectionFatou

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Passing uniform projected bounds to a limiting observable

Fatou's lemma transfers a common bound for measurable approximating
observables to their almost-everywhere limit.  An integrable real limit then
has an expectation bounded by the same extended-nonnegative constant.
-/

namespace HCPolySupport.HighContrast.Response

open _root_.Filter MeasureTheory

open scoped ENNReal

noncomputable section

/-! ## Finite normalized averages -/

/-- Integration commutes with a finite normalized average of integrable
observables. -/
theorem integral_avsum_eq_avsum_integral
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (Z : Finset ι) (F : ι → α → ℝ)
    (hF : ∀ z ∈ Z, Integrable (F z) μ) :
    (∫ a, avsum Z (fun z ↦ F z a) ∂μ) =
      avsum Z (fun z ↦ ∫ a, F z a ∂μ) := by
  unfold avsum
  rw [integral_const_mul, integral_finsetSum Z hF]

/-- A finite normalized average preserves pointwise convergence. -/
theorem tendsto_avsum {ι : Type*} (Z : Finset ι)
    (F : ℕ → ι → ℝ) (f : ι → ℝ)
    (hF : ∀ z ∈ Z, Tendsto (fun n ↦ F n z) atTop (nhds (f z))) :
    Tendsto (fun n ↦ avsum Z (fun z ↦ F n z)) atTop
      (nhds (avsum Z f)) := by
  unfold avsum
  exact tendsto_const_nhds.mul (tendsto_finsetSum Z hF)

/-- A finite normalized average of almost-everywhere measurable observables
is almost-everywhere measurable. -/
theorem aemeasurable_avsum
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (Z : Finset ι) (F : ι → α → ℝ)
    (hF : ∀ z ∈ Z, AEMeasurable (F z) μ) :
    AEMeasurable (fun a ↦ avsum Z (fun z ↦ F z a)) μ := by
  unfold avsum
  exact aemeasurable_const.mul (Finset.aemeasurable_fun_sum Z hF)

/-! ## Fatou passage -/

/-- A uniform bound for the absolute lower integrals of a sequence passes to
an almost-everywhere pointwise limit. -/
theorem lintegral_ofReal_abs_le_of_tendsto_of_uniform_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {B : ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F n a) atTop (nhds (f a)))
    (hbound : ∀ n, ∫⁻ a, ENNReal.ofReal |F n a| ∂μ ≤ B) :
    ∫⁻ a, ENNReal.ofReal |f a| ∂μ ≤ B := by
  have hmeas : ∀ n, AEMeasurable (fun a ↦ ENNReal.ofReal |F n a|) μ :=
    fun n ↦ (continuous_abs.measurable.comp_aemeasurable (hF n)).ennreal_ofReal
  have hpoint : ∀ᵐ a ∂μ,
      liminf (fun n ↦ ENNReal.ofReal |F n a|) atTop =
        ENNReal.ofReal |f a| := by
    filter_upwards [hlim] with a ha
    exact (ENNReal.tendsto_ofReal ha.abs).liminf_eq
  calc
    ∫⁻ a, ENNReal.ofReal |f a| ∂μ =
        ∫⁻ a, liminf (fun n ↦ ENNReal.ofReal |F n a|) atTop ∂μ :=
      lintegral_congr_ae (hpoint.mono fun _ ha ↦ ha.symm)
    _ ≤ liminf (fun n ↦ ∫⁻ a, ENNReal.ofReal |F n a| ∂μ) atTop :=
      lintegral_liminf_le' hmeas
    _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- An integrable limiting observable inherits the common bound for the
expectations of a pointwise convergent sequence. -/
theorem ofReal_abs_integral_le_of_tendsto_of_uniform_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {B : ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hf : Integrable f μ)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F n a) atTop (nhds (f a)))
    (hbound : ∀ n, ∫⁻ a, ENNReal.ofReal |F n a| ∂μ ≤ B) :
    ENNReal.ofReal |∫ a, f a ∂μ| ≤ B := by
  have hlimit := lintegral_ofReal_abs_le_of_tendsto_of_uniform_bound
    hF hlim hbound
  calc
    ENNReal.ofReal |∫ a, f a ∂μ| =
        ENNReal.ofReal ‖∫ a, f a ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ENNReal.ofReal (∫ a, ‖f a‖ ∂μ) :=
      ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm f)
    _ = ∫⁻ a, ‖f a‖ₑ ∂μ :=
      ofReal_integral_norm_eq_lintegral_enorm hf
    _ = ∫⁻ a, ENNReal.ofReal |f a| ∂μ := by
      apply lintegral_congr
      intro a
      exact Real.enorm_eq_ofReal_abs (f a)
    _ ≤ B := hlimit

end

end HCPolySupport.HighContrast.Response

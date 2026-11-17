/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUFamily
public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalTimeDerivative

/-! # The infinite-time endpoints of bounded Gaussian interpolation -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- A measurable function valued in a closed interval has its probability integral in that interval.
-/
theorem integral_mem_Icc_of_range {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : AEStronglyMeasurable F μ) {a b : ℝ}
    (hbound : ∀ z, F z ∈ Icc a b) : (∫ z, F z ∂μ) ∈ Icc a b := by
  have hint := Integrable.of_bound hF (max |a| |b|) (ae_of_all μ fun z => by
    simpa only [Real.norm_eq_abs] using abs_le_max_abs_abs (hbound z).1 (hbound z).2)
  have hlo := integral_mono (integrable_const a) hint (fun z => (hbound z).1)
  have hhi := integral_mono hint (integrable_const b) (fun z => (hbound z).2)
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- The Ornstein–Uhlenbeck average of a bounded continuous function is continuous in time. -/
theorem continuous_ouAverage_time {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) {B : ℝ} (hbound : ∀ z, |F z| ≤ B) (x : Fin n → ℝ) :
    Continuous (ouAverage F x) := by
  apply continuous_of_dominated (μ := standardGaussianMeasure n) (bound := fun _ => B)
  · intro t
    exact (hF.comp (by fun_prop)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound _
  · exact integrable_const B
  · exact ae_of_all _ fun z => hF.comp (by fun_prop)

/-- The Ornstein–Uhlenbeck kernel converges to its Gaussian argument as time tends to infinity. -/
theorem tendsto_ou_kernel_atTop {n : ℕ} (x z : Fin n → ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z)
      atTop (𝓝 z) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have he₂ : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) := by
    simpa only [exp_neg_two_eq_sq, zero_pow (by decide : 2 ≠ 0)] using he.pow 2
  have hb : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (𝓝 1) := by
    simpa only [sub_zero, Real.sqrt_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub he₂).sqrt
  simpa only [zero_smul, one_smul, zero_add] using (he.smul_const x).add (hb.smul_const z)

/-- The Ornstein–Uhlenbeck average of a bounded continuous function tends to its Gaussian mean. -/
theorem tendsto_ouAverage_atTop {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) {B : ℝ} (hbound : ∀ z, |F z| ≤ B) (x : Fin n → ℝ) :
    Tendsto (ouAverage F x) atTop (𝓝 (∫ z, F z ∂standardGaussianMeasure n)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun t => (hF.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using hbound _
  · exact integrable_const B
  · exact ae_of_all _ fun z => hF.continuousAt.tendsto.comp (tendsto_ou_kernel_atTop x z)

/-- A bounded continuous Ornstein–Uhlenbeck family tends coordinatewise to its Gaussian means. -/
theorem tendsto_ouFamily_atTop {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, Continuous (f i)) {B : ℝ} (hbound : ∀ i z, |f i z| ≤ B) (x : Fin n → ℝ) :
    Tendsto (fun t => ouFamily f (t, x)) atTop
      (𝓝 (fun i => ∫ z, f i z ∂standardGaussianMeasure n)) :=
  tendsto_pi_nhds.mpr fun i => tendsto_ouAverage_atTop (hf i) (hbound i) x

/-- The Gaussian mean of a smooth interval valued function remains in that interval. -/
theorem integral_mem_Icc_of_bounded {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) {a b : ℝ}
    (hbound : ∀ z, F z ∈ Icc a b) : (∫ z, F z ∂standardGaussianMeasure n) ∈ Icc a b := by
  exact isClosed_Icc.mem_of_tendsto
    (tendsto_ouAverage_atTop hF.1.continuous (fun z => abs_le_max_abs_abs (hbound z).1 (hbound z).2)
      0)
    (Eventually.of_forall (fun t => ouAverage_mem_Icc hF hbound 0 t))

/-- The interpolation scale tends to its limiting scale at infinite time. -/
theorem tendsto_interpolationScale_atTop (R ε : ℝ) :
    Tendsto (interpolationScale R ε) atTop (𝓝 R) := by
  have he₂ : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) := by
    simpa only [exp_neg_two_eq_sq, zero_pow (by decide : 2 ≠ 0)] using
      Real.tendsto_exp_neg_atTop_nhds_zero.pow 2
  have he : Tendsto (fun t : ℝ => Real.exp (-2 * t - ε)) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg, Real.exp_add, zero_mul] using he₂.mul_const (Real.exp (-ε))
  have hb : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t - ε))) atTop (𝓝 1) := by
    simpa only [sub_zero, Real.sqrt_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub he).sqrt
  change Tendsto (fun t => R * Real.sqrt (1 - Real.exp (-2 * t - ε))) atTop (𝓝 R)
  simpa only [mul_one] using hb.const_mul R


end EhrhardGaussian.Ehrhard

end

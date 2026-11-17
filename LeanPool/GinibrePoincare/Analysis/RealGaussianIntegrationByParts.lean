/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RealGaussianIntegrationByParts.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GaussianDensity

/-! # One-dimensional Gaussian integration by parts -/


@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

/-- The real density of one coordinate in the normalization of the Ginibre
Gaussian reference measure. -/
def realCoordinateDensity (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (Real.pi / n))⁻¹ * Real.exp (-(n : ℝ) * x ^ 2)

theorem continuous_realCoordinateDensity (n : ℕ) :
    Continuous (realCoordinateDensity n) := by
  unfold realCoordinateDensity
  fun_prop

theorem hasDerivAt_realCoordinateDensity (n : ℕ) (x : ℝ) :
    HasDerivAt (realCoordinateDensity n)
      (-2 * (n : ℝ) * x * realCoordinateDensity n x) x := by
  have he : HasDerivAt (fun y : ℝ => -(n : ℝ) * y ^ 2)
      (-2 * (n : ℝ) * x) x := by
    have hraw := (hasDerivAt_const x (-(n : ℝ))).mul
      ((hasDerivAt_id x).pow 2)
    change HasDerivAt (fun y : ℝ => -(n : ℝ) * y ^ 2)
      (0 * x ^ 2 + -(n : ℝ) * ((2 : ℕ) * x ^ (2 - 1) * 1)) x at hraw
    apply hraw.congr_deriv
    norm_num
    ring
  have hexp := (Real.hasDerivAt_exp (-(n : ℝ) * x ^ 2)).comp x he
  have h := hexp.const_mul (Real.sqrt (Real.pi / n))⁻¹
  have hfun : realCoordinateDensity n =
      fun y => (Real.sqrt (Real.pi / n))⁻¹ *
        Real.exp (-(n : ℝ) * y ^ 2) := by rfl
  rw [hfun]
  apply h.congr_deriv
  ring

theorem integrable_mul_realCoordinateDensity {n : ℕ} {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x ↦ f x * realCoordinateDensity n x) := by
  apply (hf.mul (Complex.continuous_ofReal.comp
    (continuous_realCoordinateDensity n))).integrable_of_hasCompactSupport
  exact hfc.mul_right

theorem integrable_deriv_mul_realCoordinateDensity {n : ℕ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (fun x ↦ deriv f x * realCoordinateDensity n x) := by
  apply ((hf.continuous_deriv le_rfl).mul (Complex.continuous_ofReal.comp
    (continuous_realCoordinateDensity n))).integrable_of_hasCompactSupport
  exact hfc.deriv.mul_right

theorem integrable_mul_realCoordinateDensity_deriv {n : ℕ} {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x ↦ f x *
      ((-2 * (n : ℝ) * x * realCoordinateDensity n x : ℝ) : ℂ)) := by
  have hc : Continuous (fun x : ℝ ↦
      ((-2 * (n : ℝ) * x * realCoordinateDensity n x : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).mul (continuous_realCoordinateDensity n))
  apply (hf.mul hc).integrable_of_hasCompactSupport
  exact hfc.mul_right

theorem integrable_deriv_product_realCoordinateDensity {n : ℕ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    Integrable (fun x ↦
      deriv f x * realCoordinateDensity n x +
        f x * ((-2 * (n : ℝ) * x * realCoordinateDensity n x : ℝ) : ℂ)) :=
  (integrable_deriv_mul_realCoordinateDensity hf hfc).add
    (integrable_mul_realCoordinateDensity_deriv hf.continuous hfc)

/-- Integration by parts without compact support.  This formulation is
tailored to polynomial test functions: Gaussian moment estimates discharge
the three explicit integrability hypotheses. -/
theorem realGaussianIntegrationByPartsLebesgue_of_integrable {n : ℕ}
    {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (hfd : Integrable (fun x ↦ deriv f x * realCoordinateDensity n x))
    (hfrho' : Integrable (fun x ↦ f x *
      ((-2 * (n : ℝ) * x * realCoordinateDensity n x : ℝ) : ℂ)))
    (hfrho : Integrable (fun x ↦ f x * realCoordinateDensity n x)) :
    (∫ x, deriv f x * realCoordinateDensity n x) =
      ∫ x, (((2 * n : ℝ) * x : ℝ) : ℂ) * f x *
        realCoordinateDensity n x := by
  let ρ : ℝ → ℂ := fun x ↦ realCoordinateDensity n x
  let ρ' : ℝ → ℂ := fun x ↦
    ((-2 * (n : ℝ) * x * realCoordinateDensity n x : ℝ) : ℂ)
  have hfder (x : ℝ) : HasDerivAt f (deriv f x) x := (hf x).hasDerivAt
  have hρ (x : ℝ) : HasDerivAt ρ (ρ' x) x := by
    exact (hasDerivAt_realCoordinateDensity n x).ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := deriv f) (v := ρ) (v' := ρ')
    (fun x _ ↦ hfder x) (fun x _ ↦ hρ x) hfrho' hfd hfrho
  change (∫ x, deriv f x * ρ x) = _
  calc
    (∫ x, deriv f x * ρ x) = -(∫ x, f x * ρ' x) := by
      rw [hibp]
      simp
    _ = ∫ x, (((2 * n : ℝ) * x : ℝ) : ℂ) * f x *
        realCoordinateDensity n x := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [ρ']
      push_cast
      ring

theorem realGaussianIntegrationByPartsLebesgue {n : ℕ}
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫ x, deriv f x * realCoordinateDensity n x) =
      ∫ x, (((2 * n : ℝ) * x : ℝ) : ℂ) * f x * realCoordinateDensity n x := by
  exact realGaussianIntegrationByPartsLebesgue_of_integrable
    (hf.differentiable (by norm_num))
    (integrable_deriv_mul_realCoordinateDensity hf hfc)
    (integrable_mul_realCoordinateDensity_deriv hf.continuous hfc)
    (integrable_mul_realCoordinateDensity hf.continuous hfc)

theorem integral_realCoordinateGaussian_eq_density {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℂ) :
    (∫ x, f x ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
      ∫ x, f x * realCoordinateDensity n x := by
  rw [realCoordinateGaussianMeasure_eq_withDensity hn,
    integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with x
    rw [realCoordinateGaussianPDF_formula hn]
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp [realCoordinateDensity, mul_comm]
  · exact ProbabilityTheory.measurable_gaussianPDF 0 (realCoordinateVariance n)
  · exact Filter.Eventually.of_forall fun x ↦
      ProbabilityTheory.gaussianPDF_lt_top

theorem integrable_mul_realCoordinateDensity_of_integrable
    {n : ℕ} (hn : 0 < n) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f)
    (hf : Integrable f (realCoordinateGaussianProbability n : Measure ℝ)) :
    Integrable (fun x ↦ f x * realCoordinateDensity n x) := by
  rw [realCoordinateGaussianMeasure_eq_withDensity hn] at hf
  have h := (integrable_withDensity_iff
    (ProbabilityTheory.measurable_gaussianPDF 0 (realCoordinateVariance n))
    (Filter.Eventually.of_forall fun x ↦
      ProbabilityTheory.gaussianPDF_lt_top)).mp hf.norm
  apply (integrable_norm_iff
    (hfm.mul ((Complex.continuous_ofReal.comp
      (continuous_realCoordinateDensity n)).aestronglyMeasurable))).mp
  apply h.congr
  filter_upwards with x
  rw [realCoordinateGaussianPDF_formula hn,
    ENNReal.toReal_ofReal (by positivity)]
  change ‖f x‖ * realCoordinateDensity n x =
    ‖f x * (realCoordinateDensity n x : ℂ)‖
  have hd : 0 ≤ realCoordinateDensity n x := by
    unfold realCoordinateDensity
    positivity
  rw [norm_mul]
  simp [abs_of_nonneg hd]

/-- Gaussian-measure form of the non-compactly-supported integration by
parts theorem. -/
theorem realGaussianIntegrationByParts_of_integrable {n : ℕ} (hn : 0 < n)
    {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (hfd : Integrable (fun x ↦ deriv f x * realCoordinateDensity n x))
    (hfrho' : Integrable (fun x ↦ f x *
      ((-2 * (n : ℝ) * x * realCoordinateDensity n x : ℝ) : ℂ)))
    (hfrho : Integrable (fun x ↦ f x * realCoordinateDensity n x)) :
    (∫ x, deriv f x ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
      (2 * n : ℝ) *
        ∫ x, (x : ℂ) * f x
          ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  rw [integral_realCoordinateGaussian_eq_density hn,
    integral_realCoordinateGaussian_eq_density hn,
    realGaussianIntegrationByPartsLebesgue_of_integrable hf hfd hfrho' hfrho,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  ring

/-- Gaussian integration by parts in the exact variance `1/(2n)`
normalization used for each real coordinate. -/
theorem realGaussianIntegrationByParts {n : ℕ} (hn : 0 < n)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫ x, deriv f x ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
      (2 * n : ℝ) *
        ∫ x, (x : ℂ) * f x
          ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  exact realGaussianIntegrationByParts_of_integrable hn
    (hf.differentiable (by norm_num))
    (integrable_deriv_mul_realCoordinateDensity hf hfc)
    (integrable_mul_realCoordinateDensity_deriv hf.continuous hfc)
    (integrable_mul_realCoordinateDensity hf.continuous hfc)

theorem realGaussianIntegrationByParts_of_gaussian_integrable
    {n : ℕ} (hn : 0 < n) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f)
    (hfi : Integrable f (realCoordinateGaussianProbability n : Measure ℝ))
    (hfdi : Integrable (deriv f)
      (realCoordinateGaussianProbability n : Measure ℝ))
    (hxfi : Integrable (fun x : ℝ ↦ (x : ℂ) * f x)
      (realCoordinateGaussianProbability n : Measure ℝ)) :
    (∫ x, deriv f x ∂(realCoordinateGaussianProbability n : Measure ℝ)) =
      (2 * n : ℝ) * ∫ x, (x : ℂ) * f x
        ∂(realCoordinateGaussianProbability n : Measure ℝ) := by
  apply realGaussianIntegrationByParts_of_integrable hn
    (hf.differentiable (by norm_num))
  · exact integrable_mul_realCoordinateDensity_of_integrable hn
      (hf.continuous_deriv le_rfl).aestronglyMeasurable hfdi
  · have h := (integrable_mul_realCoordinateDensity_of_integrable hn
        ((Complex.continuous_ofReal.mul hf.continuous).aestronglyMeasurable) hxfi).const_mul
        ((-2 * (n : ℝ) : ℝ) : ℂ)
    exact h.congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [Pi.mul_apply]
      push_cast
      ring)
  · exact integrable_mul_realCoordinateDensity_of_integrable hn
      hf.continuous.aestronglyMeasurable hfi

end

end GinibrePoincare

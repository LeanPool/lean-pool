/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAlgebraCenterCovariance.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Correspondence algebra center covariance

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `correspondence_coordinateSum_cross_covariance`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem correspondence_standardGaussian_cross_moment :
    (∫ z : ℂ, z.re*z.im ∂standardComplexGaussianMeasure) = 0 := by
  have hi : Integrable (fun z : ℂ => z^2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using
      integrable_mixedComplexMonomial 1 2 0
  have hm : (∫ z : ℂ, z^2 ∂standardComplexGaussianMeasure) = 0 := by
    have h := complexGaussianMixedMoment_formula (by norm_num : (0 : ℕ) < 1) 2 0
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using h
  have he (z : ℂ) : z.re*z.im = (1/2 : ℝ)*(z^2).im := by
    simp [pow_two, Complex.mul_im]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have him : (∫ z : ℂ, (z^2).im ∂standardComplexGaussianMeasure) = 0 := by
    calc
      _ = (∫ z : ℂ, z^2 ∂standardComplexGaussianMeasure).im := integral_im hi
      _ = 0 := by rw [hm]; rfl
  rw [him]
  simp

/-- Literal zero cross-covariance of the two centered components in (2.34). -/
theorem correspondence_coordinateSum_cross_covariance (n : ℕ) (hn : 0 < n) :
    (∫ z : Configuration n, (coordinateSum z).re*(coordinateSum z).im ∂ginibreMeasure n) = 0 := by
  have hm := integral_map (μ := ginibreMeasure n)
    (measurable_coordinateSum n).aemeasurable
    (Complex.continuous_re.mul Complex.continuous_im).aestronglyMeasurable
  change (∫ z : Configuration n, (Complex.re * Complex.im) (coordinateSum z) ∂ginibreMeasure n) = 0
  rw [← hm, coordinateSum_ginibre_gaussian n hn]
  exact correspondence_standardGaussian_cross_moment

end
end GinibrePoincare

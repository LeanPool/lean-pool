/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryEntireAnalytic.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryHolomorphicFormalSeries
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSpaceClosure

/-!
# Correspondence auxiliary entire analytic

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `gaussianEntireRepresentative_real_analytic`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Every actual Gaussian square-integrable entire representative is jointly
complex analytic, proved by its genuine infinite-radius Hermite Taylor series. -/
theorem gaussianEntireRepresentative_complex_analytic {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) (z : Configuration n) :
    AnalyticAt ℂ f z := by
  let c := fun p : Fin n → ℕ => gaussianHermiteCoefficient hn u (p, 0)
  have hcoef : ∀ p, ‖c p‖ ≤ ‖u‖ := fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0)
  have hseries := gaussianZeroMode_holomorphic_series_ae hn u
  rw [gaussianEntireRepresentative_zeroMode_eq hn u f hf] at hseries
  have heq : (fun w => ∑' p, c p * ComplexHermite.multivariateNormalized n hn p 0 w) = f :=
    continuous_eq_of_ae_eq_complexGaussian hn
      (differentiable_holomorphicHermite_series n hn c hcoef).continuous hf.1.continuous
      (hseries.trans hf.2.symm)
  rw [← heq]
  have hr := holomorphicHermiteFormalSeries_radius n c hcoef
  have ha := (holomorphicHermiteFormalSeries n c).analyticOnNhd z (by simp [hr])
  have he := funext (holomorphicHermiteFormalSeries_sum n hn c hcoef)
  rw [he] at ha
  exact ha

/-- Restriction of the actual complex Taylor series to real coordinates. -/
theorem gaussianEntireRepresentative_real_analytic {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) (z : Configuration n) :
    AnalyticAt ℝ f z :=
  (gaussianEntireRepresentative_complex_analytic hn u f hf z).restrictScalars

end
end GinibrePoincare

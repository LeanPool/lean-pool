/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitConvolution
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.WeightedCircleKernel

/-!
# Scalar supermeans from a measurable nonnegative circle kernel

The pointwise angular hypothesis is supplied independently of this module.
Tonelli, translation invariance, and an almost-everywhere real representative
turn it into a supermean inequality for an actual smooth scalar pairing.
A uniform family of these inequalities makes the tested Levi form nonpositive.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Laplacian
open scoped ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

/-- Pointwise angular bounds on a uniform interval of positive radii force
the actual integral against the classical Levi form of the test function to
be nonpositive. The kernel may be singular and agrees with the real density
only almost everywhere. -/
theorem integral_mul_leviForm_nonpos_of_pointwise_circle_lintegral
    {D : E → ℝ≥0∞} {f φ : E → ℝ}
    (hDm : Measurable D) (hDf : D =ᵐ[μ] fun x => ENNReal.ofReal (f x))
    (hf : LocallyIntegrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ) (hφn : ∀ x, 0 ≤ φ x)
    (v : E) {R : ℝ} (hR : 0 < R)
    (hpoint : ∀ r ∈ Ioo 0 R, ∀ x ∈ Function.support φ,
      (∫⁻ t in Ioc 0 (2 * Real.pi), D (x + circleMap 0 r t • v)) ≤
        ENNReal.ofReal (2 * Real.pi) * D x) :
    (∫ x, f x * leviForm φ x v ∂μ) ≤ 0 :=
  integral_mul_leviForm_nonpos_of_circleAverage_le hf hφs hφ v hR fun r hr =>
    circleAverage_pairing_le_of_pointwise_circle_lintegral hDm hDf hf hfn hφs hφ hφn
      v r (hpoint r hr)

end SGPT.Foundations.Analysis

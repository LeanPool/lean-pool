/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import LeanPool.EhrhardGaussian.Definitions.IsEhrhardType
public import LeanPool.EhrhardGaussian.Provider.EhrhardTypeCharacterization

/-! # Representation and moment bounds for Ehrhard-type laws -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace EhrhardGaussian

/-- **Ehrhard-type laws** (KPZ Lemma 3.6 `ng:quantile-closure`, §3.3): every finite convex function
of a
finite-dimensional Gaussian vector is of Ehrhard type; a law is of Ehrhard type iff it is the law of
`h(G)` with `G ∼ N(0,1)` and `h` nondecreasing and convex; the class is closed under weak
convergence; and (LX26 Theorem 2.9, used at KPZ §3.4 and `R:Ehrhard`) the approximate
log-normal bounds of KPZ Lemma 3.2 hold for every Ehrhard-type law normalised by `E e^X = 1`. -/
theorem ehrhardType_characterization :
    (∀ {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
      (F : EuclideanSpace ℝ (Fin n) → ℝ), ConvexOn ℝ Set.univ F → IsEhrhardType (μ.map F)) ∧
    (∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      (IsEhrhardType ν ↔ ∃ h : ℝ → ℝ, Monotone h ∧ ConvexOn ℝ Set.univ h ∧
        ν = (gaussianReal 0 1).map h)) ∧
    (∀ (ν : ℕ → ProbabilityMeasure ℝ) (ν' : ProbabilityMeasure ℝ), Tendsto ν atTop (nhds ν') →
      (∀ k, IsEhrhardType (ν k : Measure ℝ)) → IsEhrhardType (ν' : Measure ℝ)) ∧
    (∀ ν : Measure ℝ, IsEhrhardType ν → Integrable (fun x => Real.exp x) ν →
      ∫ x, Real.exp x ∂ν = 1 →
      Integrable (fun x => x ^ 2) ν ∧ Var[id; ν] ≤ -2 * ∫ x, x ∂ν ∧
      (∀ p : ℝ, 0 ≤ p → Real.log (∫ x, Real.exp (-p * x) ∂ν) ≤ -p * (∫ x, x ∂ν) + p ^ 2 / 2 *
        Var[id; ν]) ∧
      (Integrable (fun x => Real.exp (2 * x)) ν →
        -(∫ x, x ∂ν) ≤ Real.log (∫ x, Real.exp (2 * x) ∂ν) / 2 ∧
        ∀ p : ℝ, 0 ≤ p → ∫ x, Real.exp (-p * x) ∂ν ≤ (∫ x, Real.exp (2 * x) ∂ν) ^ (p * (p + 1) /
          2))) :=
  by exact EhrhardGaussian.Provider.ehrhardType_characterization
end EhrhardGaussian

end

end

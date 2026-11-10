/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-
Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Gaussian.Poincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.EhrhardGaussian.Gaussian.GaussianPolynomial
public import LeanPool.EhrhardGaussian.Gaussian.Poincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import LeanPool.EhrhardGaussian.Gaussian.GaussianPolynomial

/-! Prepending a scalar coordinate to a finite real vector. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace EhrhardGaussian.Gaussian

/-- Prepend one scalar coordinate to a finite real vector. -/
def finCons {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  @Fin.cons n (fun _ : Fin (n + 1) => ℝ) x y






end EhrhardGaussian.Gaussian

end

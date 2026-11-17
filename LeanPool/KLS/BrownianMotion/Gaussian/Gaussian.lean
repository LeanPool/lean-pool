/-
Copyright (c) 2026 BrownianMotion contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BrownianMotion contributors
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Gaussian measures -/


@[expose] public section

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp NormedSpace

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma HasGaussianLaw.charFun_map_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (h : HasGaussianLaw X P) (t : ℝ) :
    charFun (P.map X) t = cexp (t * P[X] * I - t ^ 2 * Var[X; P] / 2) := by
  rw [h.map_eq_gaussianReal, IsGaussian.charFun_eq', covarianceBilin_real_self]
  simp [variance_nonneg, integral_complex_ofReal, mul_comm]

end ProbabilityTheory

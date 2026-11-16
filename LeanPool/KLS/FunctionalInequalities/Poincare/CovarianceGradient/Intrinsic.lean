/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Poincare.L2.Energy

/-!
# The affine covariance Poincaré constant

Source: Blueprint `def:affine-poincare-constant`, constant part. Read `optimalConstant`, `Holds`,
`holds_iff_constant_le`, then the zero-dimensional theorems.

`Poincare.CovarianceGradient.Intrinsic.constant μ` is `C_P^aff(μ)`: the generic `L²` Poincaré
optimizer
`Poincare.L2Energy.optimalConstant` of the intrinsic law `ν` of `μ` evaluated at the affine covariance
relaxation `Energy.CovarianceGradient.Intrinsic.energy μ`, the sequential `L²(ν)` relaxation of the
globally Lipschitz
covariance pre-energy with `Σ = Covariance.operator ν`. `Holds μ C` is validity of the finite
constant `C` on the finite-energy domain of that relaxation.

What this module claims: the two definitions, their exact order-theoretic equivalence, and that a
zero-dimensional affine support gives constant zero, because every `L²` class on a subsingleton
carrier has zero variance.

What this module does not claim: finiteness of the constant for any law, closability or the
closed-form identification of the relaxation, translation invariance, the isotropic reduction,
any comparison with `Poincare.SmoothGradient.Intrinsic.optimalConstant` or
`Poincare.LocalSlope.Intrinsic.optimalConstant`, or a KLS bound.
Log-concavity is not assumed by the definition; the Blueprint states it because the covariance is
then the honest second-moment covariance and the gradient is defined almost everywhere, see
`KLS/LogConcave/Covariance.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The affine covariance Poincaré constant `C_P^aff(μ)`: the optimal extended constant of the
affine covariance relaxation on the intrinsic law. -/
def optimalConstant (μ : ProbabilityMeasure E) : ENNReal :=
  L2Energy.optimalConstant (Probability.intrinsicMeasure μ) (Energy.CovarianceGradient.Intrinsic.energy μ)

/-- Validity of a finite constant on the finite-energy domain of the affine covariance
relaxation of the intrinsic law. -/
def Holds (μ : ProbabilityMeasure E) (C : NNReal) : Prop :=
  L2Energy.Holds (Probability.intrinsicMeasure μ) (Energy.CovarianceGradient.Intrinsic.energy μ) C

section IntrinsicConstants

omit [CompleteSpace E]
/-- A finite constant is valid for the affine covariance relaxation exactly when it bounds the
optimal extended constant. -/
theorem holds_iff_constant_le (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds μ C ↔ optimalConstant μ ≤ (C : ENNReal) :=
  L2Energy.holds_iff_constant_le (Probability.intrinsicMeasure μ)
    (Energy.CovarianceGradient.Intrinsic.energy μ) C

/-- Unfolding the affine constant exposes the generic `L²` optimizer of the intrinsic law at the
sequential relaxation of the covariance pre-energy. -/
theorem constant_eq (μ : ProbabilityMeasure E) :
    optimalConstant μ =
      L2Energy.optimalConstant (Probability.intrinsicMeasure μ)
        ((Energy.CovarianceGradient.preEnergy
            (Probability.intrinsicMeasure μ)).sequentialRelaxation) :=
  rfl

/-- A zero-dimensional direction space gives affine constant zero: every intrinsic `L²` class
is constant there. -/
theorem constant_eq_zero_of_subsingleton (μ : ProbabilityMeasure E)
    [Subsingleton (Probability.affineSupport μ).direction] : optimalConstant μ = 0 :=
  L2Energy.constant_eq_zero_of_subsingleton _ _

/-- The zero-dimensional case stated through the direction submodule. -/
theorem constant_eq_zero_of_direction_eq_bot (μ : ProbabilityMeasure E)
    (h : (Probability.affineSupport μ).direction = ⊥) : optimalConstant μ = 0 := by
  have : Subsingleton (Probability.affineSupport μ).direction :=
    Submodule.subsingleton_iff_eq_bot.mpr h
  exact constant_eq_zero_of_subsingleton μ

end IntrinsicConstants

end FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic

/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv
public import LeanPool.KLS.FunctionalInequalities.Poincare.L2.Energy

/-! # Poincaré constants under covariance-gradient transport -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace FunctionalInequalities.Poincare.CovarianceGradient
open Energy.CovarianceGradient
universe u v

section Translation

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]
  (ν : ProbabilityMeasure V) (c : V)

/-- The optimal `L²` Poincaré constant of the covariance relaxation is translation invariant. -/
theorem constant_translateLaw :
    Poincare.L2Energy.optimalConstant (Probability.translateLaw ν c)
        (relaxation (Probability.translateLaw ν c)) =
      Poincare.L2Energy.optimalConstant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv ν (Probability.translateLaw ν c)
    (relaxation ν) (relaxation (Probability.translateLaw ν c))
    (L2.Translation.pullbackEquiv ν c) (L2.Translation.variance_pullbackEquiv ν c)
    (relaxation_translateLaw ν c)

end Translation

section Isometry

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

omit [SecondCountableTopology V₁] in
/-- The optimal `L²` Poincaré constant of the covariance relaxation is invariant under linear
isometric equivalences. -/
theorem constant_mapLinearIsometryEquiv :
    Poincare.L2Energy.optimalConstant (Probability.mapLinearIsometryEquiv ν L)
        (relaxation (Probability.mapLinearIsometryEquiv ν L)) =
      Poincare.L2Energy.optimalConstant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv ν
    (Probability.mapLinearIsometryEquiv ν L) (relaxation ν)
    (relaxation (Probability.mapLinearIsometryEquiv ν L)) (L2.LinearIsometry.pullbackEquiv ν L)
    (L2.LinearIsometry.variance_pullbackEquiv ν L) (relaxation_mapLinearIsometryEquiv ν L)

end Isometry

section LinearEquiv

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂]
  (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

omit [SecondCountableTopology V₁] in
/--
The optimal `L²` Poincaré constant of the covariance relaxation is invariant under continuous
linear equivalences. -/
theorem constant_mapContinuousLinearEquiv :
    Poincare.L2Energy.optimalConstant (Probability.mapContinuousLinearEquiv ν T)
        (relaxation (Probability.mapContinuousLinearEquiv ν T)) =
      Poincare.L2Energy.optimalConstant ν (relaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv ν
    (Probability.mapContinuousLinearEquiv ν T) (relaxation ν)
    (relaxation (Probability.mapContinuousLinearEquiv ν T))
    (L2.ContinuousLinearEquiv.pullbackEquiv ν T)
    (L2.ContinuousLinearEquiv.variance_pullbackEquiv ν T)
    (relaxation_mapContinuousLinearEquiv ν T)

end LinearEquiv

end FunctionalInequalities.Poincare.CovarianceGradient

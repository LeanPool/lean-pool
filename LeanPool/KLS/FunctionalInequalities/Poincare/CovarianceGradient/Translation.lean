/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.IntrinsicTranslation
public import LeanPool.KLS.FunctionalInequalities.Poincare.CovarianceGradient.Transport
public import LeanPool.KLS.FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic

/-!
# Ambient translation invariance of the affine covariance Poincaré constant

Source: Blueprint `lem:affine-poincare-translation-invariance`, the identity
`C_P^aff((τ_b)_# μ) = C_P^aff(μ)` for `τ_b(x) = x + b`. Read
`Probability.affineSupport_translateLaw`,
`Probability.direction_affineSupport_translateLaw`, `Probability.intrinsicMeasure_translateLaw`,
`Energy.CovarianceGradient.Intrinsic.exists_translateLaw_isometry` and
`Poincare.CovarianceGradient.Intrinsic.constant_translateLaw`.

For a probability law `μ` on a finite-dimensional Euclidean space `E` and `b ∈ E`, the translated
law `Probability.translateLaw μ b` is the image of `μ` under `x ↦ b + x`. Its affine support
is the translate of the affine support of `μ`, so both have the same direction submodule `V`; the
two intrinsic coordinate presentations differ by the linear isometric identification of the two
(equal) direction submodules followed by a translation inside the direction space. Hence the
intrinsic law of the translated law is a translate of the isometric image of the intrinsic law of
`μ`; the covariance relaxations correspond under the resulting `L²` isometry, which preserves
variance, and the affine covariance Poincaré constants coincide. The ambient covariance operator is
also unchanged. Finally, translating by the negative barycenter gives a law with zero mean whenever
the identity is integrable.

What this module claims: the statements above, for every Borel probability law on `E` and every
`b`, including the zero-dimensional direction space. What it does not claim: log-concavity of the
translated law (proved in `KLS/LogConcave/Translation.lean` from the compact-set
definition), any Poincaré inequality, finiteness of the constant, the isotropic reduction, or
invariance under any non-translation affine map of `E`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic

open Energy.CovarianceGradient.Intrinsic Probability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

  (μ : ProbabilityMeasure E) (b : E)

omit [CompleteSpace E] in
/--
The affine covariance Poincaré constant is invariant under ambient translations of the law. -/
theorem constant_translateLaw : optimalConstant (Probability.translateLaw μ b) = optimalConstant μ := by
  unfold optimalConstant
  rw [energy_eq_relaxation_intrinsicMeasure (Probability.translateLaw μ b),
    energy_eq_relaxation_intrinsicMeasure μ, Probability.intrinsicMeasure_translateLaw,
    Poincare.CovarianceGradient.constant_translateLaw,
    Poincare.CovarianceGradient.constant_mapLinearIsometryEquiv]

end FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic

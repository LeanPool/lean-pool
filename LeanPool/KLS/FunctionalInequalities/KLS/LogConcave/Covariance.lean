/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Intrinsic

/-!
# Log-concave discharge of the affine covariance pre-energy contracts

Source: Blueprint `def:affine-poincare-constant`, the sentence "the absolute continuity in the
Borell representation and Rademacher's theorem make the gradient well defined `ν`-almost
everywhere". Read `intrinsic_memLp_id_two`, `intrinsic_ae_hasGradientAt`,
`intrinsic_gradient_ae_eq_of_ae_eq`, then `KLS.LogConcave.intrinsicCovariance_energy_eq_of_toL2_eq`.

For a compact-set log-concave law `μ` with intrinsic law `ν` on the direction space `V`:

* `ν` has a finite second moment, so `Covariance.operator ν` is the honest covariance and not
  Mathlib's zero convention;
* every globally Lipschitz test is differentiable `ν`-almost everywhere with the canonical
  gradient as derivative, by the proved intrinsic absolute continuity and Rademacher's theorem;
* continuous representatives of one `L²(ν)` class have `ν`-almost everywhere equal gradients,
  because the frontier of the support of `ν` is `ν`-null, so the covariance energy of a test
  depends only on its `L²(ν)` class.

These are the well-definedness contracts of the definition node. Nothing here asserts
closability, density of the realization, a Poincaré inequality, translation invariance or any
KLS conclusion. The zero-dimensional direction space is included in every statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E} (hμ : LogConcave μ)

include hμ in
/-- The intrinsic law of a log-concave probability has a finite second moment, so its
covariance operator is the genuine centered covariance. -/
theorem intrinsic_memLp_id_two :
    MemLp id 2
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  rw [memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id]
  simpa using hμ.intrinsic_integrable_norm_pow 2

include hμ in
/-- Rademacher on the intrinsic law: every affine covariance test is differentiable
`ν`-almost everywhere, with the canonical gradient as its derivative. -/
theorem intrinsic_ae_hasGradientAt
    (f : Energy.CovarianceGradient.Test (Probability.intrinsicMeasure μ)) :
    ∀ᵐ v ∂(Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction),
      HasGradientAt f.toFun (gradient f.toFun v) v :=
  f.ae_hasGradientAt Measure.addHaar (hμ.intrinsic_absolutelyContinuous Measure.addHaar)

include hμ in
/-- Continuous representatives of one intrinsic `L²` class have `ν`-almost everywhere equal
canonical gradients: the frontier of the intrinsic support is `ν`-null. -/
theorem intrinsic_gradient_ae_eq_of_ae_eq {g₁ g₂ : (Probability.affineSupport μ).direction → ℝ}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ =ᵐ[(Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction)] g₂) :
    gradient g₁ =ᵐ[(Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction)] gradient g₂ :=
  Energy.Euclidean.gradient_ae_eq_of_ae_eq hμ.intrinsic_frontier_support_eq_zero h₁ h₂ h

include hμ in
/-- The affine covariance energy of a test depends only on its intrinsic `L²` class. -/
theorem intrinsicCovariance_energy_eq_of_toL2_eq
    {f g : Energy.CovarianceGradient.Test (Probability.intrinsicMeasure μ)}
    (hfg : f.toL2 = g.toL2) : f.energy = g.energy :=
  Energy.CovarianceGradient.Test.energy_eq_of_toL2_eq
    hμ.intrinsic_frontier_support_eq_zero hfg

end FunctionalInequalities.KLS.LogConcave

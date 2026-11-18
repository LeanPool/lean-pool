/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Positivity

/-!
# Full affine support of isotropic laws

An isotropic law has identity covariance, hence an injective covariance operator and full affine
support. This module proves the fact with light imports; the Section 2 reduction module restates
it with heavier imports.
-/

@[expose] public section

open MeasureTheory

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An isotropic law has full affine support. -/
theorem Isotropic.affineSupport_eq_top {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ := by
  apply Probability.affineSupport_eq_top_of_covariance_injective μ hiso.memLp_two
  rw [hiso.covariance_identity]
  exact fun _ _ h => h

end FunctionalInequalities.KLS

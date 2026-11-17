/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Norm
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction

/-!
# Borell representation on the affine support

Source: Blueprint `thm:borell-logconcave-density`, Borell (1974), *Convex measures on locally
convex spaces*, Theorem 1.1 and its finite-dimensional consequences; Bobkov (1999) for the
exponential tail. Read `IsBorellDensity`, then the representative properties, the moment
section, the construction, and finally the intrinsic theorems at the end.

The intrinsic law `ν` of a compact-set log-concave probability `μ` lives on the direction
space `V` of the affine support and is absolutely continuous with respect to every additive
Haar measure `m` on `V`; that part is proved in `KLS/LogConcave/Density/AbsoluteContinuity.lean`.
This module proves the remaining conclusions of the representation theorem:

1. `ν` has a density representative `ρ : V → ℝ` that is Borel, nonnegative, finite-valued,
   upper semicontinuous and log-concave, with `ν = ρ · m` (`IsBorellDensity`,
   `LogConcave.exists_isBorellDensity`);
2. every such representative is positive and continuous on the interior `Ω` of the support of
   `ν` and is bounded above and below by positive constants on every compact subset of `Ω`
   (`IsBorellDensity.pos_of_mem_interior_support`, `IsBorellDensity.continuousOn_interior_support`,
   `IsBorellDensity.exists_bounds_of_isCompact`);
3. `ν` has an exponential moment, hence finite moments of every order
   (`LogConcave.intrinsic_integrable_exp_norm`, `LogConcave.intrinsic_integrable_norm_pow`).

Proof routes. The representative is the upper semicontinuous envelope of the lower density
`liminf ν(B(x, rₙ)) / m(B(0, rₙ))` along `rₙ = 1/(n+1)`: the lower density is log-concave
because equal-radius ball masses are, it is bounded by the proved small-ball estimate, and it
equals the Radon--Nikodym derivative almost everywhere by the Besicovitch differentiation
theorem; the envelope changes it only on the Haar-null frontier of its convex positivity set.
Positivity and the compact bounds use that a convex set with empty interior is Haar-null and that
the logarithm of a log-concave function is concave, hence continuous, on the open interior of the
positivity set. The exponential moment is Borell's lemma applied through the proved Borel-set
formulation: once a ball of radius `R` carries mass `3/4`, the mass outside radius `k R` is at
most `3^{(1-k)/2}`, and the exponential is dominated by a geometric series.

Quantities: `Ω` is `interior ν.support`. The Blueprint writes `Ω` as the interior of the closed
convex hull of the topological support; the two descriptions coincide because the support of a
log-concave law is closed and convex, and `closure_convexHull_intrinsic_support` proves this.
`ν (Ωᶜ) = 0` is `intrinsic_interior_support_compl`.

Reference measures are arbitrary additive Haar measures, so the theorem includes the
zero-dimensional direction space, where every Haar measure is a positive multiple of the Dirac
mass and `ρ` is a positive constant. Nothing here assumes a positive dimension, a density, a
second moment or full-dimensional ambient support. Pointwise bounds on compact subsets are
stronger than the `L^∞_loc` phrasing of the Blueprint and imply it. No Poincaré, Cheeger,
Dirichlet or KLS statement is asserted here.


The implementation is organized by responsibility: Basic, Moments, Construction, Intrinsic.
Import the earliest layer containing the required interface.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Topology Filter

namespace FunctionalInequalities

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]

namespace KLS.LogConcave

section IntrinsicDensity

omit [CompleteSpace F]
/-- The support of the intrinsic law is already its own closed convex hull. Hence the interior
of the closed convex hull of the support, as written in the Blueprint, is `interior ν.support`. -/
theorem closure_convexHull_intrinsic_support {μ : ProbabilityMeasure F} (hμ : LogConcave μ) :
    closure
        (convexHull ℝ
          (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction).support) =
      (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction).support := by
  rw [hμ.intrinsicMeasure.convex_support.convexHull_eq, Measure.isClosed_support.closure_eq]

/-- The intrinsic law gives zero mass to the complement of the interior of its support. This is
the `ν(V ∖ Ω) = 0` clause; it follows from the proved null-frontier result. -/
theorem intrinsic_interior_support_compl {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
      (interior (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction).support)ᶜ = 0 := by
  set ν : Measure (Probability.affineSupport μ).direction :=
    (Probability.intrinsicMeasure μ).toMeasure
  have hsub : (interior ν.support)ᶜ ⊆ ν.supportᶜ ∪ frontier ν.support := by
    intro x hx
    by_cases hS : x ∈ ν.support
    · exact Or.inr ⟨subset_closure hS, hx⟩
    · exact Or.inl hS
  exact measure_mono_null hsub
    (measure_union_null Measure.measure_compl_support hμ.intrinsic_frontier_support_eq_zero)

/-- Existence of a Borell density representative of the intrinsic law relative to any additive
Haar measure on the direction of the affine support. Absolute continuity is already proved; the
obligation is to choose an upper semicontinuous log-concave finite-valued version of the
Radon--Nikodym density. Includes dimension zero. -/
theorem exists_isBorellDensity {μ : ProbabilityMeasure F} (hμ : LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    ∃ ρ : (Probability.affineSupport μ).direction → ℝ,
      IsBorellDensity (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) m ρ :=
  hμ.intrinsicMeasure.exists_isBorellDensity_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty (hμ.intrinsic_absolutelyContinuous m)

/-- The intrinsic law of a log-concave probability has an exponential moment: some positive
rate `t` makes `exp (t ‖v‖)` integrable. This is the tail estimate behind the moment
conclusion and is stated separately because it is the form proved in the literature. -/
theorem intrinsic_integrable_exp_norm {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖))
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  ((borel_iff _).1 hμ.intrinsicMeasure).exists_integrable_exp_norm

/-- The intrinsic law of a log-concave probability has finite moments of every order.
It follows from the exponential moment and Mathlib's `IntegrableExpMul`. -/
theorem intrinsic_integrable_norm_pow {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p)
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  obtain ⟨t, ht, hint⟩ := hμ.intrinsic_integrable_exp_norm
  exact Probability.integrable_norm_pow_of_exp _ ht hint p

end IntrinsicDensity

end KLS.LogConcave

end Intrinsic

end FunctionalInequalities

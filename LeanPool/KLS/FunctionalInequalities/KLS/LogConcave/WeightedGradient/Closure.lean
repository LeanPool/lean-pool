/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic

/-!
# Closed weighted gradient for a full-dimensional log-concave law

The closure is closed and densely defined for every bounded linear weight `B`.
This interface has no dependency on semigroup generation. The domain, core and zero-dimensional
scope are inherited unchanged from the closable weighted-gradient construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

open Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section FullDimensional

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)

/-- The closed weighted gradient `Tbar`: the closure of `g ↦ B ∘ ∇g` on `L²(ν)`. -/
abbrev closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  (hν.weightedOperator m B hi).closure

/-- `Tbar` is closed. -/
theorem closedWeightedOperator_isClosed (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.closedWeightedOperator m B hi).IsClosed :=
  (hν.weightedOperator_isClosable m B hi).closure_isClosed

/-- Every weighted-gradient test class lies in the domain of `Tbar`. This is the general-test
form of `KLS.LogConcave.toLp_mem_closedWeightedOperator_domain`, whose test is smooth and
compactly supported. -/
theorem toLp_mem_closedWeightedOperator_domain_of_isTest (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {g : V → ℝ}
    (h : WeightedGradient.IsTest ν B g) :
    h.memLp.toLp g ∈ (hν.closedWeightedOperator m B hi).domain :=
  (LinearPMap.le_closure _).1
    (WeightedGradient.toLp_mem_domain_operator ν B (hν.absolutelyContinuous_haar m hi) h)

/-- `Tbar` sends a test class to the class of its weighted gradient. This is the general-test form
of `KLS.LogConcave.closedWeightedOperator_toLp_eq`. -/
theorem closedWeightedOperator_apply_toLp (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {g : V → ℝ}
    (h : WeightedGradient.IsTest ν B g) :
    hν.closedWeightedOperator m B hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi h⟩ =
      h.memLp_apply.toLp (WeightedGradient.apply B g) := by
  have hmem := WeightedGradient.toLp_mem_domain_operator ν B (hν.absolutelyContinuous_haar m hi) h
  rw [← (LinearPMap.le_closure (hν.weightedOperator m B hi)).2 (x := ⟨_, hmem⟩)
    (y := ⟨_, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi h⟩) rfl,
    WeightedGradient.operator_apply ν B _ (hν.frontier_support_eq_zero hi) h hmem rfl]

/-- `Tbar` is densely defined: its domain contains the dense domain of `T`. -/
theorem dense_domain_closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.closedWeightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  (hν.dense_domain_weightedOperator m B hi).mono fun _ hx =>
    (LinearPMap.le_closure (hν.weightedOperator m B hi)).1 hx

end FullDimensional

end FunctionalInequalities.KLS.LogConcave

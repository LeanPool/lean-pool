/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import LeanPool.FormalLearningTheory.Learner.Bayesian
public import LeanPool.FormalLearningTheory.Criterion.Gold
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import LeanPool.FormalLearningTheory.Learner.Active
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Extended and Cross-Paradigm Criteria

Universal learning: distribution-free convergence rates.
-/

@[expose] public section

universe u

/-- Universal learning: distribution-free convergence rates.
    Strictly stronger than PAC.

    Sample space: Fin m → X with i.i.d. product measure D^m (matching PACLearnable).
    Labels: derived deterministically from target concept c (realizable case).
    The rate function converges to 0, and for every m, with probability ≥ 2 / 3
    over D^m, the learner's error is at most rate(m).

    Γ₄₈ fix: changed from existential Dm to Measure.pi (CNA₁₁ definition repair). -/
def UniversalLearnable (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∃ (L : BatchLearner X Bool) (rate : ℕ → ℝ),
    (∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε) ∧
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3)

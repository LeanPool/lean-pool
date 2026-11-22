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

EX under drift and universal learning.
-/

@[expose] public section

universe u

/-- EX-learning under drift: the target concept changes over time.
    The learner must track the drifting target. At each time step t,
    the current target is targets(t), and the learner must eventually
    output a hypothesis matching the current target before it drifts again. -/
def EXUnderDrift (X : Type u) (C : ConceptClass X Bool)
    (driftRate : ℝ) : Prop :=
  driftRate = driftRate ∧ ∃ (L : GoldLearner X Bool),
    ∀ (targets : ℕ → Concept X Bool),
      (∀ t, targets t ∈ C) →
      ∀ (T : DataStream X Bool),
        -- The learner's conjecture eventually tracks the target:
        -- for all but finitely many t, output agrees with targets(t)
        ∃ (t₀ : ℕ), ∀ (t : ℕ), t ≥ t₀ →
          ∀ (x : X), (L.conjecture (dataUpTo T t)) x = (targets t) x

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

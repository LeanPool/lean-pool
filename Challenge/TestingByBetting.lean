/-
Copyright (c) 2026 deadczarvc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: deadczarvc
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration

/-!
# Ville's inequality for testing by betting

Source: arxiv:2210.01948
Proposed by: deadczarvc
Open declarations: `Challenge.TestingByBetting.ville`
Tags: probability, martingales, sequential-testing, e-values
MSC: 60G42, 62L10
Estimated size: ~400 lines of Lean

Informal statement:
* `Challenge.TestingByBetting.ville` — Let X₁, X₂, … be real random variables adapted to a
  filtration (ℱₙ) on a probability space, with values in [-1, 1], such that the conditional
  expectation of Xₙ₊₁ given ℱₙ is at most 0 almost surely for every n. Let λ₁, λ₂, … take values in
  [0, 1], with λₙ₊₁ measurable with respect to ℱₙ (predictable stakes), and let Wₙ = ∏_{i < n} (1 +
  λᵢ₊₁ Xᵢ₊₁) be the wealth after n rounds (W₀ = 1). Then for every α > 0 the probability that Wₙ ≥
  1/α for some n is at most α.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Challenge.TestingByBetting

/-- Ville's inequality for testing by betting: under the null `E[Xₙ₊₁ | ℱₙ] ≤ 0`, the wealth of a
bettor staking a predictable fraction `λₙ₊₁ ∈ [0, 1]` reaches `1/α` with probability at most `α`. -/
theorem ville {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (X lam : ℕ → Ω → ℝ)
    (hX : Adapted ℱ X) (hXb : ∀ n ω, -1 ≤ X n ω ∧ X n ω ≤ 1)
    (hlam : ∀ n, StronglyMeasurable[ℱ n] (lam (n + 1))) (hlamb : ∀ n ω, 0 ≤ lam n ω ∧ lam n ω ≤ 1)
    (hnull : ∀ n, μ[X (n + 1) | ℱ n] ≤ᵐ[μ] 0)
    {α : ℝ} (hα : 0 < α) :
    μ {ω | ∃ n : ℕ, α⁻¹ ≤ ∏ i ∈ Finset.range n, (1 + lam (i + 1) ω * X (i + 1) ω)}
      ≤ ENNReal.ofReal α := sorry

end Challenge.TestingByBetting

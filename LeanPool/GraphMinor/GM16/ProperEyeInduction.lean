/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ProperEyeInductionStep
public import LeanPool.GraphMinor.GM15.Section8

/-!
# Proper arrangements through the downward eye induction

The induction in XV, pages 115–116, repeatedly applies the eye step.
The arrangement outcome keeps the same discs while its numerical bounds
increase. We retain its properness for XVI (7.2), page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

/-- XV (1.1), pages 115–116, with the properness retained from the actual
arrangement construction, as required in XVI (7.2), page 62. -/
theorem proper_arrangement_or_independent_eyes_or_crosscap
     :
    ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (κ φ μ : ℕ),
      ∃ (θ lam p : ℕ),
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ ≤ θ₀ →
          (∃ (H' : Drawing S) (η' : SpanEmbedding H' G) (θ' : ℕ)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ),
            IsSigmaSpan G H' η' θ_star θ' T_star T' ∧
            HasTangleMetric H' θ' T' d' ∧
            φ ≤ θ' ∧
            HasIndependentEyes G H' η' θ' T' d' (κ + 1)) ∨
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
            IsObtainedByAddingCrosscap S S' ∧
            ∃ (H' : Drawing S') (η' : SpanEmbedding H' G) (θ' : ℕ)
              (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
               φ ≤ θ' ∧ IsSigmaSpan G H' η' θ_star θ' T_star T') ∨
          (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
            IsCentralSegregation G T_star 𝒮 ∧
            GM15.IsSegregationOfType G p κ 𝒮 ∧ IsProperArrangement 𝒮 disc pt) :=
  GM15.theorem_1_1_proper

end GraphMinor.GM16

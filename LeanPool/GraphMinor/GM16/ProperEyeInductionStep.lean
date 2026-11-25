/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.EyeInductionParameters
public import LeanPool.GraphMinor.GM16.ProperLocalAssembly

/-!
# Properness through the eye induction

The induction step in XV (1.2), proved on pages 144–145, either creates
another eye, adds a crosscap, or uses the arrangement from XV (7.7).
We retain the properness of that arrangement in the third outcome,
as required by XVI (7.2), page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w

/-- The induction step of XV (1.2), retaining the proper arrangement
from XV (7.7) for the use in XVI (7.2), page 62. -/
theorem proper_eye_induction_step
     :
    ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ (k φ μ lam_next θ_next : ℕ),
      8 ≤ φ → 12 ≤ μ → Even μ → 4 ≤ lam_next →
      4 * lam_next + μ + 2 ≤ θ_next →
      ∃ (p_k lam_k θ_k : ℕ),
        4 * lam_k + μ + 2 ≤ θ_k ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H₀ : Drawing S) (η₀ : SpanEmbedding H₀ G) (θ₀ : ℕ)
          (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d₀ : Set S → Set S → ℕ),
          IsFlatSpan G H₀ η₀ θ_star θ₀ lam_k μ T_star T₀ →
          HasTangleMetric H₀ θ₀ T₀ d₀ →
          θ_k ≤ θ₀ →
          HasEyesAtDistance G H₀ η₀ θ₀ T₀ d₀ k θ_k →
          Section7S1 S G θ_star T_star k μ lam_next θ_next ∨
          Section7S2 S G θ_star T_star φ ∨
          (∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
            IsCentralSegregation G T_star 𝒮 ∧
            GM15.IsSegregationOfType G p_k k 𝒮 ∧ IsProperArrangement 𝒮 disc pt) :=
  GM15.theorem_1_2_proper

end GraphMinor.GM16

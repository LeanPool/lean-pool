/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM12.Section4Theorem45Large
import LeanPool.GraphMinor.GM12.Section3GeometricReduction
import LeanPool.GraphMinor.GM12.Section4CliqueControlMonotone
import LeanPool.GraphMinor.GM12.Section4InducedEmbedding

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.5): all clique sizes

Carry out the crossing construction for a complete graph of
size at least four, then retain the desired clique branches.
This supplies the small-parameter reduction on page 252.
For a literal drawn subgraph, its identity embedding identifies
the controlling ambient tangle with the induced tangle in the
paper's conclusion.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph Hypergraph GM14 GM15

universe u

/-- XII (4.5), pages 252--253, in the span formulation, with
region distances only bounded below by the chosen threshold.
The only statement hypotheses are VII (7.5), (5.1), and (5.5).
The source clique has size `max p 4`, instead of the paper's
reduction to at least five, before retaining the desired branches. -/
theorem theorem_4_5_span
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ k N : ℕ, 1 ≤ N ∧ ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
      (Tstar : Set (Hypergraph α β × Hypergraph α β)) (Γ : Drawing S)
      (η : SpanEmbedding Γ G) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N ≤ θ →
      ∀ (r : Fin k → Set S) (P Q : Fin k → Graph α β),
      Function.Injective r → (∀ i, IsEyeWithPaths G Γ η θ T (r i) (P i) (Q i)) →
      (∀ i j, i ≠ j → N ≤ d (r i) (r j)) →
      (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
        ((P j).vertexSet ∪ (Q j).vertexSet)) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  obtain ⟨k, N, hN, hmain⟩ := theorem_4_5_span_large hS (max p 4) (le_max_right _ _)
  refine ⟨k, N, hN, ?_⟩
  intro α β G θstar θ Tstar Γ η T d hCtrl hm hθ r P Q hri heye hfar hdisj
  exact controlsMinor_completeGraph_mono (le_max_left p 4)
    (hmain G θstar θ Tstar Γ η T d hCtrl hm hθ r P Q hri heye hfar hdisj)

/-- Graph Minors XII (4.5), pages 252--253, for a literal drawn
subgraph of the ambient graph and its induced tangle, as in the
paper. The eye data are the circuit, free four-vertex set, and
two external paths stated there. -/
theorem theorem_4_5_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ k N : ℕ, 1 ≤ N ∧ ∀ (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (G : Graph S (Set S))
      (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite),
      Γ.toGraph ≤ G → HasTangleMetric Γ θ T d → N ≤ θ →
      ∀ (r : Fin k → Set S) (C : Fin k → Drawing S) (a b c d' : Fin k → S)
        (P Q : Fin k → Graph S (Set S)),
      Function.Injective r → (∀ i, r i ∈ Γ.R) →
      (∀ i, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ ∧ (C i).U = subBd (r i)) →
      (∀ i, a i ∈ (C i).V ∧ b i ∈ (C i).V ∧ c i ∈ (C i).V ∧ d' i ∈ (C i).V) →
      (∀ i, ([a i, b i, c i, d' i]).Nodup ∧ OccurInCircuitOrder (C i) (a i) (b i) (c i) (d' i)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ {a i, b i, c i, d' i}) →
      (∀ i, IsHPathWithEnds G Γ.toGraph (P i) (a i) (c i) ∧
        IsHPathWithEnds G Γ.toGraph (Q i) (b i) (d' i)) →
      (∀ i, Disjoint (P i).vertexSet (Q i).vertexSet) →
      (∀ i j, i ≠ j → N ≤ d (r i) (r j)) →
      (∀ i j, i ≠ j → Disjoint ((P i).vertexSet ∪ (Q i).vertexSet)
        ((P j).vertexSet ∪ (Q j).vertexSet)) →
      ControlsMinor (Hypergraph.ofGraph G hV hE) θ
        (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T)
        (GM16.completeGraph p) := by
  obtain ⟨k, N, hN, hmain⟩ := theorem_4_5_span hS p
  refine ⟨k, N, hN, ?_⟩
  intro Γ θ T d G hV hE hΓG hm hθ r C a b c d' P Q hri hr hC hmarks hord hfree hPQ hdisj hfar hcross
  obtain ⟨η, hηG, hηv, _, hCtrl⟩ := exists_identity_embedding_induced_tangle Γ hV hE hΓG hm.1.2.1
  apply hmain G θ θ _ Γ η T d hCtrl hm hθ r P Q hri ?_ hfar hcross
  intro i
  refine ⟨hr i, C i, a i, b i, c i, d' i, (hC i).1, (hC i).2.1, (hC i).2.2,
    (hmarks i).1, (hmarks i).2.1, (hmarks i).2.2.1, (hmarks i).2.2.2,
    (hord i).1, (hord i).2, hfree i, hdisj i, ?_, ?_⟩
  · simpa only [hηv, hηG] using (hPQ i).1
  · simpa only [hηv, hηG] using (hPQ i).2

end GraphMinor.GM12

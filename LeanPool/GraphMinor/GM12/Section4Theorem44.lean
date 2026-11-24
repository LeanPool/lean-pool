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
import LeanPool.GraphMinor.GM12.Section4Theorem44Large
import LeanPool.GraphMinor.GM12.Section4SmallClique
import LeanPool.GraphMinor.GM12.Section4Theorem43
import LeanPool.GraphMinor.GM12.Section3GeometricReduction
import LeanPool.GraphMinor.GM12.Section4SpanControl
import LeanPool.GraphMinor.GM12.Section4InducedEmbedding

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.4): all clique sizes

Use the path and branch construction of pages 251--252 when the
clique has at least three vertices. For the smaller cliques, the
target is drawable in the surface, so (4.3) applies as the paper
instructs. The conclusion is expressed for an embedded drawing and
an ambient tangle controlling its tangle.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM14 GM15

universe u

/-- XII (4.4), pages 251--252, with the embedding and tangle
relation explicit. The only statement hypotheses are the cited
VII (7.5), (5.1), and (5.5). -/
theorem theorem_4_4_span
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ {α β : Type*} (G : Graph α β) (θstar θ : ℕ)
        (Tstar : Set (Hypergraph α β × Hypergraph α β))
        (Γ : Drawing S) (η : SpanEmbedding Γ G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph α β)
        (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T),
      HasTangleMetric Γ θ T d → N ≤ θ →
      (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
      Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
      (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y → N ≤ d {x} {y}) →
      (∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (s i)) (η.vMap (r i))) →
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
      ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
        hCtrl.isTangle_star.finite_E) θstar Tstar (GM16.completeGraph p) := by
  by_cases hp : 3 ≤ p
  · exact theorem_4_4_span_large hS p hp
  · obtain ⟨D⟩ := exists_graphDrawing_complete_of_le_two hS (show p ≤ 2 by omega)
    obtain ⟨N, hN, hmain⟩ := theorem_4_3_drawing hS D
    refine ⟨N, hN, ?_⟩
    intro α β G θstar θ Tstar Γ η T d s r P hCtrl hm hθ _ _ _ _ _ _ _
    exact controlsMinor_of_controlling_drawing_tangle η hCtrl (hmain Γ θ T d hm hθ)

/-- Graph Minors XII (4.4), pages 251--252, for the tangle induced
from a literal drawn subgraph of the ambient graph. All vertex and
edge names are shared with the drawing, as in the paper. -/
theorem theorem_4_4_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (G : Graph S (Set S))
        (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite),
      Γ.toGraph ≤ G → HasTangleMetric Γ θ T d → N ≤ θ →
      ∀ (s r : Fin (p * (p - 1) / 2) → S) (P : Fin (p * (p - 1) / 2) → Graph S (Set S)),
      (∀ i, s i ∈ Γ.V ∧ r i ∈ Γ.V ∧ s i ≠ r i) →
      Function.Injective s → Function.Injective r → Disjoint (range s) (range r) →
      (∀ x ∈ range s ∪ range r, ∀ y ∈ range s ∪ range r, x ≠ y → N ≤ d {x} {y}) →
      (∀ i, IsHPathWithEnds G Γ.toGraph (P i) (s i) (r i)) →
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) →
      ControlsMinor (Hypergraph.ofGraph G hV hE) θ
        (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T) (GM16.completeGraph p)
          := by
  obtain ⟨N, hN, hmain⟩ := theorem_4_4_span hS p
  refine ⟨N, hN, ?_⟩
  intro Γ θ T d G hV hE hΓG hm hθ s r P hends hs hr hsr hfar hP hPP
  obtain ⟨η, hηG, hηv, _, hCtrl⟩ := exists_identity_embedding_induced_tangle Γ hV hE hΓG hm.1.2.1
  apply hmain G θ θ _ Γ η T d s r P hCtrl hm hθ hends hs hr hsr hfar
  · intro i
    have h := hP i
    simpa only [hηv, hηG] using h
  · exact hPP

end GraphMinor.GM12

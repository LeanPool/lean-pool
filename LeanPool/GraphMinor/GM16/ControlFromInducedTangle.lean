/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM16.HypergraphImageTangle
public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM16.Section8Truncation
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Control from a conformal induced tangle

Relabel a tangle in a subgraph to its drawing. A restricted small
side in that drawing has the same edge set in the subgraph after
applying the inverse edge map. It therefore belongs to the
induced ambient tangle, which is contained in the original one.
The tangle orientation axiom gives the converse. This establishes
the control condition for the sphere span in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph Surface GM10 GM14 GM15
universe u v w

/-- A drawing relabelling of a subgraph tangle is controlled by the
ambient tangle when its induced ambient tangle is a subset of it. -/
theorem controllingTangle_of_induced_subset
    {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G N : Graph α β} {D : Drawing S} (η : SpanEmbedding D G) (hImage : η.imageGraph = N)
    {θstar θ : ℕ} {Tstar : Set (Hypergraph α β × Hypergraph α β)}
    (hTstar : IsGraphTangle G θstar Tstar) (hθ : θ ≤ θstar)
    (hVN : V(N).Finite) (hEN : E(N).Finite) (TN : Set (Hypergraph α β × Hypergraph α β))
    (hTN : IsTangle (Hypergraph.ofGraph N hVN hEN) θ TN)
    (f : α → S) (g : β → Set S) (hInv : LeftInvOn η.eMap g E(N))
    (hTD : IsTangle D.toHypergraph θ (imageHypergraphTangle f g TN))
    (hConformal : inducedTangle (Hypergraph.ofGraph G hTstar.finite_V hTstar.finite_E)
      (Hypergraph.ofGraph N hVN hEN) TN θ ⊆ Tstar) :
    IsControllingTangle G D η θstar θ Tstar (imageHypergraphTangle f g TN) := by
  have hForces {A B : Hypergraph α β}
      (hSep : (Hypergraph.ofGraph G hTstar.finite_V hTstar.finite_E).IsSeparation A B)
      (hOrd : separationOrder A B < θ) {AH BH : Hypergraph S (Set S)}
      (hRest : IsRestrictedSeparation D G η A B AH BH)
      (hMem : (AH,BH) ∈ imageHypergraphTangle f g TN) : (A,B) ∈ Tstar := by
    obtain ⟨⟨AN,BN⟩,hAN,hPair⟩ := hMem
    have hEdges : g '' AN.edgeSet=AH.edgeSet := congrArg (fun p => p.1.edgeSet) hPair
    have hSub : AN.edgeSet ⊆ E(N) := (hTN.isSeparation hAN).left_le.edgeSet_subset
    have hInvAN : η.eMap '' (g '' AN.edgeSet)=AN.edgeSet := hInv.image_image' hSub
    have hPattern : AN.edgeSet=A.edgeSet ∩ E(N) := by
      calc
        AN.edgeSet = η.eMap '' (g '' AN.edgeSet) := hInvAN.symm
        _ = η.eMap '' AH.edgeSet := congrArg (fun X => η.eMap '' X) hEdges
        _ = A.edgeSet ∩ E(N) := by simpa only [hImage] using hRest.2.2.1
    exact hConformal ⟨hSep,hOrd,(AN,BN),hAN,hPattern⟩
  refine ⟨hθ,hTstar,hTD,?_⟩
  intro A B hSep hOrd AH BH hRest
  constructor
  · intro hAB
    have hRestOrd : separationOrder AH BH < θ := (restrictedSeparation_order_le hRest).trans_lt hOrd
    rcases hTD.axiom1 hRest.1 hRestOrd with hMem | hMem
    · exact hMem
    · have hRestBA : IsRestrictedSeparation D G η B A BH AH :=
        ⟨hRest.1.symm,hRest.2.2.2.1,hRest.2.2.2.2,hRest.2.1,hRest.2.2.1⟩
      have hOrdBA : separationOrder B A < θ := by rw [separationOrder_comm]; exact hOrd
      have hBA := hForces hSep.symm hOrdBA hRestBA hMem
      exact (GM10.theorem_2_1_proof hTstar.isTangle hAB hBA).elim
  · intro hMem
    exact hForces hSep hOrd hRest hMem

end GraphMinor.GM16

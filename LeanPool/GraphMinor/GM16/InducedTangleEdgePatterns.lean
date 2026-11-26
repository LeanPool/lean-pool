/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphImageTangle
public import LeanPool.GraphMinor.GM10.Defs2

/-!
# Comparing induced tangles with the same chosen edge map

The original wall minor and the wall minor in the subdivision
have different branch sets but the same chosen edges. A small
side in the subdivision tangle therefore has exactly the same
chosen-edge pattern as a small side of the original wall tangle.
Intersecting its restricted edge set with the chosen edges removes
the intermediate subgraph. This compares the induced tangles in
the last paragraph of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Hypergraph GM10
universe u v w u₁ u₂ u₃ v₁

/-- A separation matching a side induced through the smaller branch
sets also matches the side induced through the original branch sets,
provided that their chosen edge maps are the same. -/
theorem mem_inducedTangle_of_same_edge_pattern
    {α : Type u} {α' : Type u₁} {ν : Type w} {ε : Type v₁} {β : Type v}
    {κ : Type u₂} {κ' : Type u₃} (W : Hypergraph ν ε)
    (G : Hypergraph α β) (N : Hypergraph α' β)
    (f : ν → κ) (f' : ν → κ') (g : ε → β)
    {T : Set (Hypergraph ν ε × Hypergraph ν ε)} {θ : ℕ}
    (hChosen : g '' W.edgeSet ⊆ N.edgeSet)
    {A B : Hypergraph α β} (hSep : G.IsSeparation A B) (hOrd : separationOrder A B < θ)
    {A' B' : Hypergraph α' β}
    (hMem : (A', B') ∈ inducedTangle N (imageHypergraph f' g W) (imageHypergraphTangle f' g T) θ)
    (hEdges : A'.edgeSet = A.edgeSet ∩ N.edgeSet) :
    (A,B) ∈ inducedTangle G (imageHypergraph f g W) (imageHypergraphTangle f g T) θ := by
  obtain ⟨p,hp,hPattern⟩ := hMem.2.2
  obtain ⟨⟨A₀,B₀⟩,h₀,hPair⟩ := hp
  have hAE : g '' A₀.edgeSet = A'.edgeSet ∩ g '' W.edgeSet :=
    (congrArg (fun q => q.1.edgeSet) hPair).trans hPattern
  refine ⟨hSep,hOrd,(imageHypergraph f g A₀,imageHypergraph f g B₀),?_,?_⟩
  · exact ⟨(A₀,B₀),h₀,rfl⟩
  · change g '' A₀.edgeSet = A.edgeSet ∩ g '' W.edgeSet
    rw [hAE,hEdges,inter_assoc,inter_eq_right.mpr hChosen]

/-- Inducing through an intermediate subgraph and the same chosen
edge map gives a subset of the tangle induced directly. -/
theorem inducedTangle_subset_of_same_edge_pattern
    {α : Type u} {α' : Type u₁} {ν : Type w} {ε : Type v₁} {β : Type v}
    {κ : Type u₂} {κ' : Type u₃} (W : Hypergraph ν ε)
    (G : Hypergraph α β) (N : Hypergraph α' β)
    (f : ν → κ) (f' : ν → κ') (g : ε → β)
    (T : Set (Hypergraph ν ε × Hypergraph ν ε)) (θ : ℕ)
    (hChosen : g '' W.edgeSet ⊆ N.edgeSet) :
    inducedTangle G N (inducedTangle N (imageHypergraph f' g W)
      (imageHypergraphTangle f' g T) θ) θ ⊆
      inducedTangle G (imageHypergraph f g W) (imageHypergraphTangle f g T) θ := by
  rintro ⟨A,B⟩ h
  obtain ⟨⟨A',B'⟩,hMem,hEdges⟩ := h.2.2
  exact mem_inducedTangle_of_same_edge_pattern W G N f f' g hChosen h.1 h.2.1 hMem hEdges

end GraphMinor.GM16

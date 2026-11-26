/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM16.HypergraphImage

/-!
# Relabelling the branches of a controlled minor

For the embedded-graph form of XII (4.3), page 249, the branch
hypergraphs must be carried through vertex and edge maps that are
injective on the actual drawing. Subhypergraph inclusion survives
such a relabelling. A skeleton walk maps to a skeleton walk because
its adjacent vertices are distinct actual vertices. Thus connected
nonempty branches stay connected and nonempty.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GM16

/-- Relabelling preserves inclusion when the edge map is injective
on the actual edge set of the larger hypergraph. -/
theorem imageHypergraph_mono_on
    {α β γ δ : Type*} (f : α → γ) (g : β → δ)
    {A H : Hypergraph α β} (hg : InjOn g H.edgeSet) (hAH : A ≤ H) :
    imageHypergraph f g A ≤ imageHypergraph f g H := by
  refine ⟨image_mono hAH.vertexSet_subset, image_mono hAH.edgeSet_subset, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  ext v
  constructor
  · rintro ⟨e₀, v₀, hi, heq, hv⟩
    have he₀ : e₀ = e := hg (H.edge_mem_of_inc hi) (hAH.edgeSet_subset he) heq
    subst e₀
    have hia : A.Inc e v₀ := (Set.ext_iff.mp (hAH.ends_eq e he) v₀).mp hi
    exact ⟨e, v₀, hia, rfl, hv⟩
  · rintro ⟨e₀, v₀, hi, heq, hv⟩
    have hiH : H.Inc e₀ v₀ := (Set.ext_iff.mp (hAH.ends_eq e₀ (A.edge_mem_of_inc hi)) v₀).mpr hi
    exact ⟨e₀, v₀, hiH, heq, hv⟩

/-- Connected branches stay connected after relabelling by a map
injective on their actual vertices. -/
theorem isConnectedSub_imageHypergraph
    {α β γ δ : Type*} (f : α → γ) (g : β → δ)
    {A : Hypergraph α β} (hf : InjOn f A.vertexSet) (hA : IsConnectedSub A) :
    IsConnectedSub (imageHypergraph f g A) := by
  have hwalk : ∀ {x y : α}, A.skeleton.Walk x y →
      (imageHypergraph f g A).skeleton.Reachable (f x) (f y) := by
    intro x y W
    induction W with
    | nil => exact .refl _
    | @cons x y z hxy W ih =>
      obtain ⟨hne, e, hex, hey⟩ := hxy
      have hneq : f x ≠ f y := fun h => hne (hf (A.vertex_mem_of_inc hex)
        (A.vertex_mem_of_inc hey) h)
      have hadj : (imageHypergraph f g A).skeleton.Adj (f x) (f y) :=
        ⟨hneq, g e, ⟨e, x, hex, rfl, rfl⟩, ⟨e, y, hey, rfl, rfl⟩⟩
      exact hadj.reachable.trans ih
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨W⟩ := hA x hx y hy
  exact hwalk W

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphImage
public import LeanPool.GraphMinor.Minor.Model

/-!
# Graph isomorphisms with specified maps

When an isomorphism agrees with given vertex and edge maps, the
hypergraph of its target is the image of the hypergraph of its source.
This identifies the hypergraph of the contracted wall with the
relabelled square grid in XVI (4.2), Claim (1).
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph
universe u v u' v'
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- The image hypergraph associated with the maps of a graph isomorphism. -/
theorem imageHypergraph_of_iso {H : Graph α β} {K : Graph α' β'}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVK : V(K).Finite) (hEK : E(K).Finite)
    (φ : Iso H K) (f : α → α') (g : β → β')
    (hf : ∀ v : V(H), (φ.vertexEquiv v).val = f v.val)
    (hg : ∀ e : E(H), (φ.edgeEquiv e).val = g e.val) :
    imageHypergraph f g (Hypergraph.ofGraph H hVH hEH) = Hypergraph.ofGraph K hVK hEK := by
  apply Hypergraph.ext
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hf ⟨x, hx⟩ ▸ (φ.vertexEquiv ⟨x, hx⟩).property
    · intro hy
      let x := φ.vertexEquiv.symm ⟨y, hy⟩
      refine ⟨x.val, x.property, ?_⟩
      exact (hf x).symm.trans (congrArg Subtype.val (φ.vertexEquiv.apply_symm_apply ⟨y, hy⟩))
  · ext e
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      exact hg ⟨e₀, he₀⟩ ▸ (φ.edgeEquiv ⟨e₀, he₀⟩).property
    · intro he
      let e₀ := φ.edgeEquiv.symm ⟨e, he⟩
      refine ⟨e₀.val, e₀.property, ?_⟩
      exact (hg e₀).symm.trans (congrArg Subtype.val (φ.edgeEquiv.apply_symm_apply ⟨e, he⟩))
  · funext e v
    apply propext
    constructor
    · rintro ⟨e₀, v₀, hi, rfl, rfl⟩
      obtain ⟨w₀, hlink⟩ := hi
      have hmap := (φ.isLink_iff ⟨e₀, hlink.edge_mem⟩ ⟨v₀, hlink.left_mem⟩
        ⟨w₀, hlink.right_mem⟩).mp hlink
      rw [hf ⟨v₀, hlink.left_mem⟩, hf ⟨w₀, hlink.right_mem⟩,
        hg ⟨e₀, hlink.edge_mem⟩] at hmap
      exact ⟨f w₀, hmap⟩
    · rintro ⟨w, hlink⟩
      let e₀ := φ.edgeEquiv.symm ⟨e, hlink.edge_mem⟩
      let v₀ := φ.vertexEquiv.symm ⟨v, hlink.left_mem⟩
      let w₀ := φ.vertexEquiv.symm ⟨w, hlink.right_mem⟩
      have hmap : K.IsLink (φ.edgeEquiv e₀).val (φ.vertexEquiv v₀).val
          (φ.vertexEquiv w₀).val := by
        simpa only [e₀, v₀, w₀, Equiv.apply_symm_apply] using hlink
      have horig := (φ.isLink_iff e₀ v₀ w₀).mpr hmap
      refine ⟨e₀.val, v₀.val, ⟨w₀.val, horig⟩, ?_, ?_⟩
      · exact (hg e₀).symm.trans
          (congrArg Subtype.val (φ.edgeEquiv.apply_symm_apply ⟨e, hlink.edge_mem⟩))
      · exact (hf v₀).symm.trans
          (congrArg Subtype.val (φ.vertexEquiv.apply_symm_apply ⟨v, hlink.left_mem⟩))

end GraphMinor.GM16

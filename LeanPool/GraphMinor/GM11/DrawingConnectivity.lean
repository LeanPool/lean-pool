/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.PaintingRegions
import LeanPool.GraphMinor.GM11.Walks

/-!
# Walks in drawings with preconnected support

The vertices in a preconnected drawing belong to one graph component.
-/

public section

namespace GraphMinor.GM11

open Set Topology Surface

universe u

/-- Vertices of a drawing with preconnected point set are joined by a
graph walk. -/
theorem drawing_walk_of_isPreconnected_U {S : Type u} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} (hU : IsPreconnected D.U) {a b : S} (ha : a ∈ D.V) (hb : b ∈ D.V) :
    Nonempty (GraphWalk D.toGraph a b) := by
  classical
  let R : Set S := {x | Nonempty (GraphWalk D.toGraph a x)}
  have hRV : R ⊆ D.V := by
    rintro x ⟨W⟩
    exact W.mem_vertexSet_of_mem_support W.end_mem_support
  let E₁ : Set (Set S) := {e ∈ D.E | ∃ x ∈ R, x ∈ closure e}
  let E₂ : Set (Set S) := D.E \ E₁
  have hprop : ∀ e ∈ E₁, ∀ x ∈ closure e ∩ D.V, x ∈ R := by
    rintro e ⟨he, u, ⟨W⟩, hue⟩ x hx
    by_cases hux : u = x
    · exact hux ▸ ⟨W⟩
    obtain ⟨p, q, hpq⟩ := D.toGraph.exists_isLink_of_mem_edgeSet he
    have hu : u ∈ ({p, q} : Set S) := hpq.2.2.2 ▸
      ⟨hue, W.mem_vertexSet_of_mem_support W.end_mem_support⟩
    have hx' : x ∈ ({p, q} : Set S) := hpq.2.2.2 ▸ hx
    have hlink : D.toGraph.IsLink e u x := by
      rcases hu with rfl | hu <;> rcases hx' with rfl | hx'
      · exact (hux rfl).elim
      · rw [mem_singleton_iff] at hx'
        exact hx' ▸ hpq
      · rw [mem_singleton_iff] at hu
        exact hu ▸ hpq.symm
      · rw [mem_singleton_iff] at hu hx'
        exact (hux (hu.trans hx'.symm)).elim
    exact ⟨W.append (.cons hlink (.nil hlink.right_mem))⟩
  let C₁ : Set S := R ∪ ⋃ e ∈ E₁, closure e
  let C₂ : Set S := (D.V \ R) ∪ ⋃ e ∈ E₂, closure e
  have hC₁V : ∀ x ∈ C₁, x ∈ D.V → x ∈ R := by
    rintro x (hx | hx) hxV
    · exact hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact hprop e he x ⟨hxe, hxV⟩
  have hC₂V : ∀ x ∈ C₂, x ∈ D.V → x ∉ R := by
    rintro x (hx | hx) _
    · exact hx.2
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      intro hxR
      exact he.2 ⟨he.1, x, hxR, hxe⟩
  have hdis : Disjoint C₁ C₂ := by
    apply disjoint_left.mpr
    intro x hx hy
    by_cases hxV : x ∈ D.V
    · exact hC₂V x hy hxV (hC₁V x hx hxV)
    obtain ⟨e, he, hxe⟩ : ∃ e ∈ E₁, x ∈ closure e :=
      by
        obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp (hx.resolve_left (fun hxR => hxV (hRV hxR)))
        exact ⟨e, he, hxe⟩
    obtain ⟨f, hf, hxf⟩ : ∃ f ∈ E₂, x ∈ closure f :=
      by
        obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp (hy.resolve_left (fun hyV => hxV hyV.1))
        exact ⟨f, hf, hxf⟩
    have hxe' : x ∈ e := by rw [← D.closure_diff_V he.1]; exact ⟨hxe, hxV⟩
    have hxf' : x ∈ f := by rw [← D.closure_diff_V hf.1]; exact ⟨hxf, hxV⟩
    have hef := D.edge_eq_of_mem he.1 hf.1 hxe' hxf'
    exact hf.2 (hef ▸ he)
  have hfin₁ : E₁.Finite := D.finite_edges.subset fun _ h => h.1
  have hfin₂ : E₂.Finite := D.finite_edges.sdiff
  have hclosed₁ : IsClosed C₁ :=
    (D.finite_V.subset hRV).isClosed.union
      (hfin₁.isClosed_biUnion fun _ _ => isClosed_closure)
  have hclosed₂ : IsClosed C₂ :=
    (D.finite_V.subset sdiff_subset).isClosed.union
      (hfin₂.isClosed_biUnion fun _ _ => isClosed_closure)
  have hcover : C₁ ∪ C₂ = D.U := by
    apply subset_antisymm
    · rintro x ((hx | hx) | hx | hx)
      · exact D.V_subset_U (hRV hx)
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact D.closure_subset_U he.1 hxe
      · exact D.V_subset_U hx.1
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact D.closure_subset_U he.1 hxe
    · intro x hx
      rw [D.U_eq] at hx
      rcases hx with hx | hx
      · by_cases hxR : x ∈ R
        · exact Or.inl (Or.inl hxR)
        · exact Or.inr (Or.inl ⟨hx, hxR⟩)
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        by_cases he₁ : e ∈ E₁
        · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, he₁, hxe⟩))
        · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, he₁⟩, hxe⟩))
  by_contra hn
  have haPart : (D.U ∩ C₁).Nonempty := ⟨a,D.V_subset_U ha,Or.inl ⟨.nil ha⟩⟩
  have hbPart : (D.U ∩ C₂).Nonempty := ⟨b,D.V_subset_U hb,Or.inl ⟨hb,hn⟩⟩
  obtain ⟨x,_,hx₁,hx₂⟩ := (isPreconnected_closed_iff.mp hU) C₁ C₂ hclosed₁ hclosed₂
    hcover.ge haPart hbPart
  exact (disjoint_left.mp hdis) hx₁ hx₂

end GraphMinor.GM11

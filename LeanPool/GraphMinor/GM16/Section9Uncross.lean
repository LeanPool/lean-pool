/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Hypergraph.Basic
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Moving a separator into the annulus

The planar Menger argument of XVI (8.1), Claim (10), starts with a
separation between the inner and outer boundary vertices. Join its
inner side to the whole inner disc, then intersect it with the outer
disc. No new separator vertex appears: each boundary already lies
on the required side of the original separation.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.GM10
universe u v

/-- The uncrossing step that puts a boundary separator in the annulus
in XVI (8.1), Claim (10). It preserves every inner edge and adds no
separator vertex. -/
theorem uncross_annular_separation {α : Type u} {β : Type v}
    {G A B C D E F : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hCD : G.IsSeparation C D) (hEF : G.IsSeparation E F)
    (hCE : C.edgeSet ⊆ E.edgeSet) (hCF : Disjoint C.vertexSet F.vertexSet)
    (hInner : C.vertexSet ∩ D.vertexSet ⊆ A.vertexSet)
    (hOuter : E.vertexSet ∩ F.vertexSet ⊆ B.vertexSet) :
    G.IsSeparation ((A ∪ C) ∩ E) ((B ∩ D) ∪ F) ∧
      (((A ∪ C) ∩ E).vertexSet ∩ ((B ∩ D) ∪ F).vertexSet ⊆ A.vertexSet ∩ B.vertexSet) ∧
      C.edgeSet ⊆ ((A ∪ C) ∩ E).edgeSet ∧ ((A ∪ C) ∩ E) ≤ E := by
  have h₁ := hAB.union_inter hCD
  refine ⟨(h₁.symm.union_inter hEF.symm).symm, ?_, ?_,
    inter_le_right h₁.left_le hEF.left_le⟩
  · rintro x ⟨⟨hxAC, hxE⟩, hxBDF⟩
    rcases hxBDF with ⟨hxB, hxD⟩ | hxF
    · refine ⟨?_, hxB⟩
      exact hxAC.elim id (fun hxC => hInner ⟨hxC, hxD⟩)
    · refine ⟨?_, hOuter ⟨hxE, hxF⟩⟩
      exact hxAC.elim id (fun hxC => False.elim (hCF.notMem_of_mem_left hxC hxF))
  · intro e he
    exact ⟨Or.inr he, hCE he⟩

end GraphMinor.GM16

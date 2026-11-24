/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Gluing the removed disc to an outside bigon

For maximality in XII (7.2), page 260, a disc between the deleted
spoke and a new spoke can be joined to the removed disc. Their
intersection is just that spoke. The joined disc is bounded by the
retained spoke and the new spoke. The side lemmas here also locate
the intersection of two discs whose open interiors are disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

variable {S : Type*} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- If the open interior of one disc misses the other, any common
point lies on both boundaries. -/
theorem disc_inter_subset_boundaries (hS : IsClosedSurface S)
    {D Q : Set S} (hD : IsClosedDisc D) (hQ : IsClosedDisc Q)
    (hdis : Disjoint (discInt D) Q) : D ∩ Q ⊆ discBd D ∩ discBd Q := by
  rintro x ⟨hxD, hxQ⟩
  have hxDb : x ∈ discBd D := by
    by_contra hn
    exact disjoint_left.mp hdis ⟨hxD, hn⟩ hxQ
  have hxQb : x ∈ discBd Q := by
    by_contra hn
    have hxcl : x ∈ closure (discInt D) := hD.subset_closure_discInt hxD
    have hopen : IsOpen (discInt Q) := hQ.isOpen_discInt fun y => (hS.2.2 y).isManifoldPoint
    obtain ⟨y, hyQ, hyD⟩ := mem_closure_iff.mp hxcl _ hopen ⟨hxQ, hn⟩
    exact disjoint_left.mp hdis hyD hyQ.1
  exact ⟨hxDb, hxQb⟩

/-- If a disc's open interior misses another disc's boundary, and
one of its boundary points is outside that disc, the open interior
lies wholly outside. -/
theorem discInt_disjoint_of_boundary_point_outside (hS : IsClosedSurface S)
    {D Q : Set S} (hD : IsClosedDisc D) (hQ : IsClosedDisc Q)
    (hdis : Disjoint (discInt Q) (discBd D))
    {z : S} (hz : z ∈ Q) (hzD : z ∉ D) : Disjoint (discInt Q) D := by
  rcases hD.side (fun y => (hS.2.2 y).isManifoldPoint) hQ.isPreconnected_discInt hdis with hin |
    hout
  · have hQD : Q ⊆ D := hQ.subset_closure_discInt.trans
      (closure_minimal (hin.trans (discInt_subset D)) hD.isClosed)
    exact (hzD (hQD hz)).elim
  · exact hout

/-- Gluing along the deleted spoke replaces it in the boundary by
the retained spoke. This is the disc union used for maximality in
XII (7.2), page 260. -/
theorem glue_bigons_along_spoke {D Q E F L : Set S} {v u : S}
    (hD : IsClosedDisc D) (hQ : IsClosedDisc Q) (hF : IsLineWithEnds F v u)
    (hinter : D ∩ Q = F) (hbdD : discBd D = E ∪ F) (hbdQ : discBd Q = F ∪ L)
    (hEF : E ∩ F ⊆ {v, u}) (hLF : L ∩ F ⊆ {v, u}) (hends : ({v, u} : Set S) ⊆ E) :
    IsClosedDisc (D ∪ Q) ∧ discBd (D ∪ Q) = E ∪ L := by
  have hFD : F ⊆ discBd D := hbdD.symm ▸ subset_union_right
  have hFQ : F ⊆ discBd Q := hbdQ.symm ▸ subset_union_left
  obtain ⟨hUnion, hbd⟩ := disc_union D Q F v u hD hQ hF hinter hFD hFQ
  refine ⟨hUnion, hbd.trans ?_⟩
  rw [hbdD, hbdQ]
  ext x
  constructor
  · rintro ⟨(hxE | hxF) | (hxF | hxL), hxnot⟩
    · exact Or.inl hxE
    · exact Or.inl (hends (by by_contra hn; exact hxnot ⟨hxF, hn⟩))
    · exact Or.inl (hends (by by_contra hn; exact hxnot ⟨hxF, hn⟩))
    · exact Or.inr hxL
  · rintro (hxE | hxL)
    · exact ⟨Or.inl (Or.inl hxE), fun hx => hx.2 (hEF ⟨hxE, hx.1⟩)⟩
    · exact ⟨Or.inr (Or.inr hxL), fun hx => hx.2 (hLF ⟨hxL, hx.1⟩)⟩

end GraphMinor.GM12

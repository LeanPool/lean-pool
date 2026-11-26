/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section73TieBoundary
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.Disc

/-!
# Attachment points of disc pieces

Two disc pieces of a tie meet, if at all, in a single point.
That point belongs to the boundary of both discs. A connected
set with more than one point has no isolated point, so neither
disc can meet the interior of the other at their sole common
point. Once their boundary circuits lie in a drawing, their
common point must be a vertex: an interior point of a common
edge would force more than that point into their intersection.
These facts let the tie walk in XII (7.3), page 262, concatenate
the two boundary walks at their attachment.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem preconnected_subset_closure_punctured
    {S : Type*} [TopologicalSpace S] [T1Space S] {A : Set S} {p : S}
    (hA : IsPreconnected A) (hne : ¬ A ⊆ {p}) : A ⊆ closure (A \ {p}) := by
  by_cases hp : p ∈ closure (A \ {p})
  · intro x hx
    by_cases hxp : x = p
    · exact hxp.symm ▸ hp
    · exact subset_closure ⟨hx, hxp⟩
  · have hcov : A ⊆ closure (A \ {p}) ∪ {p} := by
      intro x hx
      by_cases hxp : x = p
      · exact Or.inr hxp
      · exact Or.inl (subset_closure ⟨hx, hxp⟩)
    have hdis : closure (A \ {p}) ∩ ({p} : Set S) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, rfl⟩
      exact hp hx
    exact (isPreconnected_iff_subset_of_disjoint_closed.mp hA _ _ isClosed_closure
      isClosed_singleton hcov (by rw [hdis, inter_empty])).resolve_right hne

/-- A disc has no isolated point, including at its boundary. -/
theorem disc_subset_closure_punctured
    {S : Type*} [TopologicalSpace S] [T2Space S] {D : Set S}
    (hD : IsClosedDisc D) (p : S) : D ⊆ closure (D \ {p}) := by
  apply preconnected_subset_closure_punctured hD.isPathConnected.isConnected.isPreconnected
  intro hsub
  exact ((infinite_of_isOArc hD.isOArc_discBd).mono ((Surface.discBd_subset D).trans hsub)
    (finite_singleton p)).elim

/-- The sole common point of two closed discs is on both boundaries. -/
theorem disc_attachment_mem_boundaries
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {D E : Set S} {p : S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : D ∩ E = {p}) :
    p ∈ discBd D ∧ p ∈ discBd E := by
  have hfirst : ∀ {A B : Set S}, IsClosedDisc A → IsClosedDisc B →
      A ∩ B = {p} → p ∈ discBd A := by
    intro A B hA hB hAB
    have hpAB : p ∈ A ∩ B := hAB.symm ▸ mem_singleton p
    rw [← IsClosedDisc.frontier_eq_discBd hS hA]
    refine ⟨subset_closure hpAB.1, ?_⟩
    intro hpint
    have hpcl := disc_subset_closure_punctured hB p hpAB.2
    obtain ⟨x, hxint, hxB⟩ := mem_closure_iff.mp hpcl _ isOpen_interior hpint
    exact hxB.2 (hAB ▸ (⟨interior_subset hxint, hxB.1⟩ : x ∈ A ∩ B))
  exact ⟨hfirst hD hE hDE, hfirst hE hD (inter_comm D E ▸ hDE)⟩

/-- A point at which two subdrawings meet alone is an ambient
vertex. Otherwise its ambient edge lies in both subdrawings. -/
theorem mem_vertices_of_subdrawing_inter_singleton
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {K C D : Drawing S} {p : S}
    (hCK : C.IsSubdrawing K) (hDK : D.IsSubdrawing K)
    (hpC : p ∈ C.U) (hpD : p ∈ D.U) (hCD : C.U ∩ D.U ⊆ {p}) : p ∈ K.V := by
  by_contra hpV
  obtain ⟨e, heC, hpe⟩ := C.exists_edge_of_mem hpC (fun h => hpV (hCK.1 h))
  obtain ⟨f, hfD, hpf⟩ := D.exists_edge_of_mem hpD (fun h => hpV (hDK.1 h))
  have hef : e = f := K.edge_eq_of_mem (hCK.2 heC) (hDK.2 hfD) hpe hpf
  have hesub : e ⊆ {p} := by
    intro x hx
    apply hCD
    exact ⟨(heC.2.1 hx).1, (hfD.2.1 (hef ▸ hx)).1⟩
  have hcl : closure e ⊆ {p} := closure_minimal hesub isClosed_singleton
  rcases K.edge_cond e (hCK.2 heC) with ⟨a, b, _, hcap, _⟩ | ⟨a, hcap, _⟩
  · have ha : a ∈ closure e ∩ K.V := hcap.symm ▸ (Or.inl rfl : a ∈ ({a, b} : Set S))
    exact hpV ((hcl ha.1) ▸ ha.2)
  · have ha : a ∈ closure e ∩ K.V := hcap.symm ▸ mem_singleton a
    exact hpV ((hcl ha.1) ▸ ha.2)

end GraphMinor.GM12

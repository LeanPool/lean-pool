/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section74EdgeDeletion
import LeanPool.GraphMinor.GM11.Section4c

/-!
# The other regions in an edge gluing

The finite gluing in XII (7.4), pages 262--263, removes edges
between distinct corner regions. The merged region was identified
in `Section74EdgeDeletion`. Every new region other than this
one is an old region, and each old region other than the two
merged regions survives. These facts allow the gluing to continue
through the cyclic list of corners.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A region after edge deletion either meets the edge, or is
an old region of the drawing. -/
theorem region_deleteEdge_old_of_disjoint
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {e r : Set S}
    (he : e ∈ K.E) (hr : r ∈ (K.deleteEdge e).R) (hdis : Disjoint r e) : r ∈ K.R := by
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxK : x ∉ K.U := by
    intro hx
    have hxn := region_subset hr hxr
    rw [deleteEdge_U K he] at hxn
    exact hxn ⟨hx, disjoint_left.mp hdis hxr⟩
  obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem hxK
  have hrs : r ⊆ s := subset_region hs (region_isPreconnected hr)
    (disjoint_left.mpr fun y hyr hyK => by
      have hyN := region_subset hr hyr
      rw [deleteEdge_U K he] at hyN
      exact hyN ⟨hyK, disjoint_left.mp hdis hyr⟩) hxr hxs
  have hsr : s ⊆ r := subset_region hr (region_isPreconnected hs)
    (disjoint_left.mpr fun y hys hyN => region_subset hs hys
      ((deleteEdge_isSubdrawing K e).U_subset hyN)) hxs hxr
  exact (Subset.antisymm hrs hsr).symm ▸ hs

/-- Every old region other than the two being glued survives
the edge deletion. -/
theorem region_deleteEdge_of_ne_merged_pair
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {e p q r : Set S}
    (he : e ∈ K.E) (hp : p ∈ K.R) (hq : q ∈ K.R) (hpq : p ≠ q)
    (hdp : IsOpenDisc p) (hdq : IsOpenDisc q)
    (hep : e ⊆ closure p) (heq : e ⊆ closure q)
    (hr : r ∈ K.R) (hrp : r ≠ p) (hrq : r ≠ q) : r ∈ (K.deleteEdge e).R := by
  obtain ⟨hmerge, _⟩ := merged_region_deleteEdge hS he hp hq hpq hdp hdq hep heq
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxK : x ∉ K.U := region_subset hr hxr
  obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem
    (fun h => hxK ((deleteEdge_isSubdrawing K e).U_subset h))
  have hxNotMerge : x ∉ p ∪ q ∪ e := by
    rintro ((hxp | hxq) | hxe)
    · exact hrp (region_eq_of_mem hr hp hxr hxp)
    · exact hrq (region_eq_of_mem hr hq hxr hxq)
    · exact hxK (he.2.1 hxe).1
  have hsDis : Disjoint s e := by
    apply disjoint_left.mpr
    intro y hys hye
    have hsEq : s = p ∪ q ∪ e := region_eq_of_mem hs hmerge hys (Or.inr hye)
    exact hxNotMerge (hsEq ▸ hxs)
  have hsOld := region_deleteEdge_old_of_disjoint he hs hsDis
  have hsr : s = r := region_eq_of_mem hsOld hr hxs hxr
  exact hsr ▸ hs

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# Two discs meeting once meet on both boundaries

For XII (3.1)(iii) in the proof of (3.2), page 246, the two boundary
circles need a common base point. If a single intersection point
were interior to one disc, its intersection with the other disc
would be a relatively open singleton. That other disc is connected
and has another point, so this singleton cannot also be relatively
closed. Thus the point lies on both boundaries.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem mem_discBd_of_singleton_intersection
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E) {p : S}
    (hcap : D ∩ E = {p}) (hpD : p ∈ D) (hpE : p ∈ E) : p ∈ discBd D := by
  by_contra hpB
  have hpI : p ∈ discInt D := ⟨hpD, hpB⟩
  have hEinf : E.Infinite := (infinite_of_isOArc hE.isOArc_discBd).mono (Surface.discBd_subset E)
  obtain ⟨y, hyE, hyp⟩ := hEinf.exists_notMem_finite (finite_singleton p)
  have hcover : E ⊆ discInt D ∪ ({p} : Set S)ᶜ := by
    intro x _
    by_cases hxp : x = p
    · exact Or.inl (hxp.symm ▸ hpI)
    · exact Or.inr hxp
  have hopen : IsOpen (discInt D) := hD.isOpen_discInt (fun x => (hS.2.2 x).isManifoldPoint)
  obtain ⟨x, hxE, hxI, hxp⟩ := hE.isPathConnected.isConnected.isPreconnected
    (discInt D) ({p} : Set S)ᶜ hopen isClosed_singleton.isOpen_compl hcover
    ⟨p, hpE, hpI⟩ ⟨y, hyE, hyp⟩
  exact hxp (hcap.subset ⟨hxI.1, hxE⟩)

/-- Two closed discs with singleton intersection have exactly the
same singleton as the intersection of their boundary circles. -/
theorem disc_boundaries_inter_of_singleton_intersection
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E) {p : S}
    (hcap : D ∩ E = {p}) :
    p ∈ discBd D ∩ discBd E ∧ discBd D ∩ discBd E = {p} := by
  have hp : p ∈ D ∩ E := hcap.symm.subset (mem_singleton p)
  have hpD := mem_discBd_of_singleton_intersection hS hD hE hcap hp.1 hp.2
  have hpE := mem_discBd_of_singleton_intersection hS hE hD ((inter_comm E D).trans hcap) hp.2 hp.1
  refine ⟨⟨hpD, hpE⟩, Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact hcap.subset ⟨Surface.discBd_subset D hx.1, Surface.discBd_subset E hx.2⟩
  · intro x hx
    have hxp : x = p := hx
    subst x
    exact ⟨hpD, hpE⟩

end GraphMinor.GM12

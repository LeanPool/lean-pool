/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Regions
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The region meeting a prescribed disc

In XII (3.2), pages 246--247, the drawing meets each prescribed
disc only at boundary vertices. The disc interior is connected and
misses the drawing, so it lies in one region. The whole disc lies
in that region's closure. Any other region, being open and disjoint
from the first, misses the whole disc. This justifies the region
chosen for each prescription and the auxiliary-disc placement.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A closed disc meeting the drawing only in its boundary vertices
lies in the closure of one region, and no other region meets it. -/
theorem exists_unique_region_meeting_disc
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {D : Set S} (hD : IsClosedDisc D)
    (havoid : Γ.U ∩ D = Γ.V ∩ discBd D) :
    ∃ r ∈ Γ.R, discInt D ⊆ r ∧ D ⊆ closure r ∧
      ∀ s ∈ Γ.R, (s ∩ D).Nonempty → s = r := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hIU : Disjoint (discInt D) Γ.U := Set.disjoint_left.mpr fun x hx hxU =>
    hx.2 (havoid.subset ⟨hxU, hx.1⟩).2
  obtain ⟨x, hx⟩ := hD.nonempty_discInt
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (Set.disjoint_left.mp hIU hx)
  have hIr : discInt D ⊆ r := subset_region hr hD.isPreconnected_discInt hIU hx hxr
  have hDr : D ⊆ closure r := hD.subset_closure_discInt.trans (closure_mono hIr)
  refine ⟨r, hr, hIr, hDr, ?_⟩
  intro s hs hmeet
  obtain ⟨y, hys, hyD⟩ := hmeet
  obtain ⟨z, hzs, hzr⟩ := mem_closure_iff.mp (hDr hyD) s (region_isOpen hs) hys
  exact region_eq_of_mem hs hr hzs hzr

/-- Distinct regions avoid a disc whose interior lies in the first
region, as used in the auxiliary-disc step of XII (3.2), page 247. -/
theorem region_disjoint_disc_of_ne
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {D r s : Set S} (hD : IsClosedDisc D)
    (havoid : Γ.U ∩ D = Γ.V ∩ discBd D) (hr : r ∈ Γ.R) (hs : s ∈ Γ.R)
    (hrD : (r ∩ D).Nonempty) (hne : s ≠ r) : Disjoint s D := by
  obtain ⟨r', _, _, _, huniq⟩ := exists_unique_region_meeting_disc hS hD havoid
  have hrr' := huniq r hr hrD
  exact Set.disjoint_left.mpr fun x hxs hxD => hne ((huniq s hs ⟨x, hxs, hxD⟩).trans hrr'.symm)

end GraphMinor.GM12

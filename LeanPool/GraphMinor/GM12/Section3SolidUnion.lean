/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section3SolidConnections
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Solid unions and lines

The schismatic shapes in the Section 8 argument used by XII (3.1),
page 245, are finite unions of circles and lines. A line is solid by
its interval chart. In a compact Hausdorff space a union of two solid
sets is solid: the map from their disjoint sum onto the union is a
compact quotient, so local path-connectedness passes to the union.
The subspace criterion converts this back to the paper's local
arc-connectedness condition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A line is solid. Its interval chart supplies both compactness and
local path-connectedness. -/
theorem isSolid_line
    {S : Type*} [TopologicalSpace S] [T2Space S] {L : Set S} (hL : IsLine L) :
    IsSolid L := by
  obtain ⟨φ⟩ := hL
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace L := φ.locallyPathConnectedSpace
  let : CompactSpace L := φ.compactSpace
  have hc : IsCompact L := isCompact_iff_compactSpace.mpr inferInstance
  exact ⟨isLocallyArcConnected_of_locallyPathConnectedSpace, hc.isClosed⟩

/-- A union of two solid sets in a compact Hausdorff space is solid.
This supplies the finite-union step for schismatic shapes. -/
theorem isSolid_union
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {X Y : Set S} (hX : IsSolid X) (hY : IsSolid Y) : IsSolid (X ∪ Y) := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX.2.isCompact
  let : CompactSpace Y := isCompact_iff_compactSpace.mp hY.2.isCompact
  let : LocallyPathConnectedSpace X := locallyPathConnectedSpace_of_isLocallyArcConnected hX.1
  let : LocallyPathConnectedSpace Y := locallyPathConnectedSpace_of_isLocallyArcConnected hY.1
  let f : X ⊕ Y → ↥(X ∪ Y) := Sum.elim
    (fun x => ⟨x.val, Or.inl x.property⟩) (fun y => ⟨y.val, Or.inr y.property⟩)
  have hfc : Continuous f := by
    apply continuous_sum_dom.mpr
    constructor <;> exact continuous_subtype_val.subtype_mk _
  have hfs : Function.Surjective f := by
    intro z
    rcases z.property with hz | hz
    · exact ⟨.inl ⟨z.val, hz⟩, rfl⟩
    · exact ⟨.inr ⟨z.val, hz⟩, rfl⟩
  have hquot := hfc.isClosedMap.isQuotientMap hfc hfs
  let : LocallyPathConnectedSpace ↥(X ∪ Y) := hquot.locallyPathConnectedSpace
  exact ⟨isLocallyArcConnected_of_locallyPathConnectedSpace, hX.2.union hY.2⟩

end GraphMinor.GM12

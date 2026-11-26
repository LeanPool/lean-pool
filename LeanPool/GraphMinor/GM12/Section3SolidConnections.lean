/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import Mathlib.Topology.Connected.LocallyPathConnected
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Connections inside a connected solid set

The Section 8 argument of VII used in XII (3.1), page 245, joins its
selected circles inside the solid set. The paper's local
arc-connectedness definition gives path-connected neighbourhoods in
the subspace. Connectedness then gives paths between all its points,
and the arc-in-a-path theorem removes repeated parts of those paths.
-/

public section

namespace GraphMinor.GM12

open Set Topology Filter Surface GM11

/-- A nonempty arc-connected set is path-connected by parametrizing
the line between each pair of distinct points. -/
theorem isPathConnected_of_isArcConnected
    {S : Type*} [TopologicalSpace S] {X : Set S}
    (hX : IsArcConnected X) (hne : X.Nonempty) : IsPathConnected X := by
  apply isPathConnected_iff.mpr
  refine ⟨hne, ?_⟩
  intro a ha b hb
  by_cases hab : a = b
  · rw [hab]
    exact JoinedIn.refl hb
  · obtain ⟨L, hLX, φ, hφ0, hφ1⟩ := hX a ha b hb hab
    let p : Path a b := {
      toFun := fun t => (φ t).val
      continuous_toFun := continuous_subtype_val.comp φ.continuous
      source' := hφ0
      target' := hφ1 }
    exact ⟨p, fun t => hLX (φ t).property⟩

/-- The paper's local arc-connectedness condition gives a locally
path-connected subspace. The neighbourhoods are pulled back from the
ambient open sets in its definition. -/
theorem locallyPathConnectedSpace_of_isLocallyArcConnected
    {S : Type*} [TopologicalSpace S] {X : Set S} (hX : IsLocallyArcConnected X) :
    LocallyPathConnectedSpace X := by
  constructor
  intro x
  rw [hasBasis_self]
  intro O hO
  obtain ⟨U, hUO, hU, hxU⟩ := mem_nhds_iff.mp hO
  obtain ⟨A, hA, hpre⟩ := IsInducing.subtypeVal.isOpen_iff.mp hU
  have hxA : x.val ∈ A := by
    change x ∈ (Subtype.val : X → S) ⁻¹' A
    rw [hpre]
    exact hxU
  obtain ⟨A', hA'sub, hxA', hA', hArc⟩ := hX x.val x.property A hA hxA
  have hpath : IsPathConnected ((Subtype.val : X → S) ⁻¹' A') := by
    apply IsInducing.subtypeVal.isPathConnected_iff.mpr
    rw [Subtype.image_preimage_coe]
    exact isPathConnected_of_isArcConnected hArc ⟨x.val, x.property, hxA'⟩
  refine ⟨Subtype.val ⁻¹' A', (hA'.preimage continuous_subtype_val).mem_nhds hxA', hpath, ?_⟩
  intro y hy
  apply hUO
  rw [← hpre]
  exact hA'sub hy

/-- A path-connected subset of a Hausdorff space is arc-connected,
by taking an arc inside each joining path. -/
theorem isArcConnected_of_isPathConnected
    {S : Type*} [TopologicalSpace S] [T2Space S] {X : Set S}
    (hpath : IsPathConnected X) : IsArcConnected X := by
  intro a ha b hb hab
  obtain ⟨p, hp⟩ := hpath.joinedIn a ha b hb
  obtain ⟨e, hec, hei, he0, he1, heSub⟩ := exists_arc_of_path p.continuous
    (by rw [p.source, p.target]; exact hab)
  have hline := GM11.isLine_range hec hei
  rw [he0, he1, p.source, p.target] at hline
  refine ⟨range e, ?_, hline⟩
  apply heSub.trans
  rintro x ⟨t, rfl⟩
  exact hp t

/-- A connected locally arc-connected set in a Hausdorff space is
arc-connected. This supplies the joining lines in the schismatic
argument used by XII (3.1), page 245. -/
theorem isArcConnected_of_isConnected_isLocallyArcConnected
    {S : Type*} [TopologicalSpace S] [T2Space S] {X : Set S}
    (hconn : IsConnected X) (hloc : IsLocallyArcConnected X) : IsArcConnected X := by
  let : LocallyPathConnectedSpace X := locallyPathConnectedSpace_of_isLocallyArcConnected hloc
  let : ConnectedSpace X := Subtype.connectedSpace hconn
  let : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  have hpath : IsPathConnected X := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  exact isArcConnected_of_isPathConnected hpath

/-- Local path-connectedness of a subspace gives the paper's ambient
local arc-connectedness condition in a Hausdorff space. -/
theorem isLocallyArcConnected_of_locallyPathConnectedSpace
    {S : Type*} [TopologicalSpace S] [T2Space S] {X : Set S}
    [LocallyPathConnectedSpace X] : IsLocallyArcConnected X := by
  intro x hx A hA hxA
  let y : X := ⟨x, hx⟩
  have hU : IsOpen ((Subtype.val : X → S) ⁻¹' A) := hA.preimage continuous_subtype_val
  obtain ⟨W, ⟨hW, hyW, hpath⟩, hWU⟩ :=
    (isOpen_isPathConnected_basis y).mem_iff.mp (hU.mem_nhds hxA)
  obtain ⟨B, hB, hpre⟩ := IsInducing.subtypeVal.isOpen_iff.mp hW
  have hxB : x ∈ B := by
    change y ∈ (Subtype.val : X → S) ⁻¹' B
    rw [hpre]
    exact hyW
  refine ⟨B ∩ A, inter_subset_right, ⟨hxB, hxA⟩, hB.inter hA, ?_⟩
  have himage : (Subtype.val : X → S) '' W = X ∩ (B ∩ A) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwB : w.val ∈ B := by
        change w ∈ (Subtype.val : X → S) ⁻¹' B
        rw [hpre]
        exact hw
      exact ⟨w.property, hwB, hWU hw⟩
    · rintro ⟨hzX, hzB, hzA⟩
      refine ⟨⟨z, hzX⟩, ?_, rfl⟩
      rw [← hpre]
      exact hzB
  rw [← himage]
  exact isArcConnected_of_isPathConnected (hpath.image continuous_subtype_val)

end GraphMinor.GM12

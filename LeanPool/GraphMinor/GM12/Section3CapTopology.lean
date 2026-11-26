/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.Surface.PasteDisc

/-!
# Connectedness and the added interior of a cap

The planar criterion used in the Section 8 argument of VII applies
inside a connected cap. Adding a disc to a connected surface preserves
connectedness because the disc meets its cuff. The added disc interior
is outside the original surface, so any subset of the original surface
has proper image in the cap.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

universe u

/-- The proved disc-pasting theorem supplies a cap of every cuff. -/
theorem exists_cappedCuff
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S) {C : Set S} (hC : IsCuff C) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (j : S → T) (D : Set T),
      GM07.IsCappedCuff C T j D := by
  obtain ⟨T, tT, j, D, hT, hj, hD, hcover, hinter, hbd, _⟩ := paste_disc S C hS hC
  exact ⟨T, tT, j, D, hC, hT, hj.isEmbedding, hD, hbd, hcover, hinter⟩

/-- Capping a cuff of a connected surface leaves the surface connected. -/
theorem cappedCuff_connectedSpace
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [ConnectedSpace S]
    {C : Set S} {j : S → T} {D : Set T} (hcap : GM07.IsCappedCuff C T j D) :
    ConnectedSpace T := by
  have hC : C.Nonempty := by
    obtain ⟨x, hx, heq⟩ := hcap.cuff
    exact ⟨x, heq ▸ mem_connectedComponentIn hx⟩
  obtain ⟨x, hxC⟩ := hC
  have hxD : j x ∈ D := by
    apply discBd_subset D
    rw [hcap.discBd_eq]
    exact mem_image_of_mem j hxC
  have hconn : IsConnected (range j ∪ D) :=
    (isConnected_range hcap.isEmbedding.continuous).union
      ⟨j x, mem_range_self x, hxD⟩ hcap.isClosedDisc.isPathConnected.isConnected
  rw [hcap.union_eq] at hconn
  exact connectedSpace_iff_univ.mpr hconn

/-- The original surface omits the interior of the disc added in a cap. -/
theorem cappedCuff_range_ne_univ
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    {C : Set S} {j : S → T} {D : Set T} (hcap : GM07.IsCappedCuff C T j D) :
    range j ≠ univ := by
  intro heq
  obtain ⟨x, hx⟩ := hcap.isClosedDisc.nonempty_discInt
  have hxR : x ∈ range j := heq.symm ▸ mem_univ x
  have hxB : x ∈ range j ∩ D := ⟨hxR, hx.1⟩
  rw [hcap.inter_eq, ← hcap.discBd_eq] at hxB
  exact hx.2 hxB

/-- Compactness makes the inclusion into a cap a closed embedding. -/
theorem cappedCuff_isClosedEmbedding
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) {C : Set S} {j : S → T} {D : Set T}
    (hcap : GM07.IsCappedCuff C T j D) : IsClosedEmbedding j := by
  let : CompactSpace S := hS.1
  let : T2Space T := hcap.isSurface.2.1
  exact hcap.isEmbedding.continuous.isClosedEmbedding hcap.isEmbedding.injective

end GraphMinor.GM12

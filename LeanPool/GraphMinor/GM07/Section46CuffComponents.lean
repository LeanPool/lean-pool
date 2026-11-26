/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.ForestPeel
import LeanPool.GraphMinor.GM07.CutConnected
import LeanPool.GraphMinor.GM07.Section46BoundaryComponents

/-!
# Cuffs after cutting correspond to components before cutting

In VII (4.6), page 226, the cuffs of `Σ′` correspond to the components
of `U(L) ∪ bd(Σ)`. The inverse image of each such component is connected:
this is the non-separation property of a forest. Connectedness in both
directions then identifies each boundary component with that inverse
image. This gives the correspondence and its cardinal equality.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- A boundary component after cutting is the inverse image of the
corresponding component of `U(L) ∪ bd(Σ)`, in VII (4.6), page 226. -/
theorem cut_boundary_component_preimage (hS : IsSurface S) {L : Drawing S}
    {θ : S' → S} (hcut : IsCutAlongGraph L S' θ) (hNo : NoArcs L)
    {x : S'} (hx : x ∈ bd S') :
    connectedComponentIn (bd S') x = θ ⁻¹' connectedComponentIn (L.U ∪ bd S) (θ x) := by
  have : T2Space S := hS.2.1
  have : T2Space S' := hcut.isSurface.2.1
  let B := L.U ∪ bd S
  have hBd : θ ⁻¹' B = bd S' := by
    calc
      θ ⁻¹' B = θ ⁻¹' (bd S ∪ L.U) := congrArg (fun A => θ ⁻¹' A) (union_comm L.U (bd S))
      _ = bd S' := hcut.preimage_bd_union_U
  have hxB : θ x ∈ B := by change x ∈ θ ⁻¹' B; rw [hBd]; exact hx
  let C := connectedComponentIn B (θ x)
  have hCmem : C ∈ componentsIn B := ⟨θ x, hxB, rfl⟩
  have hCsub : C ⊆ B := connectedComponentIn_subset _ _
  obtain ⟨_, hclosed⟩ := boundary_components_finite_closed hS L
  have hCc := (hclosed C hCmem).1
  have hCrest := (hclosed C hCmem).2
  have hrest : IsClosed (L.U \ C) := by
    have heq : L.U \ C = L.U ∩ (B \ C) := by
      ext y
      constructor
      · rintro ⟨hy, hyC⟩; exact ⟨hy, .inl hy, hyC⟩
      · rintro ⟨hy, _, hyC⟩; exact ⟨hy, hyC⟩
    rw [heq]
    exact L.isClosed_U.inter hCrest
  have hpre : IsPreconnected (θ ⁻¹' C) :=
    isPreconnected_preimage_tree hS hcut hNo isPreconnected_connectedComponentIn hCc hrest
  have hprebd : θ ⁻¹' C ⊆ bd S' := by rw [← hBd]; exact preimage_mono hCsub
  have hxC : x ∈ θ ⁻¹' C := mem_connectedComponentIn hxB
  apply Subset.antisymm
  · have himage : IsPreconnected (θ '' connectedComponentIn (bd S') x) :=
      isPreconnected_connectedComponentIn.image θ hcut.quotientMap.continuous.continuousOn
    have hsub : θ '' connectedComponentIn (bd S') x ⊆ B := by
      rintro y ⟨z, hz, rfl⟩
      change z ∈ θ ⁻¹' B
      rw [hBd]
      exact connectedComponentIn_subset _ _ hz
    have htoC := himage.subset_connectedComponentIn
      (mem_image_of_mem θ (mem_connectedComponentIn hx)) hsub
    intro y hy
    exact htoC (mem_image_of_mem θ hy)
  · exact hpre.subset_connectedComponentIn hxC hprebd

/-- The cuff/component correspondence of VII (4.6), page 226, expressed
by inverse images under the associated cut map. -/
theorem cuffs_eq_preimages_boundary_components (hS : IsSurface S) {L : Drawing S}
    {θ : S' → S} (hcut : IsCutAlongGraph L S' θ) (hNo : NoArcs L) :
    cuffs S' = (fun C => θ ⁻¹' C) '' componentsIn (L.U ∪ bd S) := by
  apply Subset.antisymm
  · rintro C ⟨x, hx, rfl⟩
    have hxB : θ x ∈ L.U ∪ bd S := by
      have hx' : θ x ∈ bd S ∪ L.U := by
        change x ∈ θ ⁻¹' (bd S ∪ L.U)
        rwa [hcut.preimage_bd_union_U]
      exact hx'.symm
    refine ⟨connectedComponentIn (L.U ∪ bd S) (θ x), ⟨θ x, hxB, rfl⟩, ?_⟩
    exact (cut_boundary_component_preimage hS hcut hNo hx).symm
  · rintro C ⟨D, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hcut.quotientMap.surjective x
    have hybd : y ∈ bd S' := by
      rw [← hcut.preimage_bd_union_U]
      change θ y ∈ bd S ∪ L.U
      rw [hy]
      exact hx.symm
    refine ⟨y, hybd, ?_⟩
    rw [cut_boundary_component_preimage hS hcut hNo hybd, hy]

/-- The cardinal equality from the cuff/component correspondence in
VII (4.6), page 226. -/
theorem ncard_cuffs_cut_eq_components (hS : IsSurface S) {L : Drawing S}
    {θ : S' → S} (hcut : IsCutAlongGraph L S' θ) (hNo : NoArcs L) :
    (cuffs S').ncard = (componentsIn (L.U ∪ bd S)).ncard := by
  rw [cuffs_eq_preimages_boundary_components hS hcut hNo]
  exact ncard_image_of_injective _ (Set.preimage_injective.mpr hcut.quotientMap.surjective)

end GraphMinor.GM07

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3Punctured
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.GM11.Section6

/-!
# Properness of the drawing in the punctured surface

In XII (3.1), page 245, every boundary point of Sigma-star lies on one
of the removed disc boundaries. Away from those discs the inclusion is
locally an open embedding into the original closed surface, so every
such point is an interior point. The original drawing meets the disc
boundaries only at vertices, which makes the new drawing proper.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A point of Sigma-star lying in one removed disc is on its boundary.
The closure of the common complement is also in the closure of that
disc's complement. -/
theorem discComplement_inter_disc_subset_boundary {S ι : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i)) (i : ι) :
    discComplement Δ ∩ Δ i ⊆ discBd (Δ i) := by
  intro x hx
  have hsub : (⋃ j, Δ j)ᶜ ⊆ (Δ i)ᶜ := compl_subset_compl.mpr (subset_iUnion Δ i)
  have hxout : x ∈ closure (Δ i)ᶜ := closure_mono hsub hx.1
  have hxfront : x ∈ frontier (Δ i) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hx.2, hxout⟩
  rwa [IsClosedDisc.frontier_eq_discBd hS (hΔ i)] at hxfront

/-- The manifold boundary of Sigma-star is contained in the union of
the prescribed disc boundaries. The reverse identification of cuffs
is a separate geometric step. -/
theorem discComplement_boundary_subset {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) :
    bd (discComplement Δ) ⊆ (Subtype.val : discComplement Δ → S) ⁻¹' ⋃ i, discBd (Δ i) := by
  classical
  intro x hxBd
  by_contra hx
  have hxout : x.val ∉ ⋃ i, Δ i := by
    intro hxD
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
    exact hx (mem_iUnion.mpr ⟨i, discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨x.property,
      hxi⟩⟩)
  let O : Set S := (⋃ i, Δ i)ᶜ
  have hO : IsOpen O := (isClosed_iUnion_of_finite fun i => (hΔ i).isCompact.isClosed).isOpen_compl
  have hOC : O ⊆ discComplement Δ := subset_closure
  have hsource : IsInteriorPoint (⟨x.val, hxout⟩ : O) :=
    (isInteriorPoint_iff_of_isOpenEmbedding hO.isOpenEmbedding_subtypeVal).mp (hS.2.2 x.val)
  have htarget : IsInteriorPoint x :=
    isInteriorPoint_of_isOpenEmbedding (isOpenEmbedding_inclusion_of_isOpen hO hOC) hsource
  exact hxBd htarget

/-- The drawing in Sigma-star is proper, as required to apply VII in
XII (3.1), page 245. The disc-avoidance condition puts every support
point on its boundary in the vertex set. -/
theorem drawingInDiscComplement_isProper {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) :
    (drawingInSubspace Γ (discComplement Δ)
      (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)).IsProper := by
  let hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid
  rintro x ⟨hxBd, hxU⟩
  rw [drawingInSubspace_U] at hxU
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (discComplement_boundary_subset hS Δ hΔ hxBd)
  have hm : x.val ∈ Γ.V ∩ discBd (Δ i) := havoid i ▸
    (show x.val ∈ Γ.U ∩ Δ i from ⟨hxU, Surface.discBd_subset _ hxi⟩)
  rw [drawingInSubspace_V]
  exact hm.1

/-- Boundary vertices of the drawing in Sigma-star map into the set Z
of the setup of XII (3.1), pages 244--245. -/
theorem drawingInDiscComplement_boundary_vertices_subset {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) (hUC : Γ.U ⊆ discComplement Δ) :
    (Subtype.val : discComplement Δ → S) ''
      ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ bd (discComplement Δ)) ⊆
        discBoundaryVertices Γ Δ := by
  rintro x ⟨y, ⟨hyV, hyBd⟩, rfl⟩
  rw [drawingInSubspace_V] at hyV
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (discComplement_boundary_subset hS Δ hΔ hyBd)
  exact mem_iUnion.mpr ⟨i, hyV, hxi⟩

/-- The punctured drawing has no more boundary vertices than the set
Z in XII (3.1), page 245, so the same vertex-count bound can be used
in VII (7.5). -/
theorem drawingInDiscComplement_boundary_vertex_count {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) (hUC : Γ.U ⊆ discComplement Δ) :
    ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ bd (discComplement Δ)).ncard ≤
      (discBoundaryVertices Γ Δ).ncard := by
  have hfinite : (discBoundaryVertices Γ Δ).Finite := Γ.finite_V.subset (by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.1)
  have hsub := drawingInDiscComplement_boundary_vertices_subset hS Γ Δ hΔ hUC
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm.le.trans
    (Set.ncard_le_ncard hsub hfinite)

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM11.Section6

/-!
# The exact boundary of the punctured surface

For XII (3.1), page 245, Sigma-star has precisely the prescribed disc
boundaries as its manifold boundary. A subspace interior chart has
ambient open image by invariance of domain. At a disc boundary point,
every ambient neighbourhood meets the disc interior, so such a chart
cannot stay in Sigma-star. Together with the opposite inclusion, this
identifies the boundary and the exact boundary vertex set.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 Metric

/-- An interior point of a subspace of a closed surface is an ambient
interior point of that subspace. This is invariance of domain applied
to its open-disc chart. -/
theorem interiorPoint_subspace_mem_interior {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {C : Set S} {x : C} (hx : IsInteriorPoint x) :
    x.val ∈ interior C := by
  obtain ⟨U, h, g, hc, _, hg0⟩ := hx.exists_ballChart isOpen_univ (mem_univ x) (R := 1) one_pos
  have hg : ContinuousOn (fun z => (g z).val) (ball (0 : ℂ) 1) :=
    continuous_subtype_val.comp_continuousOn hc.gc
  have hgi : InjOn (fun z => (g z).val) (ball (0 : ℂ) 1) := by
    intro z hz z' hz' heq
    exact hc.hg.injOn hz hz' (Subtype.ext heq)
  have hopen : IsOpen ((fun z => (g z).val) '' ball (0 : ℂ) 1) :=
    isOpen_image_of_manifold isOpen_ball hg hgi (fun _ _ => (hS.2.2 _).isManifoldPoint)
  apply mem_interior.mpr
  refine ⟨(fun z => (g z).val) '' ball (0 : ℂ) 1, ?_, hopen, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact (g z).property
  · exact ⟨0, mem_ball_self one_pos, congrArg Subtype.val hg0⟩

/-- A point of a removed disc boundary cannot be an ambient interior
point of Sigma-star, since that disc is the closure of its interior. -/
theorem disc_boundary_not_mem_interior_discComplement {S ι : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    {i : ι} {x : S} (hx : x ∈ discBd (Δ i)) : x ∉ interior (discComplement Δ) := by
  intro hxint
  have hxcl : x ∈ closure (Δ i \ frontier (Δ i)) :=
    IsClosedDisc.subset_closure_diff_frontier hS (hΔ i) (Surface.discBd_subset _ hx)
  obtain ⟨y, hyC, hyD⟩ := mem_closure_iff.mp hxcl (interior (discComplement Δ)) isOpen_interior
    hxint
  have hyBd := discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨interior_subset hyC, hyD.1⟩
  have hyFront : y ∈ frontier (Δ i) := by
    rwa [IsClosedDisc.frontier_eq_discBd hS (hΔ i)]
  exact hyD.2 hyFront

/-- The manifold boundary of Sigma-star is exactly the part of the
union of disc boundaries lying in it. This identifies the boundary in
XII (3.1), page 245. -/
theorem discComplement_boundary_eq {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) :
    bd (discComplement Δ) = (Subtype.val : discComplement Δ → S) ⁻¹' ⋃ i, discBd (Δ i) := by
  apply Subset.antisymm (discComplement_boundary_subset hS Δ hΔ)
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  intro hxint
  exact disc_boundary_not_mem_interior_discComplement hS Δ hΔ hxi
    (interiorPoint_subspace_mem_interior hS hxint)

/-- Boundary vertices of the punctured drawing map to exactly the set
Z used by XII (3.1), pages 244--245. Disjointness keeps every prescribed
disc boundary in Sigma-star. -/
theorem drawingInDiscComplement_boundary_vertices_eq {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hUC : Γ.U ⊆ discComplement Δ) :
    (Subtype.val : discComplement Δ → S) ''
      ((drawingInSubspace Γ (discComplement Δ) hUC).V ∩ bd (discComplement Δ)) =
        discBoundaryVertices Γ Δ := by
  apply Subset.antisymm (drawingInDiscComplement_boundary_vertices_subset hS Γ Δ hΔ hUC)
  intro x hx
  obtain ⟨i, hxV, hxBd⟩ := mem_iUnion.mp hx
  have hxC : x ∈ discComplement Δ := disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxBd
  let y : discComplement Δ := ⟨x, hxC⟩
  refine ⟨y, ⟨?_, ?_⟩, rfl⟩
  · rw [drawingInSubspace_V]
    exact hxV
  · rw [discComplement_boundary_eq hS Δ hΔ]
    exact mem_iUnion.mpr ⟨i, hxBd⟩

end GraphMinor.GM12

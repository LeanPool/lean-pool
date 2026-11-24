/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Local image coverage from neighbourhoods of a fibre

For the positive-length trace restriction in XII (2.1), pages 243--244,
all sufficiently near curve-image points come from neighbourhoods of
the parameters mapping to the chosen vertex. The complement of those
parameter neighbourhoods is compact. Its image is closed and misses
the vertex, so deleting that image gives the required neighbourhood.
This lets finitely many entering and leaving corner germs control
the whole curve image near the vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology

/-- Near a point of the target, every image point of a compact source
comes from any prescribed open neighbourhood of that point's fibre. -/
theorem exists_image_neighbourhood_from_fibre_cover
    {A S : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace S] [T2Space S] {f : A → S} (hf : Continuous f)
    {v : S} {U : Set A} (hU : IsOpen U) (hcover : f ⁻¹' {v} ⊆ U) :
    ∃ N : Set S, IsOpen N ∧ v ∈ N ∧ range f ∩ N ⊆ f '' U := by
  let N := (f '' Uᶜ)ᶜ
  have hNc : IsOpen N := ((hU.isClosed_compl.isCompact).image hf).isClosed.isOpen_compl
  have hvN : v ∈ N := by
    rintro ⟨z, hz, he⟩
    exact hz (hcover (show z ∈ f ⁻¹' {v} from he))
  refine ⟨N, hNc, hvN, ?_⟩
  rintro x ⟨⟨z, rfl⟩, hzN⟩
  by_cases hz : z ∈ U
  · exact ⟨z, hz, rfl⟩
  · exact (hzN ⟨z, hz, rfl⟩).elim

/-- If the curve image lies in a set near every parameter over a
point, its whole image lies in that set near the point. -/
theorem exists_image_neighbourhood_of_fibre_germs
    {A S : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace S] [T2Space S] {f : A → S} (hf : Continuous f)
    {v : S} {V : Set S}
    (hgerm : ∀ z, f z = v → f ⁻¹' V ∈ nhds z) :
    ∃ N : Set S, IsOpen N ∧ v ∈ N ∧ range f ∩ N ⊆ V := by
  have hcover : f ⁻¹' {v} ⊆ interior (f ⁻¹' V) := by
    intro z hz
    exact mem_interior_iff_mem_nhds.mpr (hgerm z hz)
  obtain ⟨N, hN, hvN, hsub⟩ := exists_image_neighbourhood_from_fibre_cover hf isOpen_interior hcover
  refine ⟨N, hN, hvN, hsub.trans ?_⟩
  rintro x ⟨z, hz, rfl⟩
  exact interior_subset (s := f ⁻¹' V) hz

/-- If a part of the image accumulates at a point, it accumulates
at some parameter over that point. Compactness makes the image
of the closed parameter accumulation set closed. -/
theorem exists_fibre_point_in_closure_preimage
    {A S : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace S] [T2Space S] {f : A → S} (hf : Continuous f)
    {v : S} {B : Set S} (hv : v ∈ closure (range f ∩ B)) :
    ∃ a : A, f a = v ∧ a ∈ closure (f ⁻¹' B) := by
  have hclosed : IsClosed (f '' closure (f ⁻¹' B)) :=
    (isClosed_closure.isCompact.image hf).isClosed
  have hsub : range f ∩ B ⊆ f '' closure (f ⁻¹' B) := by
    rintro z ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, subset_closure ha, rfl⟩
  obtain ⟨a, ha, hav⟩ := (closure_minimal hsub hclosed) hv
  exact ⟨a, hav, ha⟩

end GraphMinor.GM12

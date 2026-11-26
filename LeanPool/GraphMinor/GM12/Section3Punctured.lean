/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Section6

/-!
# The surface with the prescribed discs removed

XII Section 3, page 245, writes Sigma-star for the closure of the
complement of the disjoint discs. Their boundaries remain in this
closure. The drawing also remains there, because its only points in
each disc are vertices on that disc's boundary. These inclusions are
the first step in reading the drawing as a proper graph for VII (7.5).
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The closure of the complement of the discs, denoted Sigma-star in
Graph Minors XII, Section 3, page 245. -/
@[expose] def discComplement {S ι : Type*} [TopologicalSpace S] (Δ : ι → Set S) : Set S :=
  closure (⋃ i, Δ i)ᶜ

/-- The boundary vertex set denoted Z in XII, Section 3, pages 244--245:
the union of the original vertices on the prescribed disc boundaries. -/
@[expose] def discBoundaryVertices {S ι : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (Δ : ι → Set S) : Set S := ⋃ i, Γ.V ∩ discBd (Δ i)

/-- A boundary point of one closed member of a finite disjoint family
is approached from outside the whole family. Exclude the other closed
members before approaching from outside the chosen member. -/
theorem mem_discComplement_of_mem_frontier {S ι : Type*} [TopologicalSpace S] [Finite ι]
    (Δ : ι → Set S) (hclosed : ∀ i, IsClosed (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {i : ι} {x : S} (hxi : x ∈ Δ i) (hfront : x ∈ frontier (Δ i)) :
    x ∈ discComplement Δ := by
  classical
  let B : Set S := ⋃ j : {j // j ≠ i}, Δ j.val
  have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hclosed j.val
  have hxB : x ∉ B := by
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hdisj j.property.symm) hxi hxj
  have hxout : x ∈ closure (Δ i)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hfront
    exact hfront.2
  apply mem_closure_iff.mpr
  intro O hO hxO
  obtain ⟨y, hyO, hyout⟩ := mem_closure_iff.mp hxout (O ∩ Bᶜ)
    (hO.inter hB.isOpen_compl) ⟨hxO, hxB⟩
  refine ⟨y, hyO.1, ?_⟩
  intro hyunion
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hyunion
  by_cases hji : j = i
  · exact hyout (hji ▸ hyj)
  · exact hyO.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)

/-- Every prescribed disc boundary remains in the surface Sigma-star
of XII (3.1), page 245. -/
theorem disc_boundary_subset_discComplement {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) (i : ι) :
    discBd (Δ i) ⊆ discComplement Δ := by
  intro x hx
  apply mem_discComplement_of_mem_frontier Δ (fun j => (hΔ j).isCompact.isClosed) hdisj
    (Surface.discBd_subset _ hx)
  rwa [IsClosedDisc.frontier_eq_discBd hS (hΔ i)]

/-- The drawing in the setup of XII (3.1), pages 244--245, is supported
in Sigma-star. The hypothesis that it meets each disc only at boundary
vertices is used at every point lying in a prescribed disc. -/
theorem drawing_support_subset_discComplement {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) : Γ.U ⊆ discComplement Δ := by
  intro x hx
  by_cases hxD : x ∈ ⋃ i, Δ i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
    have hxb : x ∈ Γ.V ∩ discBd (Δ i) := havoid i ▸ ⟨hx, hxi⟩
    exact disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxb.2
  · exact subset_closure hxD

end GraphMinor.GM12

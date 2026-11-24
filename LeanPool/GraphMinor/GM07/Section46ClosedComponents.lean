/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs

/-!
# Finite closed component families

The cuff count on page 226 of VII (4.6) uses the components of
`U(L) ∪ bd(Σ)`. A finite connected cover makes their number finite.
For a closed set, each component is closed, and a finite component
family makes the complement of each component closed as well.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- A finite cover by nonempty preconnected sets gives finitely many
components, as used for the cuff count in VII (4.6), page 226. -/
theorem finite_componentsIn_of_finite_preconnected_cover {S : Type*} [TopologicalSpace S]
    {B : Set S} {𝒜 : Set (Set S)} (hfin : 𝒜.Finite)
    (hne : ∀ A ∈ 𝒜, A.Nonempty) (hconn : ∀ A ∈ 𝒜, IsPreconnected A)
    (hcover : B = ⋃₀ 𝒜) : (componentsIn B).Finite := by
  classical
  have : Finite 𝒜 := hfin.to_subtype
  choose p hp using fun A : 𝒜 => hne A.1 A.2
  apply (finite_range (fun A : 𝒜 => connectedComponentIn B (p A))).subset
  rintro C ⟨x, hx, rfl⟩
  obtain ⟨A, hA, hxA⟩ := (congrArg (fun Z => x ∈ Z) hcover).mp hx
  let A' : 𝒜 := ⟨A, hA⟩
  have hAB : A ⊆ B := hcover ▸ subset_sUnion_of_mem hA
  have hxComp : x ∈ connectedComponentIn B (p A') :=
    (hconn A hA).subset_connectedComponentIn (hp A') hAB hxA
  exact ⟨A', connectedComponentIn_eq hxComp⟩

/-- Components of a closed set are closed in the ambient space. -/
theorem isClosed_of_mem_componentsIn {S : Type*} [TopologicalSpace S]
    {B C : Set S} (hB : IsClosed B) (hC : C ∈ componentsIn B) : IsClosed C := by
  obtain ⟨x, hx, rfl⟩ := hC
  apply isClosed_of_closure_subset
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hx))
    (closure_minimal (connectedComponentIn_subset _ _) hB)

/-- Distinct components are disjoint. -/
theorem disjoint_of_mem_componentsIn_ne {S : Type*} [TopologicalSpace S]
    {B C D : Set S} (hC : C ∈ componentsIn B) (hD : D ∈ componentsIn B) (hne : C ≠ D) :
    Disjoint C D := by
  obtain ⟨x, _, rfl⟩ := hC
  obtain ⟨y, _, rfl⟩ := hD
  apply disjoint_left.mpr
  intro z hzC hzD
  exact hne ((connectedComponentIn_eq hzC).trans (connectedComponentIn_eq hzD).symm)

/-- In a finite closed component family, deleting one component leaves
a closed set, as needed for lifting the components in VII (4.6), page 226. -/
theorem isClosed_sdiff_of_mem_finite_componentsIn {S : Type*} [TopologicalSpace S]
    {B C : Set S} (hB : IsClosed B) (hfin : (componentsIn B).Finite)
    (hC : C ∈ componentsIn B) : IsClosed (B \ C) := by
  have heq : B \ C = ⋃₀ (componentsIn B \ {C}) := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxC⟩
      let D := connectedComponentIn B x
      have hD : D ∈ componentsIn B := ⟨x, hxB, rfl⟩
      have hxD : x ∈ D := mem_connectedComponentIn hxB
      have hDC : D ≠ C := fun h => hxC (h ▸ hxD)
      exact ⟨D, ⟨hD, hDC⟩, hxD⟩
    · rintro x ⟨D, ⟨hD, hDC⟩, hxD⟩
      have hDB : D ⊆ B := by obtain ⟨y, _, rfl⟩ := hD; exact connectedComponentIn_subset _ _
      exact ⟨hDB hxD, fun hxC => disjoint_left.mp
        (disjoint_of_mem_componentsIn_ne hD hC hDC) hxD hxC⟩
  rw [heq]
  exact hfin.sdiff.isClosed_sUnion fun D hD => isClosed_of_mem_componentsIn hB hD.1

end GraphMinor.GM07

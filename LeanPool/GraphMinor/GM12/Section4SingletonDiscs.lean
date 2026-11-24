/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4VertexRegion
import LeanPool.GraphMinor.GM12.Section4NormalArcDisc
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Small empty discs at selected vertices

In XII (4.4), page 251, put a small disc at each selected vertex
that meets the drawing only there. Leave the vertex through a
region inside an assigned open neighborhood and thicken that arc.
Forbid the drawing and the complement of the neighborhood. Distinct
selected vertices have disjoint open neighborhoods, so their discs
can be chosen simultaneously disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A disc inside an assigned open neighborhood meeting the drawing
at exactly one chosen boundary vertex. -/
theorem exists_single_vertex_disc_in_open
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {v : S} (hv : v ∈ Γ.V)
    {U : Set S} (hU : IsOpen U) (hvU : v ∈ U) :
    ∃ D, IsClosedDisc D ∧ D ⊆ U ∧ Γ.U ∩ D = {v} ∧ v ∈ discBd D := by
  obtain ⟨a, ha, ha0, ha1, haU, haΓ⟩ := exists_normal_arc_from_vertex_in_open hS Γ hv hU hvU
  let B := Γ.U ∪ Uᶜ ∪ {a 1}
  have hB : IsClosed B := (Γ.isClosed_U.union hU.isClosed_compl).union isClosed_singleton
  have hmeet : range a ∩ B ⊆ {a 0, a 1} := by
    rintro x ⟨hxa, hxB⟩
    rcases hxB with (hxΓ | hxU) | hx1
    · have hxv := Set.mem_singleton_iff.mp (haΓ.subset ⟨hxa, hxΓ⟩)
      exact Or.inl (hxv.trans ha0.symm)
    · exact False.elim (hxU (haU hxa))
    · exact Or.inr hx1
  obtain ⟨D, hD, hDB, hbd, _⟩ := exists_normal_arc_disc hS ha hB
    (Or.inl (Or.inl (ha0.symm ▸ Γ.V_subset_U hv))) (Or.inr (by simp)) hmeet
  refine ⟨D, hD, ?_, ?_, ha0 ▸ hbd (Or.inl rfl)⟩
  · intro x hxD
    by_contra hxU
    have hends := hDB.subset ⟨hxD, Or.inl (Or.inr hxU)⟩
    rcases hends with hx0 | hx1
    · exact hxU (hx0 ▸ haU (mem_range_self 0))
    · exact hxU ((Set.mem_singleton_iff.mp hx1) ▸ haU (mem_range_self 1))
  · apply Set.Subset.antisymm
    · rintro x ⟨hxΓ, hxD⟩
      have hends := hDB.subset ⟨hxD, Or.inl (Or.inl hxΓ)⟩
      rcases hends with hx0 | hx1
      · exact Set.mem_singleton_iff.mpr (hx0.trans ha0)
      · exact False.elim (ha1 ((Set.mem_singleton_iff.mp hx1) ▸ hxΓ))
    · rintro x rfl
      exact ⟨Γ.V_subset_U hv, discBd_subset D (ha0 ▸ hbd (Or.inl rfl))⟩

/-- The mutually disjoint empty discs chosen in XII (4.4), page
251, with their exact boundary vertex sets. -/
theorem exists_disjoint_single_vertex_discs
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {t : ℕ} (z : Fin t → S)
    (hz : ∀ i, z i ∈ Γ.V) (hinj : Function.Injective z) :
    ∃ Δ : Fin t → Set S,
      (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = {z i} ∧
        z i ∈ discBd (Δ i) ∧ Γ.V ∩ discBd (Δ i) = {z i}) ∧
      ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j) := by
  obtain ⟨U, hU, hUdisj⟩ := (Set.finite_range z).t2_separation
  have hex : ∀ i, ∃ D, IsClosedDisc D ∧ D ⊆ U (z i) ∧
      Γ.U ∩ D = {z i} ∧ z i ∈ discBd D :=
    fun i => exists_single_vertex_disc_in_open hS Γ (hz i) (hU (z i)).2 (hU (z i)).1
  choose Δ hΔ hsub hmeet hbd using hex
  refine ⟨Δ, ?_, ?_⟩
  · intro i
    refine ⟨hΔ i, hmeet i, hbd i, ?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      exact (hmeet i).subset ⟨Γ.V_subset_U hx.1, discBd_subset _ hx.2⟩
    · rintro x rfl
      exact ⟨hz i, hbd i⟩
  · intro i j hij
    exact (hUdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hinj h))).mono (hsub i)
      (hsub j)

end GraphMinor.GM12

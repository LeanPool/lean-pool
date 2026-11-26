/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3FeasibilityForests
import LeanPool.GraphMinor.GM12.Section3SurfaceForestUnion
import LeanPool.GraphMinor.GM12.Section3DisjointFamilyWalks

/-!
# The feasibility forest with its boundary classes

For XII (3.1), page 245, combine the disjoint local forests into one
proper surface forest. Its boundary vertex set is the union of the
prescribed partition parts. A walk stays in one local forest, while
each local forest is connected. Thus its boundary connection classes
are exactly the prescribed parts.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Topological feasibility supplies the actual forest needed by
VII (7.5) in the proof of XII (3.1), including its exact boundary
vertex set and connection classes. -/
theorem exists_feasibility_forest
    {S : Type*} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (Zs : Fin p → Set S) (hfin : ∀ j, (Zs j).Finite)
    (hZ : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i))
    (hfeasible : IsTopologicallyFeasible Δ Zs) :
    ∃ K : Drawing (discComplement Δ), GM07.IsSurfaceForest K ∧
      K.V ∩ bd (discComplement Δ) = Subtype.val ⁻¹' ⋃ j, Zs j ∧
      ∀ j, ∀ x ∈ (Subtype.val : discComplement Δ → S) ⁻¹' Zs j,
        ∀ y ∈ K.V ∩ bd (discComplement Δ),
          Nonempty (GraphWalk K.toGraph x y) ↔ y.val ∈ Zs j := by
  obtain ⟨H, hH, hdis⟩ := exists_disjoint_feasibility_forests hS Δ hΔ hdisj Zs hfin hZ hfeasible
  obtain ⟨K, hK, _, hV, hE, hsub⟩ :=
    exists_disjoint_surface_forest_union H (fun j => (hH j).1) hdis
  have hdisV : Pairwise (fun i j => Disjoint (H i).V (H j).V) := by
    intro i j hij
    exact (hdis i j hij).mono (H i).V_subset_U (H j).V_subset_U
  have hboundary : K.V ∩ bd (discComplement Δ) = Subtype.val ⁻¹' ⋃ j, Zs j := by
    ext x
    constructor
    · rintro ⟨hxV, hxB⟩
      rw [hV] at hxV
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxV
      have hx : x ∈ (H j).V ∩ bd (discComplement Δ) := ⟨hxj, hxB⟩
      rw [(hH j).2.2] at hx
      exact mem_iUnion.mpr ⟨j, hx⟩
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      have hx : x ∈ (H j).V ∩ bd (discComplement Δ) := by
        rw [(hH j).2.2]
        exact hxj
      exact ⟨(hsub j).1 hx.1, hx.2⟩
  refine ⟨K, hK, hboundary, ?_⟩
  intro j x hx y hy
  have hxH : x ∈ (H j).V ∩ bd (discComplement Δ) := by
    rw [(hH j).2.2]
    exact hx
  have hiff := walk_iff_mem_boundary_class_of_disjoint_family H K hsub hdisV hE.le
    j (hH j).2.1 hxH hy
  rw [(hH j).2.2] at hiff
  exact hiff

end GraphMinor.GM12

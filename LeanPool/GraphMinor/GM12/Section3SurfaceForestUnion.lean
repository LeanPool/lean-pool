/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM12.Section3FiniteDrawingUnion
import LeanPool.GraphMinor.GM12.Section3DisjointFamilyWalks

/-!
# The union of disjoint surface forests

The local forests of XII (3.1), page 245, combine into one proper
surface forest. The drawing union has exact vertex and edge formulas.
Properness holds in each component, and the walk containment lemma
passes the forest property to the union.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A finite disjoint family of proper surface forests combines into
a proper surface forest, with exact support, vertex and edge sets. -/
theorem exists_disjoint_surface_forest_union
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (H : ι → Drawing S) (hF : ∀ i, GM07.IsSurfaceForest (H i))
    (hdis : Pairwise (fun i j => Disjoint (H i).U (H j).U)) :
    ∃ K : Drawing S, GM07.IsSurfaceForest K ∧ K.U = ⋃ i, (H i).U ∧
      K.V = ⋃ i, (H i).V ∧ K.E = ⋃ i, (H i).E ∧ ∀ i, (H i).IsSubdrawing K := by
  obtain ⟨K, hU, hV, hE⟩ := exists_finite_disjoint_drawing_union H hdis
  have hsub : ∀ i, (H i).IsSubdrawing K := by
    intro i
    constructor
    · intro x hx
      rw [hV]
      exact mem_iUnion.mpr ⟨i, hx⟩
    · intro e he
      rw [hE]
      exact mem_iUnion.mpr ⟨i, he⟩
  have hdisV : Pairwise (fun i j => Disjoint (H i).V (H j).V) := by
    intro i j hij
    exact (hdis hij).mono (H i).V_subset_U (H j).V_subset_U
  have hproper : K.IsProper := by
    rintro x ⟨hxB, hxU⟩
    rw [hU] at hxU
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    rw [hV]
    exact mem_iUnion.mpr ⟨i, (hF i).1 ⟨hxB, hxi⟩⟩
  have hforest : IsGraphForest K.toGraph := isGraphForest_of_disjoint_family_cover H K
    hsub hdisV (hV.le) (hE.le) (fun i => (hF i).2)
  exact ⟨K, ⟨hproper, hforest⟩, hU, hV, hE, hsub⟩

end GraphMinor.GM12

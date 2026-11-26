/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3FeasibilityDiscs
public import LeanPool.GraphMinor.GM12.Section3DiscStarForest
import LeanPool.GraphMinor.GM12.Section3FiniteDrawingUnion
import LeanPool.GraphMinor.GM12.Section3DisjointFamilyWalks
import LeanPool.GraphMinor.GM11.Walks

/-!
# A feasibility forest in the original surface

For the auxiliary-disc step of XII (3.2), page 247, construct the
boundary-connection forest before choosing the third disc. Draw a
finite star inside each topological feasibility disc. Their supports
are disjoint, so their union is a forest. It meets the prescribed
discs exactly at the prescribed vertices and has exactly the required
boundary connection classes.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The feasibility forest of XII (3.1), retained in the original
surface to choose the auxiliary disc of (3.2), page 247. -/
theorem exists_ambient_feasibility_forest
    {S : Type*} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Δ : Fin t → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdis : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (Zs : Fin p → Set S) (hfin : ∀ j, (Zs j).Finite)
    (hZ : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i)) (hfeasible : IsTopologicallyFeasible Δ Zs) :
    ∃ K : Drawing S, IsGraphForest K.toGraph ∧
      K.U ∩ ⋃ i, Δ i = ⋃ j, Zs j ∧ K.V ∩ ⋃ i, Δ i = ⋃ j, Zs j ∧
      ∀ j, ∀ x ∈ Zs j, ∀ y ∈ K.V ∩ ⋃ i, Δ i,
        Nonempty (GraphWalk K.toGraph x y) ↔ y ∈ Zs j := by
  classical
  obtain ⟨D, hD, hDD, hcontact⟩ := hfeasible
  have hlocal : ∀ j, ∃ H : Drawing S, H.U ⊆ D j ∧ IsGraphForest H.toGraph ∧
      IsConnectedDrawing H ∧ Zs j ⊆ H.V := by
    intro j
    have hZbd := feasibility_contacts_subset_discBd hS Δ hΔ hdis (hD j) (hcontact j) (hZ j)
    obtain ⟨H, c, _, hUD, hV, _, hF, hC⟩ := exists_connected_forest_in_disc (hD j) (hfin j) hZbd
    refine ⟨H, hUD, hF, hC, ?_⟩
    rw [hV]
    exact subset_insert _ _
  choose H hHU hHF hHC hZV using hlocal
  have hdisU : Pairwise (fun i j => Disjoint (H i).U (H j).U) :=
    fun i j hij => (hDD i j hij).mono (hHU i) (hHU j)
  obtain ⟨K, hKU, hKV, hKE⟩ := exists_finite_disjoint_drawing_union H hdisU
  have hsub : ∀ i, (H i).IsSubdrawing K := by
    intro i
    constructor
    · intro x hx
      rw [hKV]
      exact mem_iUnion.mpr ⟨i, hx⟩
    · intro e he
      rw [hKE]
      exact mem_iUnion.mpr ⟨i, he⟩
  have hdisV : Pairwise (fun i j => Disjoint (H i).V (H j).V) :=
    fun i j hij => (hdisU hij).mono (H i).V_subset_U (H j).V_subset_U
  have hF : IsGraphForest K.toGraph := isGraphForest_of_disjoint_family_cover H K
    hsub hdisV hKV.subset hKE.subset hHF
  have hHUcap : ∀ j, (H j).U ∩ ⋃ i, Δ i = Zs j := by
    intro j
    apply Subset.antisymm
    · intro x hx
      exact (hcontact j).subset ⟨hHU j hx.1, hx.2⟩
    · intro x hx
      exact ⟨(H j).V_subset_U (hZV j hx), ((hcontact j).symm.subset hx).2⟩
  have hKUcap : K.U ∩ ⋃ i, Δ i = ⋃ j, Zs j := by
    ext x
    constructor
    · rintro ⟨hx, hxΔ⟩
      rw [hKU] at hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j, (hHUcap j).subset ⟨hxj, hxΔ⟩⟩
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      refine ⟨K.V_subset_U ((hsub j).1 (hZV j hxj)), ?_⟩
      exact ((hcontact j).symm.subset hxj).2
  have hKVcap : K.V ∩ ⋃ i, Δ i = ⋃ j, Zs j := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ K.V_subset_U).trans hKUcap.subset
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact ⟨(hsub j).1 (hZV j hxj), ((hcontact j).symm.subset hxj).2⟩
  refine ⟨K, hF, hKUcap, hKVcap, ?_⟩
  intro j x hx y hy
  constructor
  · rintro ⟨W⟩
    have hyH := (walk_stays_in_disjoint_family H K hsub hdisV hKE.subset j W (hZV j hx)).1
      y W.end_mem_support
    exact (hHUcap j).subset ⟨(H j).V_subset_U hyH, hy.2⟩
  · intro hyj
    obtain ⟨W⟩ := hHC j x (hZV j hx) y (hZV j hyj)
    obtain ⟨W', _, _⟩ := (hsub j).exists_walk_up W
    exact ⟨W'⟩

end GraphMinor.GM12

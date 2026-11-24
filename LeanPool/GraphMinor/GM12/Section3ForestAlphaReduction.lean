/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ForestBound
public import LeanPool.GraphMinor.GM12.Section3BoundaryLinked
import LeanPool.GraphMinor.GM12.Section3ForestEmptyClasses
import LeanPool.GraphMinor.GM12.Section3ForestConnections
import LeanPool.GraphMinor.GM12.Section3AmbientTransfer
import LeanPool.GraphMinor.GM12.Section3BoundaryEquality

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The alpha reduction with a supplied feasibility forest

For the auxiliary-disc step of XII (3.2), page 247, keep the
boundary-connection forest when adding an empty-boundary disc.
The VII (7.5) reduction works directly with this forest. No new
choice of topological feasibility discs is required.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- The VII (7.5) application in XII (3.1), with the boundary
connection forest supplied explicitly for use in XII (3.2). -/
theorem connecting_subdrawings_of_alpha_bound_of_forest
    {S : Type u} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    (Zs : Fin p → Set S) (hcover : ⋃ j, Zs j = discBoundaryVertices Γ Δ)
    (hdisZ : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (H : Drawing (discComplement Δ)) (hHF : GM07.IsSurfaceForest H)
    (hHB : H.V ∩ bd (discComplement Δ) = Subtype.val ⁻¹' ⋃ j, Zs j)
    (hclasses : ∀ j, ∀ x ∈ (Subtype.val : discComplement Δ → S) ⁻¹' Zs j,
      ∀ y ∈ H.V ∩ bd (discComplement Δ),
        Nonempty (GraphWalk H.toGraph x y) ↔ y.val ∈ Zs j)
    (hbound : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      ∀ D : Set S, IsClosedDisc D → discBd D = F →
      ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
        (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard)
    (a b c z : ℕ) (hcomplex : 3 ≤ 3 * a + 3 * b + c)
    (hmodel : Nonempty (discComplement Δ ≃ₜ SurfaceModel a b c))
    (hcount : (discBoundaryVertices Γ Δ).ncard ≤ z)
    (hα : 42 * (z + c + 1) * GM07.vModel a b (c + 1) (z + c + 1) ≤
      GM07.alpha (drawingInSubspace Γ (discComplement Δ)
        (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid))) :
    HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  let C := discComplement Δ
  let Z := discBoundaryVertices Γ Δ
  let hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid
  let G := drawingInSubspace Γ C hUC
  have hZs : ∀ j, Zs j ⊆ Z := by
    intro j x hx
    change x ∈ discBoundaryVertices Γ Δ
    rw [← hcover]
    exact mem_iUnion.mpr ⟨j, hx⟩
  have hZsV : ∀ j, Zs j ⊆ Γ.V := by
    intro j x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hZs j hx)
    exact hxi.1
  have hZsBd : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i) := by
    intro j x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hZs j hx)
    exact mem_iUnion.mpr ⟨i, hxi.2⟩
  have hZsC : ∀ j, Zs j ⊆ C := by
    intro j x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hZsBd j hx)
    exact disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxi
  have hHB' : H.V ∩ bd C = (Subtype.val : C → S) ⁻¹' Z := by
    rw [hcover] at hHB
    exact hHB
  have hGBimage := drawingInDiscComplement_boundary_vertices_eq hS Γ Δ hΔ hdisj hUC
  have hGB : G.V ∩ bd C = (Subtype.val : C → S) ⁻¹' Z := by
    ext x
    constructor
    · intro hx
      change x.val ∈ discBoundaryVertices Γ Δ
      rw [← hGBimage]
      exact mem_image_of_mem Subtype.val hx
    · intro hx
      change x.val ∈ discBoundaryVertices Γ Δ at hx
      rw [← hGBimage] at hx
      obtain ⟨y, hy, he⟩ := hx
      have hyx : y = x := Subtype.ext he
      exact hyx ▸ hy
  have hlinked := drawingInDiscComplement_isBoundaryLinked hS Γ Δ hΔ hdisj havoid hbound
  have hcountG : (G.V ∩ bd C).ncard ≤ z :=
    (drawingInDiscComplement_boundary_vertex_count hS Γ Δ hΔ hUC).trans hcount
  have hfeas := feasible_forest_of_large_alpha (discComplement_isSurface hS Δ hΔ hdisj)
    hcomplex hmodel G H hlinked hcountG hα hHF (hGB.trans hHB'.symm)
  have hparts : ∀ j, (Subtype.val : C → S) ⁻¹' Zs j ⊆ H.V ∩ bd C := by
    intro j x hx
    rw [hHB']
    exact hZs j hx
  have hparts_dis : ∀ i j, i ≠ j → Disjoint
      ((Subtype.val : C → S) ⁻¹' Zs i) (Subtype.val ⁻¹' Zs j) := by
    intro i j hij
    exact (hdisZ i j hij).preimage Subtype.val
  have hconnect := hasConnectingSubdrawings_of_feasible_forest_allowing_empty hfeas hparts
    hparts_dis hclasses
  rw [hHB'] at hconnect
  exact hasConnectingSubdrawings_from_closed_subspace Γ C isClosed_closure hUC hZsC hconnect

end GraphMinor.GM12

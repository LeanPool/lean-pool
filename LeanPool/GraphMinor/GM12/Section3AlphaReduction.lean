/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ForestBound
public import LeanPool.GraphMinor.GM12.Section3BoundaryLinked
import LeanPool.GraphMinor.GM12.Section3FeasibilityForest
import LeanPool.GraphMinor.GM12.Section3ForestAlphaReduction

/-!
# The final reduction of XII (3.1) to VII

Once the alpha bound and the surface model are known, apply VII (7.5)
to the actual punctured drawing and feasibility forest. Boundary
linkage follows from XII (3.1)(v). The feasible forest preserves its
boundary connection classes, giving connected subdrawings. Finally,
include them back into the original surface.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- The application of VII (7.5) in XII (3.1), page 245, after the
alpha estimate and the surface model have been established. All drawing,
forest, boundary-linkage and ambient-transfer steps are proved here. -/
theorem connecting_subdrawings_of_alpha_bound
    {S : Type u} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    (Zs : Fin p → Set S) (hcover : ⋃ j, Zs j = discBoundaryVertices Γ Δ)
    (_hne : ∀ j, (Zs j).Nonempty)
    (hdisZ : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hfeasible : IsTopologicallyFeasible Δ Zs)
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
  let Z := discBoundaryVertices Γ Δ
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
  obtain ⟨H, hHF, hHB, hclasses⟩ := exists_feasibility_forest hS Δ hΔ hdisj Zs
    (fun j => Γ.finite_V.subset (hZsV j)) hZsBd hfeasible
  exact connecting_subdrawings_of_alpha_bound_of_forest hS Γ Δ hΔ hdisj havoid Zs hcover
    hdisZ H hHF hHB hclasses hbound a b c z hcomplex hmodel hcount hα

end GraphMinor.GM12

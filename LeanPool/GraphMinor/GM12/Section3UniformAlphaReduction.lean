/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3AlphaEmptyClasses
public import LeanPool.GraphMinor.GM12.Section3ModelComplexity

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# A uniform alpha threshold for the connecting subdrawings

The application of VII in XII (3.1), page 245, chooses its threshold
from the fixed surface, the number of deleted discs and the boundary
vertex bound. The punctured surface has fixed model parameters, so
VII's numerical threshold is independent of the drawing and of the
disc placement. The alpha estimate is the remaining input here.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- The uniform numerical choice in the application of VII (7.5) for
XII (3.1). All model, complexity, forest and boundary-linkage requirements
are discharged. Only the alpha bound remains as a hypothesis. -/
theorem exists_uniform_connecting_alpha_threshold
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ N : ℕ, ∀ (Γ : Drawing S) (Δ : Fin t → Set S)
      (hΔ : ∀ i, IsClosedDisc (Δ i))
      (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
      (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
      (p : ℕ) (Zs : Fin p → Set S),
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) →
      IsTopologicallyFeasible Δ Zs →
      (∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
        ∀ D : Set S, IsClosedDisc D → discBd D = F →
        ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
          (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      N ≤ GM07.alpha (drawingInSubspace Γ (discComplement Δ)
        (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨a, b, hcomplex, hmodel⟩ := exists_uniform_discComplement_model hS t hcase
  refine ⟨42 * (z + t + 1) * GM07.vModel a b (t + 1) (z + t + 1), ?_⟩
  intro Γ Δ hΔ hd ha p Zs hcover hdisZ hfeasible hbound hcount hα
  exact connecting_subdrawings_of_alpha_bound_allowing_empty hS Γ Δ hΔ hd ha Zs
    hcover hdisZ hfeasible hbound a b t z hcomplex (hmodel Δ hΔ hd) hcount hα

end GraphMinor.GM12

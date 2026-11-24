/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ProperDiscForest
public import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section3BoundaryEquality
import LeanPool.GraphMinor.GM12.Section3FeasibilityDiscs

/-!
# Disjoint local forests from topological feasibility

The discs in the topological feasibility condition of XII (3.1),
page 245, lie in Sigma-star. Read each disc there and draw its proper
connected star. Its boundary vertices are the prescribed part of the
partition. Since each star stays in its own disc, their supports are
pairwise disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Topological feasibility supplies a disjoint family of actual
proper connected forests in Sigma-star, with the prescribed boundary
vertex sets, for XII (3.1), page 245. -/
theorem exists_disjoint_feasibility_forests
    {S : Type*} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (Zs : Fin p → Set S) (hfin : ∀ j, (Zs j).Finite)
    (hZ : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i))
    (hfeasible : IsTopologicallyFeasible Δ Zs) :
    ∃ H : Fin p → Drawing (discComplement Δ),
      (∀ j, GM07.IsSurfaceForest (H j) ∧ IsConnectedDrawing (H j) ∧
        (H j).V ∩ bd (discComplement Δ) = Subtype.val ⁻¹' Zs j) ∧
      ∀ i j, i ≠ j → Disjoint (H i).U (H j).U := by
  classical
  let C := discComplement Δ
  obtain ⟨D, hD, hDD, hcontact⟩ := hfeasible
  have hDC : ∀ j, D j ⊆ C := fun j =>
    feasibility_disc_subset_discComplement hS Δ hΔ hdisj (hcontact j) (hZ j)
  have hlocal : ∀ j : Fin p, ∃ H : Drawing C,
      H.U ⊆ Subtype.val ⁻¹' D j ∧ GM07.IsSurfaceForest H ∧
      IsConnectedDrawing H ∧ H.V ∩ bd C = Subtype.val ⁻¹' Zs j := by
    intro j
    have hdisc := isClosedDisc_subtype_preimage (hDC j) (hD j)
    apply exists_proper_connected_forest_in_disc (discComplement_isSurface hS Δ hΔ hdisj)
      hdisc.1 ((hfin j).preimage Subtype.val_injective.injOn)
    · intro x hx
      have hxD : x.val ∈ D j := ((hcontact j).symm ▸ hx).1
      exact hxD
    · intro x hx
      rw [discComplement_boundary_eq hS Δ hΔ]
      exact hZ j hx
    · rintro x ⟨hxD, hxB⟩
      rw [discComplement_boundary_eq hS Δ hΔ] at hxB
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
      exact hcontact j ▸ (show x.val ∈ D j ∩ ⋃ i, Δ i from
        ⟨hxD, mem_iUnion.mpr ⟨i, discBd_subset _ hxi⟩⟩)
  choose H hHU hHF hHC hHV using hlocal
  refine ⟨H, fun j => ⟨hHF j, hHC j, hHV j⟩, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact Set.disjoint_left.mp (hDD i j hij) (hHU i hxi) (hHU j hxj)

end GraphMinor.GM12

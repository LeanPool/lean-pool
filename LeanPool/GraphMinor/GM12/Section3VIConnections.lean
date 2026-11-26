/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SubgraphDrawing
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM06.Section3Basic

/-!
# Returning a VI realization as connected subdrawings

The application of VI (3.6) in XII (3.2), page 247, supplies a
forest realization of the boundary partition. Each part belongs
to its own graph component. Read those components as subdrawings.
Their vertex sets are disjoint, and a component meets the full
prescribed vertex set exactly in its own part. Thus the realization
has precisely the connected-subdrawing conclusion of XII.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06 Graph

/-- A VI realization of nonempty disjoint partition parts gives
the connecting subdrawings required in XII (3.2), page 247. -/
theorem hasConnectingSubdrawings_of_vi_feasible
    {S : Type*} [TopologicalSpace S] [T1Space S] (Γ : Drawing S) {p : ℕ}
    (Zs : Fin p → Set S) (hne : ∀ i, (Zs i).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hf : GM06.IsFeasible Γ.toGraph (range Zs)) :
    HasConnectingSubdrawings Γ (⋃ j, Zs j) Zs := by
  obtain ⟨H, _, _, hHG, _, C, hCin, hC, _⟩ := hf
  have hZmem : ∀ j, Zs j ∈ range Zs := fun j => mem_range_self j
  have hZne : ∀ i j, i ≠ j → Zs i ≠ Zs j := by
    intro i j hij heq
    obtain ⟨x, hx⟩ := hne i
    exact Set.disjoint_left.mp (hdis i j hij) hx (heq ▸ hx)
  have hCne : ∀ i j, i ≠ j → C (Zs i) ≠ C (Zs j) :=
    fun i j hij heq => hZne i j hij (hCin (hZmem i) (hZmem j) heq)
  have hex : ∀ j, ∃ D : Drawing S, D.IsSubdrawing Γ ∧ D.V = (C (Zs j)).vertexSet ∧
      D.toGraph = C (Zs j) := fun j => exists_subdrawing_of_subgraph Γ (C (Zs j))
        ((hC (Zs j) (hZmem j)).1.1.trans hHG)
  choose D hsub hV hG using hex
  refine ⟨D, hsub, ?_, ?_, ?_⟩
  · intro j x hx y hy
    rw [hV] at hx hy
    have hconn := (hC (Zs j) (hZmem j)).1.2.1.2 x hx y hy
    change Nonempty (GraphWalk (D j).toGraph x y)
    rw [hG]
    exact hconn
  · intro i j hij
    rw [hV, hV]
    exact (hC (Zs i) (hZmem i)).1.disjoint_vertexSet_of_ne
      (hC (Zs j) (hZmem j)).1 (hCne i j hij)
  · intro j
    ext x
    constructor
    · rintro ⟨hxD, hxZ⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxZ
      by_cases hij : i = j
      · exact hij ▸ hxi
      · have hxCi := (hC (Zs i) (hZmem i)).2 hxi
        have hxCj : x ∈ (C (Zs j)).vertexSet := hV j ▸ hxD
        exact False.elim (Set.disjoint_left.mp
          ((hC (Zs i) (hZmem i)).1.disjoint_vertexSet_of_ne
            (hC (Zs j) (hZmem j)).1 (hCne i j hij)) hxCi hxCj)
    · intro hx
      exact ⟨(hV j).symm ▸ (hC (Zs j) (hZmem j)).2 hx, mem_iUnion.mpr ⟨j, hx⟩⟩

end GraphMinor.GM12

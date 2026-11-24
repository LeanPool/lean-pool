/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM12.Section73DiscPreprocess
import LeanPool.GraphMinor.GM12.Section72Regions
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.Surface.PlaneSeparation

/-!
# Components preserved by the disc reduction in XII (7.4)

The induction step on page 263 removes the inside of a normal
disc through the deleted vertex. After deleting that vertex, the
disc boundary misses the drawing. A connected component cannot
cross that boundary. Hence any component of the drawing outside
the disc was already a component before the disc reduction.
This proves the component assertion in the induction step.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Restriction across a boundary missing the whole set removes
components without splitting the components that remain. -/
theorem component_of_restriction_of_disjoint_frontier
    {S : Type*} [TopologicalSpace S] {U X C : Set S}
    (hX : IsClosed X) (hdis : Disjoint U (frontier X))
    (hC : C ∈ componentsIn (U ∩ X)) : C ∈ componentsIn U := by
  obtain ⟨x, hx, rfl⟩ := hC
  have hxC : x ∈ connectedComponentIn U x := mem_connectedComponentIn hx.1
  have hCX : connectedComponentIn U x ⊆ X := by
    apply subset_of_disjoint_frontier isPreconnected_connectedComponentIn hX
      (hdis.mono_left (connectedComponentIn_subset U x)) hxC hx.2
  have heq : connectedComponentIn (U ∩ X) x = connectedComponentIn U x := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans inter_subset_left)
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hxC
        (subset_inter (connectedComponentIn_subset U x) hCX)
  exact ⟨x, hx.1, heq.symm⟩

/-- Every component left after the one-vertex disc reduction and
vertex deletion is a component of the original vertex deletion,
as claimed in XII (7.4), page 263. -/
theorem component_after_normal_disc_reduction
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {D F C : Set S} {v : S}
    (hbd : subBd D = F) (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v})
    (hC : C ∈ componentsIn (deleteVertices (Γ.interSet (closure (univ \ D))) {v}).U) :
    C ∈ componentsIn (deleteVertices Γ {v}).U := by
  let N := deleteVertices Γ {v}
  let X := closure (univ \ D)
  have hfrD : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hfrX : frontier X ⊆ F := by
    change frontier (closure (univ \ D)) ⊆ F
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    exact frontier_interior_subset.trans hfrD.subset
  have hvnot : v ∉ N.U := by
    intro hvU
    have hvΓ : v ∈ Γ.V := (hFV.symm ▸ mem_singleton v).2
    have hvN := (isSubdrawing_U_inter_V (deleteVertices_isSubdrawing Γ {v})).subset ⟨hvU, hvΓ⟩
    exact ((deleteVertices_V Γ {v}).subset hvN).2 rfl
  have hdis : Disjoint N.U (frontier X) := by
    apply disjoint_left.mpr
    intro x hxN hxF
    have hxΓ : x ∈ Γ.U := (deleteVertices_isSubdrawing Γ {v}).U_subset hxN
    have hxv : x = v := by
      have hh : x ∈ F ∩ Γ.V := ⟨hfrX hxF, hn ⟨hfrX hxF, hxΓ⟩⟩
      rw [hFV] at hh
      exact hh
    exact hvnot (hxv ▸ hxN)
  have hNU : (N.interSet X).U = N.U ∩ X :=
    interSet_U_eq_of_normal_frontier isClosed_closure
      (fun x hx => False.elim (disjoint_left.mp hdis hx.2 hx.1))
  have hdelete := deleteVertices_interSet (Γ := Γ) (Z := ({v} : Set S))
    (X := closure (univ \ D)) isClosed_closure
  rw [hdelete, hNU] at hC
  exact component_of_restriction_of_disjoint_frontier isClosed_closure hdis hC

end GraphMinor.GM12

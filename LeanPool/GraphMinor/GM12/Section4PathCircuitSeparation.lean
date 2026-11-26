/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM12.Section4CircuitMeet

/-!
# A short radial circuit misses one of two disjoint path portions

In claim (1) of XII (4.3), pages 249--250, the two portions of the
path have disjoint vertex sets. A radial circuit with at most one
original vertex can meet at most one of these portions. The radial
intersection condition ensures that every meeting point is an original
vertex, so counting vertices suffices to separate the point sets.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The path separation step of XII (4.3), claim (1), pages 249--250. -/
theorem path_portion_disjoint_short_radial_circuit
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hC : C.IsSubdrawing K) (hcard : (C.V ∩ Γ.V).ncard ≤ 1)
    {a b c d : S} (P : GraphWalk Γ.toGraph a b) (Q : GraphWalk Γ.toGraph c d)
    (hPQ : Disjoint {z | z ∈ P.support} {z | z ∈ Q.support}) :
    Disjoint (walkDrawing Γ P).U C.U ∨ Disjoint (walkDrawing Γ Q).U C.U := by
  have meeting_vertex {x y : S} (W : GraphWalk Γ.toGraph x y) {z : S}
      (hzW : z ∈ (walkDrawing Γ W).U) (hzC : z ∈ C.U) :
      z ∈ W.support ∧ z ∈ C.V ∩ Γ.V := by
    have hzΓ : z ∈ Γ.U := (walkDrawing_isSubdrawing Γ W).U_subset hzW
    have hzK : z ∈ K.U := hC.U_subset hzC
    have hzV : z ∈ Γ.V := by
      have hi : z ∈ Γ.U ∩ K.U := ⟨hzΓ, hzK⟩
      change z ∈ (PaintingOrDrawing.drawing Γ).U ∩ K.U at hi
      rw [hK.2.1.1] at hi
      exact hi
    have hzKV : z ∈ K.V := hK.2.1.2.1 hzV
    have hzWV := subdrawing_vertex_of_mem_U (walkDrawing_isSubdrawing Γ W) hzW hzV
    rw [walkDrawing_V] at hzWV
    exact ⟨hzWV, subdrawing_vertex_of_mem_U hC hzC hzKV, hzV⟩
  by_cases hP : Disjoint (walkDrawing Γ P).U C.U
  · exact Or.inl hP
  right
  apply Set.disjoint_left.mpr
  intro y hyQ hyC
  have hy := meeting_vertex Q hyQ hyC
  apply hP
  apply Set.disjoint_left.mpr
  intro x hxP hxC
  have hx := meeting_vertex P hxP hxC
  have hfin : (C.V ∩ Γ.V).Finite := C.finite_V.subset inter_subset_left
  have hxy : x = y := (Set.ncard_le_one hfin).mp hcard x hx.2 y hy.2
  exact Set.disjoint_left.mp hPQ hx.1 (hxy.symm ▸ hy.1)

end GraphMinor.GM12

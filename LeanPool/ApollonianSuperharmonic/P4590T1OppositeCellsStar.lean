/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P4590T1OppositeCellsStar]

/-!
# P4590T1OppositeCellsStar

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1OppositeCellsStar (U V : ProtoTile) (x : GaussianInt)
    (hopp : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells ∧
      LatticeVertexIncidentCell x (j + 2) ∈ V.cells) :
    ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
      y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V := by
-- BODY
  obtain ⟨j, hj, hk⟩ := hopp
  have raw (W : ProtoTile) (a : GaussianInt) (ha : a ∈ W.cells)
      (y : GaussianInt)
      (hy : y = a ∨ y = a + 1 ∨ y = a + ⟨0, 1⟩ ∨
        y = a + 1 + ⟨0, 1⟩) : y ∈ FootprintVertices W := by
    simp only [FootprintVertices, show W.cells.Nonempty from ⟨a, ha⟩,
      ite_true, Set.mem_ofPred_eq]
    exact ⟨a, ha, hy⟩
  intro y hy
  fin_cases j <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl
  all_goals first
  | (left; apply raw U _ hj; simp [LatticeVertexIncidentCell,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm]; done)
  | (right; apply raw V _ hk; simp [LatticeVertexIncidentCell,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm]; )

end ApollonianSuperharmonic

end

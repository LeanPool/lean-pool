/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.CompleteCase

/-!
# The small-order Dross case

Below twenty vertices, the nine-tenths minimum-degree condition forces a
nonempty graph to be complete. The empty graph has the trivial decomposition.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dross's fractional triangle decomposition for graphs of order below twenty. -/
public theorem dross_fractional_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hlt : Fintype.card V < 20) : FractionalTriangleDecomp G := by
  by_cases hV : Fintype.card V = 0
  · have hEmpty : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    refine ⟨fun _ => 1, fun _ => by norm_num, ?_⟩
    intro e _
    rcases e with ⟨u, _⟩
    exact False.elim (hEmpty.false u)
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  have hbound : G.minDegree ≤ Fintype.card V - 1 :=
    (G.minDegree_le_degree v).trans (degree_le_card_sub_one G v)
  have hcard : 10 ≤ Fintype.card V := by omega
  have hmin : G.minDegree = Fintype.card V - 1 := by omega
  exact complete_fractional G hmin (by omega)

end LeanPool.DrossFractionalTriangleDecomposition

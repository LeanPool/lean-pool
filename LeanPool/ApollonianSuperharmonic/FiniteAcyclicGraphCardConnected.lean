/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: FiniteAcyclicGraphCardConnected]

/-!
# FiniteAcyclicGraphCardConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FiniteAcyclicGraphCardConnected
    {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (hacyclic : G.IsAcyclic)
    (hcard : Nat.card V = Nat.card G.edgeSet + 1) : G.Connected := by
-- BODY
  classical
  let topGraph : SimpleGraph V := ⊤
  obtain ⟨T, hGT, hT⟩ :=
    topGraph.exists_maximal_isAcyclic_of_le_isAcyclic le_top hacyclic
  have hTtree : T.IsTree := by
    apply (SimpleGraph.isTree_iff_maximal_isAcyclic (G := T)).2
    exact ⟨inferInstance, by simpa [topGraph] using hT⟩
  have hTcard : Nat.card T.edgeSet + 1 = Nat.card V :=
    (SimpleGraph.isTree_iff_connected_and_card (G := T)).1 hTtree |>.2
  have hEqCard : Nat.card T.edgeSet = Nat.card G.edgeSet := by
    omega
  let := Fintype.ofFinite T.edgeSet
  let := Fintype.ofFinite G.edgeSet
  have hsubset : G.edgeSet ⊆ T.edgeSet := by
    exact (SimpleGraph.edgeSet_subset_edgeSet).2 hGT
  have hcardle : Fintype.card T.edgeSet ≤ Fintype.card G.edgeSet := by
    simpa [Nat.card_eq_fintype_card] using hEqCard.le
  have hEqEdge : G.edgeSet = T.edgeSet :=
    Set.eq_of_subset_of_card_le hsubset hcardle
  have hgraphs : G = T := SimpleGraph.edgeSet_injective hEqEdge
  rw [hgraphs]
  exact hTtree.connected

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge

/-!
# Adjoining a missing-color edge

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Adjoining an edge with an earlier missing color preserves the Tashkinov-tree property. -/
theorem TashkinovTree.adjoinEdge {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi2 : PartialEdgeColoring E k) (S U : TreeSequence G e0) (f : E)
    (hadjoin : TreeSequenceAdjoinEdge S f U) (hS : TashkinovTree G e0 phi2 S)
    (c : Fin k) (hf : phi2 f = some c) (v : V) (hv : v ∈ TreeSequenceVertexSet S)
    (hmiss : c ∈ MissingColors G phi2 v) : TashkinovTree G e0 phi2 U := by
  classical
  rcases hadjoin with ⟨hlen, hinitial, hlast⟩
  rcases hinitial with ⟨hle, hvert, hedge⟩
  intro q hq
  by_cases hold : q.val < S.length
  · let qS : Fin S.length := ⟨q.val, hold⟩
    obtain ⟨a, color, hcolor, hcolorMissing⟩ :=
      hS qS hq
    let aU : Fin (q.val + 1) := ⟨a.val, a.isLt⟩
    refine ⟨aU, color, ?_, ?_⟩
    · have hqeq : Fin.castLE hle qS = q := by
        apply Fin.ext
        rfl
      have hUedge : U.edge q = S.edge qS := by
        rw [← hqeq]
        exact hedge qS
      rw [hUedge]
      exact hcolor
    · let oldVertexIndex : Fin (S.length + 1) :=
        Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ qS.isLt))
      let newVertexIndex : Fin (U.length + 1) :=
        Fin.castLT aU (Nat.lt_trans aU.isLt (Nat.succ_lt_succ q.isLt))
      have hindex : Fin.castLE (Nat.succ_le_succ hle) oldVertexIndex =
          newVertexIndex := by
        apply Fin.ext
        rfl
      have hvertex : U.vertex newVertexIndex = S.vertex oldVertexIndex := by
        rw [← hindex]
        exact hvert oldVertexIndex
      simpa [oldVertexIndex, newVertexIndex] using hvertex.symm ▸ hcolorMissing
  · have hqval : q.val = S.length := by
      have hqbound : q.val < S.length + 1 := by simpa [hlen] using q.isLt
      omega
    obtain ⟨a, ha⟩ : ∃ a : Fin (S.length + 1), S.vertex a = v := by
      simpa [TreeSequenceVertexSet] using hv
    let aU : Fin (q.val + 1) := ⟨a.val, by omega⟩
    refine ⟨aU, c, ?_, ?_⟩
    · have hqlast : q = Fin.cast hlen.symm (Fin.last S.length) := by
        apply Fin.ext
        simpa using hqval
      rw [hqlast, hlast]
      exact hf
    · let newVertexIndex : Fin (U.length + 1) :=
        Fin.castLT aU (Nat.lt_trans aU.isLt (Nat.succ_lt_succ q.isLt))
      have hindex : Fin.castLE (Nat.succ_le_succ hle) a =
          newVertexIndex := by
        apply Fin.ext
        rfl
      have hvertex : U.vertex newVertexIndex = v := by
        rw [← hindex, hvert a, ha]
      simpa [newVertexIndex, hvertex] using hmiss

end GoldbergSeymour

end

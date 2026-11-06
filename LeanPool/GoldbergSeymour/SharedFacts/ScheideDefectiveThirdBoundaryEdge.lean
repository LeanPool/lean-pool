/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveReturnData
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge

/-!
# Shared facts for ScheideDefectiveThirdBoundaryEdge

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ScheideDefectiveThirdBoundaryEdge

open scoped Sym2

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev tashkinovAdjoinStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
          G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
          T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (_ :
          ScheideDefectiveReturnData G k e0 phi T C D d) (rho : PartialEdgeColoring E k) (S U :
          TreeSequence G e0) (f : E), TreeSequenceAdjoinEdge S f U → TashkinovTree G e0 rho S →
      ∀ (c : Fin k), rho f = some c →
      ∀ v ∈ TreeSequenceVertexSet S, c ∈ MissingColors G rho v → TashkinovTree G e0 rho U

/-- A common proof used by the branches of this transport or construction argument. -/
theorem tashkinov_adjoin.{u_1, u_2} : tashkinovAdjoinStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R rho S U f hadjoin hS c hf v hv hmiss
  rcases hadjoin with ⟨hlen, hinitial, hlast⟩
  rcases hinitial with ⟨hle, hvert, hedge⟩
  intro q hq
  by_cases hold : q.val < S.length
  · let qS : Fin S.length := ⟨q.val, hold⟩
    obtain ⟨a, color, hcolor, hcolorMissing⟩ :=
      hS qS (by simpa [qS] using hq)
    let aU : Fin (q.val + 1) := ⟨a.val, by simpa [qS] using a.isLt⟩
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
      simpa [oldVertexIndex, newVertexIndex] using
        hvertex.symm ▸ hcolorMissing
  · have hqval : q.val = S.length := by
      have hqbound : q.val < S.length + 1 := by simpa [hlen] using q.isLt
      omega
    obtain ⟨a, ha⟩ : ∃ a : Fin (S.length + 1), S.vertex a = v := by
      simpa [TreeSequenceVertexSet] using hv
    let aU : Fin (q.val + 1) := ⟨a.val, by simpa [hqval] using a.isLt⟩
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

end GoldbergSeymour.SharedFacts.ScheideDefectiveThirdBoundaryEdge

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tree Sequence Boundary Edge Append Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TreeSequenceBoundaryEdgeAppendExists
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {e0 : E}
    (T : TreeSequence G e0) (f : E)
    (hf : f ∈ BoundaryEdges G (TreeSequenceVertexSet T)) :
    ∃ U : TreeSequence G e0, TreeSequenceAdjoinEdge T f U := by
  classical
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨x, hx, y, hy, hxy⟩ := hf
  have vertex_mem : ∀ i : Fin (T.length + 1),
      T.vertex i ∈ TreeSequenceVertexSet T := by
    intro i
    simp [TreeSequenceVertexSet]
  have edge_new : ∀ i : Fin T.length, f ≠ T.edge i := by
    intro i he
    obtain ⟨q, hq⟩ := T.attaches i
    have hyend : y ∈ G.ends (T.edge i) := by
      rw [← he, hxy]
      exact Sym2.mem_iff.mpr (Or.inr rfl)
    rw [hq] at hyend
    rcases Sym2.mem_iff.mp hyend with hqv | hqv
    · exact hy (by simpa [← hqv] using vertex_mem i.succ)
    · exact hy (by simpa [← hqv] using vertex_mem (Fin.castLT q (by omega)))
  let U : TreeSequence G e0 :=
    { length := T.length + 1
      positive := by omega
      vertex := Fin.lastCases y (fun i => T.vertex i)
      edge := Fin.lastCases f (fun i => T.edge i)
      vertex_injective := by
        intro i j
        revert j
        refine Fin.lastCases ?_ (fun i => ?_) i
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hij
            apply Fin.ext
            rfl
          · intro hij
            dsimp only [Fin.lastCases] at hij
            rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
            exact (hy (hij ▸ vertex_mem j)).elim
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hij
            dsimp only [Fin.lastCases] at hij
            rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
            exact (hy (hij ▸ vertex_mem i)).elim
          · intro hij
            dsimp only [Fin.lastCases] at hij
            rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
            exact congrArg Fin.castSucc (T.vertex_injective hij)
      edge_injective := by
        intro i j
        revert j
        refine Fin.lastCases ?_ (fun i => ?_) i
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hij
            apply Fin.ext
            rfl
          · intro hij
            dsimp only [Fin.lastCases] at hij
            rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
            exact False.elim (edge_new j hij)
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · intro hij
            dsimp only [Fin.lastCases] at hij
            rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
            exact False.elim (edge_new i hij.symm)
          · intro hij
            dsimp only [Fin.lastCases] at hij
            rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
            exact congrArg Fin.castSucc (T.edge_injective hij)
      first_edge := by
        have hzero : (⟨0, Nat.succ_pos _⟩ : Fin (T.length + 1)) =
            (⟨0, T.positive⟩ : Fin T.length).castSucc := by rfl
        rw [hzero]
        simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
        exact T.first_edge
      attaches := by
        intro j
        by_cases hj : j = Fin.last T.length
        · subst j
          obtain ⟨i, hi⟩ := by
            simpa [TreeSequenceVertexSet] using hx
          refine ⟨i, ?_⟩
          have hc : (Fin.castLT i (by omega) : Fin (T.length + 1 + 1)) =
              i.castSucc := by
            apply Fin.ext
            rfl
          rw [hc]
          simp only [Fin.lastCases_last, Fin.succ_last, Nat.succ_eq_add_one, Fin.lastCases_castSucc]
          rw [← hi] at hxy
          rw [hxy]
          exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, rfl⟩)
        · have hjle : j.val ≤ T.length := Nat.lt_succ_iff.mp j.isLt
          have hjne : j.val ≠ T.length := by
            intro he
            apply hj
            apply Fin.ext
            simpa using he
          have hj' : j.val < T.length := Nat.lt_of_le_of_ne hjle hjne
          obtain ⟨i, hi⟩ := T.attaches (j.castPred hj)
          have hjform : j = (j.castPred hj).castSucc := by
            apply Fin.ext
            rfl
          have hji : (j.castPred hj).val + 1 ≤ j.val + 1 := by
            rw [show (j.castPred hj).val = j.val by rfl]
          refine ⟨Fin.castLE hji i, ?_⟩
          convert hi using 1
          · apply congrArg G.ends
            conv_lhs => rw [hjform]
            simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
          · apply (Sym2.eq_iff).2
            left
            constructor
            · have hjs : j.succ = (j.castPred hj).succ.castSucc := by
                apply Fin.ext
                rfl
              rw [hjs]
              simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
            · have ibound : i.val < T.length + 1 := by omega
              have hq :
                  (Fin.castLE hji i).castLT (by omega) =
                    (i.castLT ibound).castSucc := by
                apply Fin.ext
                rfl
              rw [hq]
              simp only [Fin.lastCases, Fin.reverseInduction_castSucc] }
  refine ⟨U, ?_⟩
  refine ⟨by simp [U], ?_, ?_⟩
  · refine ⟨Nat.le_succ _, ?_, ?_⟩
    · intro i
      have hc : Fin.castLE (Nat.succ_le_succ (Nat.le_succ T.length)) i =
          i.castSucc := by
        apply Fin.ext
        rfl
      rw [hc]
      simp [U, Fin.lastCases, Fin.reverseInduction_castSucc]
    · intro j
      have hc : Fin.castLE (Nat.le_succ T.length) j = j.castSucc := by
        apply Fin.ext
        rfl
      rw [hc]
      simp [U, Fin.lastCases, Fin.reverseInduction_castSucc]
  · simp [U, Fin.lastCases]

end GoldbergSeymour

end

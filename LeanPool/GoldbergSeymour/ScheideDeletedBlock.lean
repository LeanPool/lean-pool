/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Tashkinov trees after removing a Scheide block

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Removing a block preserves the Tashkinov property under color agreement away from it. -/
theorem ScheideReducedConfiguration.tashkinovDeletedBlock {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k} {T : TreeSequence G e0}
    (C : ScheideReducedConfiguration G k e0 phi T) (removed : Fin C.s) (delta : Fin k)
    (deltaMember : delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (newColoring : PartialEdgeColoring E k) (shortTree : TreeSequence G e0)
    (lengthEqual : shortTree.length + 2 = T.length)
    (baseVertices : ∀ a : Fin C.p,
      ∃ q : Fin (shortTree.length + 1), q.val = a.val ∧ shortTree.vertex q = C.y a)
    (edgeCases : ∀ q : Fin shortTree.length,
      (∃ a : Fin (C.p - 1), q.val = a.val ∧ shortTree.edge q = C.baseEdge a) ∨
      ∃ (r : Fin C.s) (b : Fin 2), r ≠ removed ∧ C.p - 1 ≤ q.val ∧
        shortTree.edge q = C.blockEdge r b)
    (htreeOld : TashkinovTree G e0 phi T)
    (unusedDefective : Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T))
      (TreeUsedColors phi T))
    (edgeColorAgreement : ∀ (q : Fin T.length) (c : Fin k),
      phi (T.edge q) = some c → newColoring (T.edge q) = some c)
    (missingUnaffected : ∀ v ∈ TreeSequenceVertexSet T, ∀ c : Fin k,
      c ≠ C.gamma removed → c ≠ delta →
        (c ∈ MissingColors G newColoring v ↔ c ∈ MissingColors G phi v)) :
    TashkinovTree G e0 newColoring shortTree := by
  classical
  let X := TreeSequenceVertexSet T
  intro q hq
  rcases edgeCases q with
    ⟨a, hqa, hqe⟩ | ⟨r, b, hri, hqbase, hqe⟩
  · have haPos : 1 ≤ a.val := by omega
    let oldq : Fin T.length := ⟨a.val, by omega⟩
    obtain ⟨w, c, hc, hm⟩ := htreeOld oldq haPos
    have hwP : w.val < C.p := by
      have hw := w.isLt
      dsimp [oldq] at hw
      omega
    let wp : Fin C.p := ⟨w.val, hwP⟩
    obtain ⟨ws, hwsval, hws⟩ := baseVertices wp
    have hwq : w.val < q.val + 1 := by
      have hw := w.isLt
      dsimp [oldq] at hw
      omega
    let wn : Fin (q.val + 1) := ⟨w.val, hwq⟩
    have hcast : Fin.castLT wn
        (Nat.lt_trans wn.isLt (Nat.succ_lt_succ q.isLt)) = ws := by
      apply Fin.ext
      simpa [wn] using hwsval.symm
    have holdedge : T.edge oldq = C.baseEdge a := by
      simpa [oldq] using C.base_edge_position a
    have hcbase : phi (C.baseEdge a) = some c := holdedge ▸ hc
    have hcGamma : c ≠ C.gamma removed :=
      C.initial_nonfirst_avoids_blocks a haPos c hcbase removed
    have hcUsed : c ∈ TreeUsedColors phi T := by
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨oldq, haPos, hc⟩
    have hcDelta : c ≠ delta := by
      intro heq
      exact (Finset.disjoint_left.mp unusedDefective) deltaMember (heq ▸ hcUsed)
    refine ⟨wn, c, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edgeColorAgreement oldq c hc
    · rw [hcast, hws]
      have hvwpX : C.y wp ∈ X := by
        rw [← C.base_vertex_position wp]
        simp [X, TreeSequenceVertexSet]
      have holdvertex : T.vertex
          (Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ oldq.isLt))) =
          C.y wp := by
        have hidx : Fin.castLT w
            (Nat.lt_trans w.isLt (Nat.succ_lt_succ oldq.isLt)) =
            (⟨wp.val, by omega⟩ : Fin (T.length + 1)) := by
          apply Fin.ext
          rfl
        rw [hidx]
        exact C.base_vertex_position wp
      have hmwp : c ∈ MissingColors G phi (C.y wp) := by
        simpa only [holdvertex] using hm
      exact (missingUnaffected (C.y wp) hvwpX c hcGamma hcDelta).mpr hmwp
  · obtain ⟨w, hwmissing⟩ := C.block_color_missing_on_base r
    obtain ⟨ws, hwsval, hws⟩ := baseVertices w
    let wn : Fin (q.val + 1) := ⟨w.val, by omega⟩
    have hcast : Fin.castLT wn
        (Nat.lt_trans wn.isLt (Nat.succ_lt_succ q.isLt)) = ws := by
      apply Fin.ext
      simpa [wn] using hwsval.symm
    have hrgamma : C.gamma r ≠ C.gamma removed := by
      intro h
      exact hri (C.gamma_injective h)
    let oldq : Fin T.length := ⟨C.p - 1 + 2 * r.val + b.val, by
      have hr := r.isLt
      have hb := b.isLt
      have hlen := C.length_eq
      omega⟩
    have hrdelta : C.gamma r ≠ delta := by
      intro h
      have hused : delta ∈ TreeUsedColors phi T := by
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨oldq, by
          have hp := C.p_ge_two
          simp [oldq]
          omega, ?_⟩
        rw [show T.edge oldq = C.blockEdge r b by
          simpa [oldq] using C.block_edge_position r b]
        simpa [h] using C.block_color r b
      exact (Finset.disjoint_left.mp unusedDefective) deltaMember hused
    have holdedge : T.edge oldq = C.blockEdge r b := by
      simpa only [oldq] using C.block_edge_position r b
    have hcold : phi (T.edge oldq) = some (C.gamma r) := by
      rw [holdedge]
      exact C.block_color r b
    refine ⟨wn, C.gamma r, ?_, ?_⟩
    · rw [hqe, ← holdedge]
      exact edgeColorAgreement oldq (C.gamma r) hcold
    · rw [hcast, hws]
      exact (missingUnaffected (C.y w) (by
        rw [← C.base_vertex_position w]
        simp [TreeSequenceVertexSet])
        (C.gamma r) hrgamma hrdelta).mpr hwmissing

end GoldbergSeymour

end

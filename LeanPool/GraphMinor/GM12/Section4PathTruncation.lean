/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic

/-!
# Removing the last vertex of a path

XII (4.4), page 252, deletes the last vertex of each external path
and retains its incident edge as a joining edge. Reverse a simple
walk tracing the path. Its first edge is the retained joining edge,
and the remaining walk traces the shortened path. Simplicity
excludes the removed vertex and joining edge from that remainder.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface GM09

/-- The path truncation used in XII (4.4), page 252. The shortened
path has exactly the old vertices except the terminal vertex, and
exactly the old edges except its incident terminal edge. -/
theorem exists_path_without_last_vertex
    {α β : Type*} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ (Q : Graph α β) (e : β) (x : α),
      IsGraphPathWithEnds G Q a x ∧ Q ≤ P ∧
      Q.vertexSet = P.vertexSet \ {b} ∧ Q.edgeSet = P.edgeSet \ {e} ∧
      G.IsLink e x b ∧ e ∈ P.edgeSet ∧ b ∉ Q.vertexSet := by
  obtain ⟨hPG, W, hW, hV, hE⟩ := hP
  have hVr : P.vertexSet = {z | z ∈ W.reverse.support} := by
    rw [hV]
    ext z
    simp only [mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse]
  have hEr : P.edgeSet = {e | e ∈ W.reverse.edges} := by
    rw [hE]
    ext e
    simp only [mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse]
  have hWr := hW.reverse
  cases hrev : W.reverse with
  | nil hb => exact False.elim (hab rfl)
  | @cons b x a e hl R =>
    rw [hrev] at hVr hEr hWr
    have hR : R.IsSimple := hWr.of_cons
    have hbR : b ∉ R.support := (List.nodup_cons.mp hWr).1
    have heR : e ∉ R.edges := fun he => hbR (walk_isLink_mem_support R he hl).1
    let Q := walkSubgraph R
    have hQ : IsGraphPathWithEnds P Q x a := isGraphPathWithEnds_walkSubgraph hR
    refine ⟨Q, e, x, hQ.symm.mono hPG, hQ.1, ?_, ?_, hl.symm.mono hPG, hl.edge_mem, ?_⟩
    · rw [hVr, vertexSet_walkSubgraph]
      ext z
      simp only [GraphWalk.support_cons, mem_ofPred_eq, List.mem_cons, mem_sdiff,
        mem_singleton_iff]
      constructor
      · intro hz
        exact ⟨Or.inr hz, fun hzb => hbR (hzb ▸ hz)⟩
      · rintro ⟨hz, hzb⟩
        exact hz.resolve_left hzb
    · rw [hEr, edgeSet_walkSubgraph]
      ext f
      simp only [GraphWalk.edges_cons, mem_ofPred_eq, List.mem_cons, mem_sdiff,
        mem_singleton_iff]
      constructor
      · intro hf
        exact ⟨Or.inr hf, fun hfe => heR (hfe ▸ hf)⟩
      · rintro ⟨hf, hfe⟩
        exact hf.resolve_left hfe
    · simpa only [Q, vertexSet_walkSubgraph, mem_ofPred_eq] using hbR

end GraphMinor.GM12

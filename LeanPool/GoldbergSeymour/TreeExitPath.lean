/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Tree Exit Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- A simple two-color path of length at least two meeting the tree only at its inside endpoint,
with a missing color outside.
-/
def TreeExitPath {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (u v : V)
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)) : Prop :=
  p.IsPath ∧
    2 ≤ p.length ∧
      u ∉ TreeSequenceVertexSet T ∧
        v ∈ TreeSequenceVertexSet T ∧
          (alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) ∧
            ∀ w ∈ TreeSequenceVertexSet T, (Sum.inl w ∈ p.support ↔ w = v)

/-- Clip a simple two-color walk at its first visit to the actual tree vertex set. -/
theorem TreeExitPath.firstEntry {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {u v : V}
    (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v))
    (path : P.IsPath)
    (missing : alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u)
    (outside : u ∉ TreeSequenceVertexSet T)
    (meets : ∃ x ∈ TreeSequenceVertexSet T, Sum.inl x ∈ P.support) :
    ∃ (c : V) (_ : c ∈ TreeSequenceVertexSet T) (member : Sum.inl c ∈ P.support),
      TreeExitPath T phi alpha beta u c (P.takeUntil (Sum.inl c) member) := by
  classical
  let S : Finset (Sum V E) := (TreeSequenceVertexSet T).image Sum.inl
  obtain ⟨z, hzS, hzP, first⟩ :=
    P.exists_mem_support_forall_mem_support_imp_eq S (by
      obtain ⟨x, hxT, hxP⟩ := meets
      exact ⟨Sum.inl x, by simp [S, hxT, hxP]⟩)
  obtain ⟨c, inside, hcz⟩ : ∃ c, c ∈ TreeSequenceVertexSet T ∧ Sum.inl c = z := by
    simpa [S] using hzS
  subst z
  let Q := P.takeUntil (Sum.inl c) hzP
  have only : ∀ w ∈ TreeSequenceVertexSet T, (Sum.inl w ∈ Q.support ↔ w = c) := by
    intro w hw
    constructor
    · intro member
      exact Sum.inl.inj (first (Sum.inl w) (by simp [S, hw]) member)
    · rintro rfl
      exact Q.end_mem_support
  have different : u ≠ c := by rintro rfl; exact outside inside
  have length : 2 ≤ Q.length := by
    have positive : 0 < Q.length := by
      apply Nat.pos_of_ne_zero
      intro zero
      exact different (Sum.inl.inj (SimpleGraph.Walk.length_eq_zero_iff.mp zero).eq)
    by_contra short
    have one : Q.length = 1 := by omega
    have adjacent := Q.adj_getVert_succ (i := 0) (by omega)
    have endpoint : Q.getVert 1 = Sum.inl c := by
      have last := Q.getVert_length
      rwa [one] at last
    rw [Q.getVert_zero, endpoint] at adjacent
    exact adjacent.elim
  exact ⟨c, inside, hzP, path.takeUntil _, length, outside, inside, missing, only⟩

/-- The last edge of an exit path crosses the tree boundary from an outside vertex. -/
theorem TreeExitPath.lastBoundaryEdge {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {u v : V}
    {P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)}
    (exit : TreeExitPath T phi alpha beta u v P) :
    ∃ (edge : E) (other : V),
      P.getVert (P.length - 1) = Sum.inr edge ∧ Sum.inr edge ∈ P.support ∧
      Incident G v edge ∧ Incident G other edge ∧ other ∉ TreeSequenceVertexSet T ∧
      edge ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧
      (phi edge = some alpha ∨ phi edge = some beta) := by
  classical
  have length := exit.2.1
  have adjacent := P.adj_getVert_succ (i := P.length - 1) (by omega)
  rw [show P.length - 1 + 1 = P.length by omega, P.getVert_length] at adjacent
  cases last : P.getVert (P.length - 1) with
  | inl w => rw [last] at adjacent; exact adjacent.elim
  | inr edge =>
    rw [last] at adjacent
    have data : Incident G v edge ∧ (phi edge = some alpha ∨ phi edge = some beta) := adjacent
    have previous := P.adj_getVert_succ (i := P.length - 2) (by omega)
    rw [show P.length - 2 + 1 = P.length - 1 by omega, last] at previous
    cases before : P.getVert (P.length - 2) with
    | inr f => rw [before] at previous; exact previous.elim
    | inl other =>
      rw [before] at previous
      have incident : Incident G other edge := previous.1
      have outside : other ∉ TreeSequenceVertexSet T := by
        intro inside
        have endpoint := (exit.2.2.2.2.2 other inside).mp (by
          rw [← before]
          exact P.getVert_mem_support (P.length - 2))
        have equal : P.getVert (P.length - 2) = P.getVert P.length := by
          rw [before, endpoint, P.getVert_length]
        have := exit.1.getVert_injOn (Nat.sub_le _ _) (by simp) equal
        omega
      have different : v ≠ other := by intro h; exact outside (h ▸ exit.2.2.2.1)
      have ends : G.ends edge = s(v, other) :=
        (Sym2.mem_and_mem_iff different).mp ⟨data.1, incident⟩
      have boundary : edge ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨v, exit.2.2.2.1, other, outside, ends⟩
      refine ⟨edge, other, rfl, ?_, data.1, incident, outside, boundary, data.2⟩
      rw [← last]
      exact P.getVert_mem_support (P.length - 1)

end GoldbergSeymour

end

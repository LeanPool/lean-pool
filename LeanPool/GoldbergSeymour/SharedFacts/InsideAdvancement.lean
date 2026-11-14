/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTailColorFacts

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for HierarchySituationOneAdvanceInsideStored

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.InsideAdvancement

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev tailExceptionStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    (∀ R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = A) →
    TreeSequenceInitialSegment A T → ∀ hlen : 4 ≤ T.length,
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
      HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j) →
    (∀ R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1) = B) →
    (∀ R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
    1 ≤ j → j < T.length - A.length → ∀ c ∈ MissingColors G R.coloring
      ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length)),
    ∀ t : Fin T.length, A.length ≤ t.val → t.val < A.length + j →
    R.coloring (T.edge t) = some c →
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      c ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds)


/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev consecutiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base) (_ : ℕ)
        (_ : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C),
      let A : TreeSequence G e0 :=
        HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
      ∀ (t : Fin T.length) (_ : A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ)),
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem tailException.{u_1, u_2} : tailExceptionStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq hAT hlen B fullEq fullB
    elementary R j positive bound color missing t lower upper colored
  apply R.counterexample.hierarchy.tailMissingColorIncident
    (by rw [starEq R]; exact hAT)
    (by
      change ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)))
      rw [fullB R]
      exact elementary R) j positive
    (by rw [starEq R]; exact bound) color
    (by
      change color ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix R.counterexample j).vertex
        (Fin.last (HierarchyFullTailPrefix R.counterexample j).length))
      rw [fullEq R]
      exact missing) t
    (by simpa only [starEq R] using lower)
    (by simpa only [starEq R] using upper) colored


/-- A common proof used by the branches of this transport or construction argument. -/
theorem consecutive.{u_1, u_2} : consecutiveStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C i hpathUpper A t ht
  clear * - G T A C t ht hpathUpper
  let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  have hp : HierarchyPathNumber C.hierarchy =
      (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) := rfl
  have hn : candidates.Nonempty := by
    by_contra hn
    rw [dite_eq_right hn] at hp
    have hu : HierarchyPathNumber C.hierarchy < T.length - A.length := hpathUpper
    omega
  have hm : candidates.min' hn = HierarchyPathNumber C.hierarchy := by
    simpa only [dite_eq_left hn] using hp.symm
  have hh := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  rw [hm] at hh
  exact hh t ht

end GoldbergSeymour.SharedFacts.InsideAdvancement

end

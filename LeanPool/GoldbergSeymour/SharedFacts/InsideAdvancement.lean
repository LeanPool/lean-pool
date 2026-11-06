/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
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
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (_ : (
      ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
          TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)),
      let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
          C.hierarchy.dividerCount);
      ∀ (_ : (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStarredStage R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount) = A)) (_ : TreeSequenceInitialSegment A T) (hlen
          : (4 : ℕ) ≤ T.length),
      let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
          (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
      by omega
      ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
      by omega
      );
      ∀ (_ : TreeSequenceInitialSegment B T) (_ : (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
          HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j)) (_ : (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
          ℕ)) = B)) (_ : (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B))) (_ : (
      ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
          U)) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ :
          (1 : ℕ) ≤ j) (_ : j < T.length - A.length),
      ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
          (HierarchyFullTailPrefix C j).length)),
      ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
          some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
          R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
          R.corresponding.replacementETT.series.data (Fin.last
          R.corresponding.replacementETT.rounds)

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
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i trans A starEq hAT hlen B hBT fullEq
      fullB elementary vertexMem R j hj hjlt c hc t hlo hhi hcol
  clear * - R j hj hjlt c hc t hlo hhi hcol starEq hAT hBT fullEq fullB elementary vertexMem
  let U := HierarchyFullTailPrefix R.counterexample j
  have hUlen : U.length = A.length + j := by
    simp only [U, HierarchyFullTailPrefix, TreeSequencePrefix]
    rw [starEq R]
    exact min_eq_left (by have := hAT.1; omega)
  have hUT : TreeSequenceInitialSegment U T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  let u : Fin U.length := ⟨t.val, by rw [hUlen]; omega⟩
  have hut : Fin.castLE hUT.1 u = t := Fin.ext rfl
  have hcU : c ∈ MissingColors G R.coloring (U.vertex (Fin.last U.length)) := by
    dsimp only [U]
    rw [fullEq R]
    exact hc
  have hcolU : R.coloring (U.edge u) = some c := by
    rw [← hUT.2.2 u, hut]; exact hcol
  have hex := HierarchyTailMissingColorExclusion G k e0 R.corresponding.replacementInput T
    R.coloring R.corresponding.replacementETT R.replacementBase R.counterexample.hierarchy
    (by
      change ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)))
      rw [fullB R]
      exact elementary R)
    j hj (by
      rw [starEq R]
      exact hjlt) c hcU u
    (by
      change (HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).length ≤ t.val
      rw [starEq R]
      exact hlo)
    (by
      change t.val < (HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).length + j
      rw [starEq R]
      exact hhi) hcolU
  obtain ⟨hzero, hcore, hval, f, hstep, hkind, hedges, hedge, hcF, hstored⟩ := hex
  have hAval : t.val = A.length := by
    change u.val = _ at hval
    rw [starEq R] at hval
    exact hval
  have hAn : A = R.corresponding.replacementETT.series.data.tree
      (Fin.last R.corresponding.replacementETT.rounds).castSucc := by
    rw [← starEq R]
    have hs : HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = R.replacementBase.core := by
      simp [HierarchyStarredStage, hzero, Fin.last]
    exact hs.trans hcore
  obtain ⟨i, hi⟩ := T.attaches t
  let a : Fin (A.length + 1) := ⟨i.val, by simpa only [hAval] using i.isLt⟩
  let old : Fin (T.length + 1) :=
    Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt))
  have ha : Fin.castLE (Nat.succ_le_succ hAT.1) a = old := Fin.ext rfl
  refine ⟨⟨T.vertex old, ?_, ?_⟩, hstored⟩
  · rw [← hAn, ← ha, hAT.2.1 a]
    exact vertexMem A a
  · rw [Incident, hi]
    exact Sym2.mem_mk_right _ _

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

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for HierarchySituationTwoSubcaseOneTwo

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.FirstSubcaseTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev bTStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
          B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment B T

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev sameStarStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStarredStage P.counterexample.hierarchy (Fin.last
          P.counterexample.hierarchy.dividerCount) = A

/-- A common proof used by the branches of this transport or construction argument. -/
theorem bT.{u_1, u_2} : bTStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C B hBlen
  refine ⟨?_, ?_, ?_⟩
  · omega
  · intro i
    rfl
  · intro i
    rfl

/-- A common proof used by the branches of this transport or construction argument. -/
theorem sameStar.{u_1, u_2} : sameStarStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx H q A P
  have helper :
    ∀ (n m : ℕ) (X Y : TreeSequence G e0) (s : Fin (n + 2) → TreeSequence G e0) (t : Fin (m + 2) →
        TreeSequence G e0), n = m → X = Y → HEq s t → Fin.cases (motive := fun _ => TreeSequence G
        e0) X (fun i : Fin n => s i.succ.castSucc) (Fin.last n) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) Y (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
    intro n m X Y s t hnm hXY hst
    subst m
    have he := eq_of_heq hst
    simp [hXY, he]
  exact (helper _ _ base.core P.replacementBase.core H.stage
    P.counterexample.hierarchy.stage P.sameGood.1.2.1 P.sameGood.1.1
    P.sameGood.1.2.2.1).symm

end GoldbergSeymour.SharedFacts.FirstSubcaseTransport

end

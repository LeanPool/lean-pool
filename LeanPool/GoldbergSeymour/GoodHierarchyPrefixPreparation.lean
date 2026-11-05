/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy

/-!
# Good Hierarchy Prefix Repackage

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

namespace GoodHierarchyPrefix

theorem helper_segmentTrans_64.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
        C → TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  rcases hAB with ⟨hab, hvab, heab⟩
  rcases hBC with ⟨hbc, hvbc, hebc⟩
  refine ⟨le_trans hab hbc, ?_, ?_⟩
  · intro i
    have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
    simpa using hmid.trans (hvab i)
  · intro i
    have hmid := hebc (Fin.castLE hab i)
    simpa using hmid.trans (heab i)

theorem helper_stageSegment_77.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (_ : Fin (H.dividerCount + (1 : ℕ))),
    (∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A) →
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
      (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r segmentRefl segmentTrans a d
  induction d with
  | zero =>
      intro hbound
      simpa using segmentRefl (H.stage ⟨a, by omega⟩)
  | succ d ih =>
      intro hbound
      have hprev := ih (by omega)
      have hnext := H.nested ⟨a + d, by omega⟩
      have hnext' : TreeSequenceInitialSegment
          (H.stage ⟨a + d, by omega⟩)
          (H.stage ⟨a + (d + 1), by omega⟩) := by
        simpa [Nat.add_assoc] using hnext
      exact segmentTrans hprev hnext'

theorem helper_prefixEqOfSegment_95.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {A B : TreeSequence G e0} (hAB : TreeSequenceInitialSegment A B),
    A = TreeSequencePrefix B A.length A.positive hAB.1 := by
  classical
  intro V E G e0 A B hAB
  cases A with
  | mk la pa va ea via eia fea aa =>
    cases B with
    | mk lb pb vb eb vib eib feb ab =>
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa [TreeSequencePrefix] using (hAB.2.1 i).symm
      · apply heq_of_eq
        funext i
        simpa [TreeSequencePrefix] using (hAB.2.2 i).symm

theorem helper_firstToPrefix_111.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (r : Fin (H.dividerCount + (1 : ℕ))),
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    let Tp : TreeSequence G e0 := H.stage r.castSucc;
    TreeSequenceInitialSegment
      (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))) Tp := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r stageSegment Tp
  change TreeSequenceInitialSegment
    (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tp
  rw [← H.baseStage]
  have hs := stageSegment 0 r.val (by omega)
  convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> simp

theorem helper_prefixToTerminal_118.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (r : Fin (H.dividerCount + (1 : ℕ))),
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    let Tp : TreeSequence G e0 := H.stage r.castSucc;
    TreeSequenceInitialSegment Tp T := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r stageSegment Tp
  have hs := stageSegment r.val (H.dividerCount + 1 - r.val) (by omega)
  have hind : r.val + (H.dividerCount + 1 - r.val) =
      H.dividerCount + 1 := by omega
  have hidx : (⟨r.val + (H.dividerCount + 1 - r.val), by omega⟩ :
      Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
    Fin.ext hind
  rw [hidx, H.terminalStage] at hs
  convert hs using 1
  apply congrArg H.stage
  apply Fin.ext
  rfl

theorem helper_hidx_141.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
        G k e0 input T generating) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett
        base) (r : Fin (H.dividerCount + (1 : ℕ))) (hr : (1 : ℕ) ≤ (↑r : ℕ)),
    let Tp : TreeSequence G e0 := H.stage r.castSucc; H.stage (⟨(1 : ℕ) + ((↑r : ℕ) - (1 : ℕ)),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = Tp := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r hr Tp
  dsimp [Tp]
  apply congrArg H.stage
  apply Fin.ext
  simp
  omega

theorem helper_branch_233.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
        G k e0 input T generating) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett
        base) (_ : Fin (H.dividerCount + (1 : ℕ))) {A B : TreeSequence G e0} (hAB :
        TreeSequenceInitialSegment A B) (eta : Fin k) (i : Fin (A.length + (1 : ℕ))), (↑i : ℕ) <
        A.length →
    let candidatesA : Finset (Fin (A.length + (1 : ℕ))) :=
        ({x : Fin (A.length + (1 : ℕ)) | eta ∈ MissingColors G phi (A.vertex x)} : Finset (Fin
        (A.length + (1 : ℕ))));
    let candidatesB : Finset (Fin (B.length + (1 : ℕ))) :=
        ({x : Fin (B.length + (1 : ℕ)) | eta ∈ MissingColors G phi (B.vertex x)} : Finset (Fin
        (B.length + (1 : ℕ)))); (↑i : ℕ) < (↑(if h : candidatesA.Nonempty then candidatesA.min' h
        else Fin.last A.length) : ℕ) → candidatesB.Nonempty → (↑(Fin.castLE (Nat.succ_le_succ
        hAB.1) i) : ℕ) < (↑(if h : candidatesB.Nonempty then candidatesB.min' h else Fin.last
        B.length) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r A B hAB eta i hiEnd candidatesA
      candidatesB hi hB
  rw [dite_eq_left hB]
  by_contra hnot
  have hle : (candidatesB.min' hB).val ≤ i.val := by simpa using hnot
  let ia : Fin (A.length + 1) :=
    ⟨(candidatesB.min' hB).val, by omega⟩
  have hmemB := Finset.min'_mem candidatesB hB
  have hmissingB : eta ∈ MissingColors G phi
      (B.vertex (candidatesB.min' hB)) :=
    (Finset.mem_filter.mp hmemB).2
  have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) ia =
      candidatesB.min' hB := Fin.ext rfl
  have hmissingA : eta ∈ MissingColors G phi (A.vertex ia) := by
    rw [← hAB.2.1 ia, hcast]
    exact hmissingB
  have hmemA : ia ∈ candidatesA :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmissingA⟩
  by_cases hA : candidatesA.Nonempty
  · rw [dite_eq_left hA] at hi
    have hminA := Finset.min'_le candidatesA ia hmemA
    change (candidatesA.min' hA).val ≤ ia.val at hminA
    dsimp [ia] at hminA
    omega
  · exact hA ⟨ia, hmemA⟩

theorem helper_terminalClosed_412.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
      (r : Fin (H.dividerCount + (1 : ℕ))) (hr : (1 : ℕ) ≤ (↑r : ℕ)),
    let _ : Fin H.dividerCount := (⟨(↑r : ℕ) - (1 : ℕ), by omega⟩ : Fin H.dividerCount);
    TreeColorSetMinusClosed G phi (H.stage r.castSucc)
      ((HierarchyStoredColorsAt H r).biUnion
        (good.gamma (⟨(↑r : ℕ) - (1 : ℕ), by omega⟩ : Fin (H.dividerCount + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H good r hr lastInternal
  have hold := good.minusClosed lastInternal
  have hs : lastInternal.succ = r := by
    apply Fin.ext
    dsimp [lastInternal]
    omega
  rw [hs] at hold
  simpa [lastInternal] using hold

theorem helper_beforeFirstMissing_386.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
        G k e0 input T generating) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett
        base) (_ : Fin (H.dividerCount + (1 : ℕ))) {A B : TreeSequence G e0} (hAB :
        TreeSequenceInitialSegment A B) (eta : Fin k) (i : Fin (A.length + (1 : ℕ))) (_ : (↑i : ℕ)
        < A.length) (_ : (↑i : ℕ) < (↑(HierarchyFirstMissingPosition phi A eta) : ℕ)),
    let iB : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hAB.1) i; (↑iB : ℕ) <
        (↑(HierarchyFirstMissingPosition phi B eta) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r A B hAB eta i hiEnd hi
  let candidatesA : Finset (Fin (A.length + 1)) :=
    Finset.univ.filter fun x => eta ∈ MissingColors G phi (A.vertex x)
  let candidatesB : Finset (Fin (B.length + 1)) :=
    Finset.univ.filter fun x => eta ∈ MissingColors G phi (B.vertex x)
  change i.val < (if h : candidatesA.Nonempty then candidatesA.min' h
    else Fin.last A.length).val at hi
  change (Fin.castLE (Nat.succ_le_succ hAB.1) i).val <
    (if h : candidatesB.Nonempty then candidatesB.min' h
    else Fin.last B.length).val
  by_cases hB : candidatesB.Nonempty
  · exact helper_branch_233 (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base)
      (@H) (@r) (@hAB) (@eta) (@i) (@hiEnd) (@hi) (@hB)
  · rw [dite_eq_right hB]
    simpa using lt_of_lt_of_le hiEnd hAB.1

theorem helper_strictAbovePenultimate_337.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
        G k e0 input T generating) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett
        base) (r : Fin (H.dividerCount + (1 : ℕ))) (_ : (1 : ℕ) ≤ (↑r : ℕ)) (_ :
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))),
    let Tp : TreeSequence G e0 := H.stage r.castSucc; (ett.series.data.tree (⟨ett.rounds,
    by
              omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))).length < Tp.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r hr stageSegment Tp
  change (ett.series.data.tree
    (Fin.last ett.rounds).castSucc).length < Tp.length
  rw [← H.baseStage]
  have hfirst := H.strict (0 : Fin (H.dividerCount + 1))
  have hrest := (stageSegment 1 (r.val - 1) (by omega)).1
  have hidx : H.stage ⟨1 + (r.val - 1), by omega⟩ = Tp := by
    exact helper_hidx_141 (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H)
        (@r) (@hr)
  rw [hidx] at hrest
  apply lt_of_lt_of_le hfirst
  exact hrest

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperTerminalStage419Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
        G k e0 input T generating) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett
        base) (r : Fin (H.dividerCount + (1 : ℕ))) (hr : (1 : ℕ) ≤ (↑r : ℕ)),
    let Tp : TreeSequence G e0 := H.stage r.castSucc; H.stage (⟨(↑(Fin.last ((↑r : ℕ) - (1 : ℕ) +
        (1 : ℕ))) : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = Tp

theorem helper_terminalStage_419.{u_1, u_2} :
    helperTerminalStage419Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H r hr Tp
  dsimp [Tp]
  apply congrArg H.stage
  apply Fin.ext
  simp
  omega

end GoodHierarchyPrefix

end GoldbergSeymour

end

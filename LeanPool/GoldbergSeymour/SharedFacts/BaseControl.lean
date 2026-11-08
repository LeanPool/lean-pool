/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Shared facts for BaseControl

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.BaseControl

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev transStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
          {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W
          Z → TreeSequenceInitialSegment U Z

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev stageChainStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy; (
      ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
          → TreeSequenceInitialSegment U Z) →
      ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
          j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
          ℕ))))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev branchStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      ∀ {u : V}, ett.rounds = (1 : ℕ) → u ∈ TreeSequenceVertexSet Tn →
      ∀ {v : V}, v ∈ TreeSequenceVertexSet Tn → u ≠ v → Disjoint (MissingColors G
          (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
      have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
          - (1 : ℕ) < ett.rounds) ↦
      by
                    omega
      ⟩ : Fin ett.rounds).castSucc) u) (MissingColors G (ett.series.data.coloring (⟨ett.rounds - (1
          : ℕ),
      have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
          - (1 : ℕ) < ett.rounds) ↦
      by
                    omega
      ⟩ : Fin ett.rounds).castSucc) v)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem trans.{u_1, u_2} : transStatement.{u_1, u_2} := by
  intro V E G e0 U W Z hUW hWZ
  exact hUW.trans hWZ


/-- A common proof used by the branches of this transport or construction argument. -/
theorem stageChain.{u_1, u_2} : stageChainStatement.{u_1, u_2} := by
  intro V E _ _ _ _ G k e0 input T phi ett base C H trans last bound first ordered
  exact H.stageInitialSegmentOfLE first ⟨last, bound⟩ ordered


/-- A common proof used by the branches of this transport or construction argument. -/
theorem branch.{u_1, u_2} : branchStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C n Tn _ hn
  have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc =
    0 :=
    Fin.ext (by simp [hn])
  have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
    Fin.ext (by simp [n, hn])
  dsimp only [Tn]
  rw [hcolor, htree]
  exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1

end GoldbergSeymour.SharedFacts.BaseControl

end

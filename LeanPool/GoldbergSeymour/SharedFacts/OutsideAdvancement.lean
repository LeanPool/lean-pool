/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for HierarchySituationOneAdvanceOutsideStored

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.OutsideAdvancement

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstMissingPositionUpperBoundStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
        (k : ℕ) (e0 : E) (T : TreeSequence G e0) (psi : PartialEdgeColoring E k) (c : Fin k)
        (j : Fin (T.length + (1 : ℕ))),
      c ∈ MissingColors G psi (T.vertex j) →
      HierarchyFirstMissingPosition psi T c ≤ j

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev lastDataStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
      HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount) ∧
        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
          C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
            R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev gammaTransportStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), C.good.gamma
          (Fin.last C.hierarchy.dividerCount) eta = R.counterexample.good.gamma (Fin.last
          R.counterexample.hierarchy.dividerCount) eta) →
      ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
      ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
          S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
          R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev gammaUnusedStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
      let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
          C.hierarchy.dividerCount); (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStarredStage R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount) = A) →
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k),
          eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
          R.counterexample.hierarchy.dividerCount) eta →
      ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑(HierarchyFirstMissingPosition
          R.coloring T eta) : ℕ) → R.coloring (T.edge t) ≠ some a

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev notRawStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
      let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
          C.hierarchy.dividerCount); (
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStarredStage R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount) = A) →
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
      ∀ c ∉ TreeMissingColors R.coloring A, c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) → c ∉ TashkinovStoredColors
          R.corresponding.replacementETT.series.data (Fin.last
          R.corresponding.replacementETT.rounds)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev gammaChoiceStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
      ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
      ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
          R.counterexample.hierarchy.dividerCount),
      ∀ (f : E),
      ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
          R.coloring f ≠ some a

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev sameLastStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) {a b : ℕ} (s : Fin (a +
          (2 : ℕ)) → TreeSequence G e0) (t : Fin (b + (2 : ℕ)) → TreeSequence G e0) (u v :
          TreeSequence G e0), a = b → s ≍ t → u = v → (Fin.cases u (fun (i : Fin a) ↦ s
          i.castSucc.succ) (Fin.last a) : TreeSequence G e0) = (Fin.cases v (fun (i : Fin b) ↦ t
          i.castSucc.succ) (Fin.last b) : TreeSequence G e0)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstMissingPositionUpperBound.{u_1, u_2} :
    firstMissingPositionUpperBoundStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 T psi c j hj
  let _ := Fintype.ofFinite V
  let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
    c ∈ MissingColors G psi (T.vertex j)
  have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hn : candidates.Nonempty := ⟨j, hm⟩
  unfold HierarchyFirstMissingPosition
  rw [dite_eq_left hn]
  exact Finset.min'_le candidates j hm

/-- A common proof used by the branches of this transport or construction argument. -/
theorem lastData.{u_1, u_2} : lastDataStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx R
  obtain ⟨hcount, hdata⟩ := R.sameGood.2
  have hh := hdata (Fin.last C.hierarchy.dividerCount)
  have hidx : Fin.cast (congrArg (fun q => q + 1) hcount)
      (Fin.last C.hierarchy.dividerCount) =
      Fin.last R.counterexample.hierarchy.dividerCount := Fin.ext hcount
  simpa only [hidx] using hh

/-- A common proof used by the branches of this transport or construction argument. -/
theorem gammaTransport.{u_1, u_2} : gammaTransportStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx lastData R S eta heta
  have hOrig : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)
     := by
    rw [(lastData R).1]; exact heta
  refine ⟨?_, ((lastData R).2 eta hOrig).symm.trans ((lastData S).2 eta hOrig)⟩
  rw [← (lastData S).1]
  exact hOrig

/-- A common proof used by the branches of this transport or construction argument. -/
theorem gammaUnused.{u_1, u_2} : gammaUnusedStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq R eta a heta ha t hlo hhi hc
  have hnot := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance
    (Fin.last R.counterexample.hierarchy.dividerCount) eta heta ha)).2
  apply hnot
  unfold HierarchySegmentColors
  dsimp only
  rw [starEq R, Fin.succ_last, R.counterexample.hierarchy.terminalStage]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo,
    lt_min hhi t.isLt, hc⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem notRaw.{u_1, u_2} : notRawStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq R c hcA hcD hm
  apply hcD
  unfold HierarchyStoredColorsAt
  dsimp only
  rw [starEq R]
  exact Finset.mem_sdiff.mpr ⟨hm, hcA⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem gammaChoice.{u_1, u_2} : gammaChoiceStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx R eta heta f
  by_contra hn
  push Not at hn
  have hc : (R.counterexample.good.gamma
      (Fin.last R.counterexample.hierarchy.dividerCount) eta).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((hn a ha).symm.trans (hn b hb))
  rw [R.counterexample.good.twoColors _ eta heta] at hc
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem sameLast.{u_1, u_2} : sameLastStatement.{u_1, u_2} := by
  classical
  intro V E G e0 a b s t u v hab hst huv
  cases hab
  have he : s = t := eq_of_heq hst
  cases he
  cases huv
  rfl

end GoldbergSeymour.SharedFacts.OutsideAdvancement

end

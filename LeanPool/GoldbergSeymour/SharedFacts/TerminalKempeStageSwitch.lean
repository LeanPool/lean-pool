/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for TerminalKempeStageSwitch

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.TerminalKempeStageSwitch

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hsoneStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (R :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (a b : Fin k), a ≠ b →
      let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
          (T.vertex (Fin.last T.length))); IsOneEdgeUncolored sigma e0

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hsone.{u_1, u_2} : hsoneStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx R a b hne sigma
  refine ⟨?_, ?_⟩
  · simp [sigma, TwoColorComponentSwap, R.minimumContext.oneEdgeUncolored.1]
  · intro e he
    obtain ⟨c, hc⟩ := R.minimumContext.oneEdgeUncolored.2 e he
    by_cases hm : Sum.inr e ∈ TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))
    · by_cases hca : c = a
      · subst c; exact ⟨b, by simp [sigma, TwoColorComponentSwap, hm, hc]⟩
      · by_cases hcb : c = b
        · subst c; exact ⟨a, by simp [sigma, TwoColorComponentSwap, hm, hc, hne.symm]⟩
        · exact ⟨c, by simp [sigma, TwoColorComponentSwap, hm, hc, hca, hcb]⟩
    · exact ⟨c, by simp [sigma, TwoColorComponentSwap, hm, hc]⟩

end GoldbergSeymour.SharedFacts.TerminalKempeStageSwitch

end

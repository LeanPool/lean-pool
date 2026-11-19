/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyNonparallelBaseTransport
public import LeanPool.GoldbergSeymour.SameHierarchyStages

/-!
# Nonparallel correspondence of hierarchy stages

Generalized from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Transport the actual hierarchy stages along a nonparallel correspondence. -/
def TashkinovHierarchy.ofNonparallelCorresponding {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input phi sigma : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
    (hierarchy : TashkinovHierarchy ett base)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) :
    TashkinovHierarchy corr.replacementETT (base.ofNonparallelCorresponding corr nonparallel) := by
  have terminalTree := corr.terminalData.1
  exact {
    dividerCount := hierarchy.dividerCount
    stage := hierarchy.stage
    baseStage := hierarchy.baseStage.trans terminalTree.symm
    terminalStage := hierarchy.terminalStage
    nested := hierarchy.nested
    strict := hierarchy.strict
    dividerPosition := hierarchy.dividerPosition
    dividerPositive := hierarchy.dividerPositive
    dividerIncreasing := hierarchy.dividerIncreasing
    dividerStage := hierarchy.dividerStage
    coreInsideFirst := hierarchy.coreInsideFirst }

/-- The transported nonparallel hierarchy preserves its stages and divider positions. -/
theorem TashkinovHierarchy.sameStagesOfNonparallelCorresponding {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input phi sigma : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
    (hierarchy : TashkinovHierarchy ett base)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) :
    SameHierarchyStages hierarchy (hierarchy.ofNonparallelCorresponding corr nonparallel) := by
  have terminalKind := corr.terminalData.2.1
  refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
  · exact ⟨fun h => (nonparallel h).elim,
      fun h => (nonparallel (terminalKind.symm.trans h)).elim⟩
  · intro h
    exact (nonparallel h).elim

/-- A nonparallel correspondence transports the base and the actual hierarchy stages. -/
theorem TashkinovHierarchy.nonparallelCorrespondence {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input phi sigma : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
    (hierarchy : TashkinovHierarchy ett base)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) :
    ∃ (newBase : HierarchyBase corr.replacementETT sigma)
      (replacement : TashkinovHierarchy corr.replacementETT newBase),
      SameHierarchyStages hierarchy replacement := by
  exact ⟨base.ofNonparallelCorresponding corr nonparallel,
    hierarchy.ofNonparallelCorresponding corr nonparallel,
    hierarchy.sameStagesOfNonparallelCorresponding corr nonparallel⟩

end GoldbergSeymour

end

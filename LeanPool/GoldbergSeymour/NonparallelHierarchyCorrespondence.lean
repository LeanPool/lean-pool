/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData
public import LeanPool.GoldbergSeymour.SameHierarchyStages

/-!
# Nonparallel correspondence of hierarchy stages

Generalized from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

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
  classical
  have terminalTree := corr.terminalData.1
  have terminalKind := corr.terminalData.2.1
  let position := Fin.cast
    (congrArg (fun tree : TreeSequence G e0 => tree.length + 1) terminalTree.symm)
    base.supportPosition
  let newBase : HierarchyBase corr.replacementETT sigma := {
    core := base.core
    closure := base.closure
    supportPosition := position
    supportPositive := by simpa only [position, Fin.val_cast] using base.supportPositive
    terminalMissingColors := rfl
    parallel := by
      dsimp only
      intro h
      exact (nonparallel (terminalKind.symm.trans h)).elim
    nonparallel := by
      dsimp only
      intro _
      exact (base.nonparallel nonparallel).trans terminalTree.symm }
  let replacement : TashkinovHierarchy corr.replacementETT newBase := {
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
  refine ⟨newBase, replacement, rfl, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
  · exact ⟨fun h => (nonparallel h).elim,
      fun h => (nonparallel (terminalKind.symm.trans h)).elim⟩
  · intro h
    exact (nonparallel h).elim

end GoldbergSeymour

end

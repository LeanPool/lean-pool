/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData
public import LeanPool.GoldbergSeymour.HierarchyBase

/-!
# Transporting a nonparallel hierarchy base

Shared from the credited Trellis stable-change proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. Corresponding terminal metadata supplies
the support-position cast while preserving the actual core and closure.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A corresponding nonparallel tree preserves the core, closure and support position. -/
def HierarchyBase.ofNonparallelCorresponding {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} (base : HierarchyBase ett phi)
    {U : TreeSequence G e0} (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠ some TashkinovExtensionKind.PE) :
    HierarchyBase corr.replacementETT sigma := by
  have terminal := CorrespondingExtendedTashkinovTree.terminalTreeKind G k e0 sigma ett U corr
  let position : Fin ((corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
    Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) terminal.1.symm)
      base.supportPosition
  exact {
    core := base.core
    closure := base.closure
    supportPosition := position
    supportPositive := by simpa only [position, Fin.val_cast] using base.supportPositive
    terminalMissingColors := rfl
    parallel := fun kind => (nonparallel (terminal.2.symm.trans kind)).elim
    nonparallel := fun _ => (base.nonparallel nonparallel).trans terminal.1.symm }

end GoldbergSeymour

end

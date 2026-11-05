/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovHierarchy

/-!
# Same Hierarchy Stages

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Agreement of hierarchy cores, stages, dividers and parallel-extension closure data. -/
def SameHierarchyStages {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input₁ input₂ : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {generating₁ generating₂ phi₁ phi₂ : PartialEdgeColoring E k}
  {ett₁ : ExtendedTashkinovTree G k e0 input₁ T generating₁}
  {ett₂ : ExtendedTashkinovTree G k e0 input₂ T generating₂} {base₁ : HierarchyBase ett₁ phi₁}
  {base₂ : HierarchyBase ett₂ phi₂} (H₁ : TashkinovHierarchy ett₁ base₁)
  (H₂ : TashkinovHierarchy ett₂ base₂) : Prop :=
 let pe₁ := ett₁.series.data.kind (Fin.last ett₁.rounds) = some TashkinovExtensionKind.PE
 let pe₂ := ett₂.series.data.kind (Fin.last ett₂.rounds) = some TashkinovExtensionKind.PE
 base₁.core = base₂.core ∧
  H₁.dividerCount = H₂.dividerCount ∧
   HEq H₁.stage H₂.stage ∧
    HEq H₁.dividerPosition H₂.dividerPosition ∧ (pe₁ ↔ pe₂) ∧ (pe₁ → base₁.closure = base₂.closure)

end GoldbergSeymour

end

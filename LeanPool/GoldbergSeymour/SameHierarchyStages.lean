/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.HierarchyStarredStage

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

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {T : TreeSequence G e0}
    {input₁ input₂ input₃ generating₁ generating₂ generating₃ phi₁ phi₂ phi₃ :
      PartialEdgeColoring E k}
    {ett₁ : ExtendedTashkinovTree G k e0 input₁ T generating₁}
    {ett₂ : ExtendedTashkinovTree G k e0 input₂ T generating₂}
    {ett₃ : ExtendedTashkinovTree G k e0 input₃ T generating₃}
    {base₁ : HierarchyBase ett₁ phi₁} {base₂ : HierarchyBase ett₂ phi₂}
    {base₃ : HierarchyBase ett₃ phi₃}
    {hierarchy₁ : TashkinovHierarchy ett₁ base₁}
    {hierarchy₂ : TashkinovHierarchy ett₂ base₂}
    {hierarchy₃ : TashkinovHierarchy ett₃ base₃}

/-- Agreement of hierarchy stages composes across independent colorings and bases. -/
theorem SameHierarchyStages.trans (first : SameHierarchyStages hierarchy₁ hierarchy₂)
    (second : SameHierarchyStages hierarchy₂ hierarchy₃) :
    SameHierarchyStages hierarchy₁ hierarchy₃ := by
  refine ⟨first.1.trans second.1, first.2.1.trans second.2.1,
    first.2.2.1.trans second.2.2.1, first.2.2.2.1.trans second.2.2.2.1,
    first.2.2.2.2.1.trans second.2.2.2.2.1, ?_⟩
  intro parallel
  exact (first.2.2.2.2.2 parallel).trans
    (second.2.2.2.2.2 (first.2.2.2.2.1.mp parallel))

/-- Stage agreement evaluates at the canonical cast of any target index. -/
theorem SameHierarchyStages.stage_eq (same : SameHierarchyStages hierarchy₁ hierarchy₂)
    (index : Fin (hierarchy₂.dividerCount + 2)) :
    hierarchy₂.stage index = hierarchy₁.stage
      (Fin.cast (congrArg (fun count => count + 2) same.2.1.symm) index) := by
  have evaluate {r s : ℕ} (equal : r = s) (first : Fin r → TreeSequence G e0)
      (second : Fin s → TreeSequence G e0) (agreement : HEq first second) (position : Fin r) :
      second (Fin.cast equal position) = first position := by
    cases equal
    cases agreement
    rfl
  exact (evaluate _ hierarchy₂.stage hierarchy₁.stage same.2.2.1.symm index).symm

/-- Starred stages agree after transporting the index by the divider-count equality. -/
theorem SameHierarchyStages.starredStage_eq (same : SameHierarchyStages hierarchy₁ hierarchy₂)
    (index : Fin (hierarchy₂.dividerCount + 1)) :
    HierarchyStarredStage hierarchy₂ index = HierarchyStarredStage hierarchy₁
      (Fin.cast (congrArg (fun count => count + 1) same.2.1.symm) index) := by
  refine Fin.cases ?_ (fun position => ?_) index
  · simpa only [Fin.cast_zero, HierarchyStarredStage, Fin.cases_zero] using same.1.symm
  · simpa only [Fin.cast_succ_eq, Fin.cast_castSucc, HierarchyStarredStage, Fin.cases_succ]
      using same.stage_eq position.succ.castSucc

/-- The last ordinary stages agree without exposing their dependent index proofs. -/
theorem SameHierarchyStages.lastOrdinaryStage_eq
    (same : SameHierarchyStages hierarchy₁ hierarchy₂) :
    hierarchy₂.stage (Fin.last hierarchy₂.dividerCount).castSucc =
      hierarchy₁.stage (Fin.last hierarchy₁.dividerCount).castSucc :=
  (same.stage_eq _).trans (congrArg hierarchy₁.stage (Fin.ext same.2.1.symm))

/-- The final starred stages agree after the divider-count transport. -/
theorem SameHierarchyStages.lastStarredStage_eq
    (same : SameHierarchyStages hierarchy₁ hierarchy₂) :
    HierarchyStarredStage hierarchy₂ (Fin.last hierarchy₂.dividerCount) =
      HierarchyStarredStage hierarchy₁ (Fin.last hierarchy₁.dividerCount) :=
  (same.starredStage_eq _).trans
    (congrArg (HierarchyStarredStage hierarchy₁) (Fin.ext same.2.1.symm))

end GoldbergSeymour

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages

/-!
# Same Good Hierarchy

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Agreement of hierarchy stages, stored colors and the auxiliary color pairs after transporting
indices.
-/
def SameGoodHierarchy {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input₁ input₂ : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {generating₁ generating₂ phi₁ phi₂ : PartialEdgeColoring E k}
  {ett₁ : ExtendedTashkinovTree G k e0 input₁ T generating₁}
  {ett₂ : ExtendedTashkinovTree G k e0 input₂ T generating₂} {base₁ : HierarchyBase ett₁ phi₁}
  {base₂ : HierarchyBase ett₂ phi₂} {H₁ : TashkinovHierarchy ett₁ base₁}
  {H₂ : TashkinovHierarchy ett₂ base₂} (good₁ : GoodHierarchy H₁) (good₂ : GoodHierarchy H₂) :
  Prop :=
 SameHierarchyStages H₁ H₂ ∧
  ∃ hcount : H₁.dividerCount = H₂.dividerCount,
   ∀ j : Fin (H₁.dividerCount + 1),
    let j₂ : Fin (H₂.dividerCount + 1) := Fin.cast (congrArg (fun q => q + 1) hcount) j
    HierarchyStoredColorsAt H₁ j = HierarchyStoredColorsAt H₂ j₂ ∧
     ∀ eta ∈ HierarchyStoredColorsAt H₁ j, good₁.gamma j eta = good₂.gamma j₂ eta

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

/-- Agreement of the auxiliary color pairs composes after the canonical index casts. -/
theorem SameGoodHierarchy.trans
    {good₁ : GoodHierarchy hierarchy₁} {good₂ : GoodHierarchy hierarchy₂}
    {good₃ : GoodHierarchy hierarchy₃}
    (first : SameGoodHierarchy good₁ good₂) (second : SameGoodHierarchy good₂ good₃) :
    SameGoodHierarchy good₁ good₃ := by
  rcases first with ⟨firstStages, firstCount, firstColors⟩
  rcases second with ⟨secondStages, secondCount, secondColors⟩
  refine ⟨firstStages.trans secondStages, firstCount.trans secondCount, ?_⟩
  intro index
  have castIndex :
      Fin.cast (congrArg (fun count => count + 1) (firstCount.trans secondCount)) index =
        Fin.cast (congrArg (fun count => count + 1) secondCount)
          (Fin.cast (congrArg (fun count => count + 1) firstCount) index) := by
    apply Fin.ext
    simp only [Fin.val_cast]
  obtain ⟨firstStored, firstGamma⟩ := firstColors index
  obtain ⟨secondStored, secondGamma⟩ := secondColors
    (Fin.cast (congrArg (fun count => count + 1) firstCount) index)
  dsimp only at firstStored firstGamma secondStored secondGamma ⊢
  rw [castIndex]
  exact ⟨firstStored.trans secondStored, fun color member =>
    (firstGamma color member).trans (secondGamma color (firstStored ▸ member))⟩

end GoldbergSeymour

end

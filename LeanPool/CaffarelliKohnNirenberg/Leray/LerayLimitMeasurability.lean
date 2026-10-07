/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Leray Limit Measurability

Supporting estimates for the Navier–Stokes development.
-/

public section

open Set

noncomputable section

namespace CKN.Leray

/-- Fields continuous on complementary measurable regions define a measurable
piecewise field, as used for extensions in `prop:leray-limit`. -/
theorem lerayLimit_measurableOn_extension
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (s : Set α)
    [∀ x : α, Decidable (x ∈ s)] (hs : MeasurableSet s)
    (f g : α → β) (hf : ContinuousOn f s) (hg : ContinuousOn g sᶜ) :
    Measurable (s.piecewise f g) := by
  classical
  exact hf.measurable_piecewise hg hs

end CKN.Leray

end

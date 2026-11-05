/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Coloring properties of certified Tashkinov series

Every stage is proper and leaves exactly the distinguished edge uncolored.
Derived from the certificates in Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Every certified step preserves the two basic coloring properties. -/
theorem TashkinovSeriesStep.coloringProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {data : TashkinovSeriesData G k rounds e0}
    {i : Fin (rounds + 1)} (step : TashkinovSeriesStep G k rounds e0 input data i) :
    IsProperEdgeColoring G (data.coloring i) ∧ IsOneEdgeUncolored (data.coloring i) e0 := by
  cases step with
  | initial triple _ coloring _ _ _ _ _ _ _ _ =>
      rw [coloring]
      exact triple.2.2.2
  | SE _ _ _ _ _ _ choice _ coloring _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [coloring]
      exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
  | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ proper one _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨proper, one⟩
  | RE _ proper one _ _ _ coloring _ _ _ _ _ _ _ _ _ _ _ _ =>
      rw [coloring]
      exact ⟨proper, one⟩

/-- Every stage of a certified series is proper and has one uncolored edge. -/
theorem TashkinovSeries.coloringProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (i : Fin (rounds + 1)) :
    IsProperEdgeColoring G (series.data.coloring i) ∧
      IsOneEdgeUncolored (series.data.coloring i) e0 :=
  (series.certified i).coloringProperties

end GoldbergSeymour

end

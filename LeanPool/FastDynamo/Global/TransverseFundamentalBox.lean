/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartL2Operators
public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus

/-!
# The fundamental box of the transverse quotient carries the transverse measure

`pairUnitIocBox = (0,1]²` (`FastDynamo/Analysis/LiteralThreeTorus.lean`) is the pair-coordinate
form of `TorusChartL2.rawFundamentalBox` (`FastDynamo/Global/TorusChartL2Operators.lean`).  This
module is the one place where the two are compared: pairing the two raw coordinates is measure
preserving between the restricted Lebesgue measures, and composing with
`TorusChartL2.measurePreserving_rawTorusPoint` shows that `transverseTorusPoint` carries Lebesgue
measure restricted to `(0,1]²` to the normalised transverse volume.

Consumed by `FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean`; nothing here refers to the
velocity, to a flow or to a parameter.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- Pairing the two raw coordinates carries Lebesgue measure restricted to
`TorusChartL2.rawFundamentalBox` to Lebesgue measure restricted to `pairUnitIocBox`. -/
theorem measurePreserving_finTwoArrow_pairUnitIocBox :
    MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ)
      (volume.restrict TorusChartL2.rawFundamentalBox) (volume.restrict pairUnitIocBox) := by
  have hmp := (volume_preserving_finTwoArrow ℝ).restrict_preimage measurableSet_pairUnitIocBox
  have hpre : (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ) ⁻¹' pairUnitIocBox
      = TorusChartL2.rawFundamentalBox := by
    ext x
    simp only [pairUnitIocBox, Set.mem_preimage, Set.mem_prod,
      MeasurableEquiv.finTwoArrow_apply, TorusChartL2.rawFundamentalBox,
      ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate.iocFundamentalBox,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzero, hone⟩ k
      fin_cases k <;> simpa using ‹_›
    · intro hx
      exact ⟨by simpa using hx 0, by simpa using hx 1⟩
  rwa [hpre] at hmp

/-- **The transverse quotient map is measure preserving on the fundamental box.**  Restricting
Lebesgue measure to `(0,1]²` and projecting to `TransverseTorus` gives the normalized transverse
volume.  This is the pair-coordinate form of `TorusChartL2.measurePreserving_rawTorusPoint`. -/
theorem measurePreserving_transverseTorusPoint :
    MeasurePreserving transverseTorusPoint (volume.restrict pairUnitIocBox) transverseMeasure := by
  have hsymm := measurePreserving_finTwoArrow_pairUnitIocBox.symm MeasurableEquiv.finTwoArrow
  have hcomp := TorusChartL2.measurePreserving_rawTorusPoint.comp hsymm
  have hfun : TorusChartL2.rawTorusPoint ∘
      (MeasurableEquiv.finTwoArrow.symm : ℝ × ℝ → (Fin 2 → ℝ)) = transverseTorusPoint := by
    funext x
    funext j
    fin_cases j <;> rfl
  rwa [hfun] at hcomp

end

end FastDynamo

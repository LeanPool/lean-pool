/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDuhamelSemigroup
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesRealification

/-!
# Real heat evolution as a continuous linear operator

The real Fourier heat map is bounded and therefore commutes with
Bochner integration on finite intervals.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The real heat operator as a bounded real-linear map on spatial L². -/
@[expose]
def realHeatOperatorCLM (t : ℝ) (ht : 0 ≤ t) :
    RealVectorL2 →L[ℝ] RealVectorL2 :=
  realPartVectorL2.comp
    ((heatSemigroupCLM t ht).restrictScalars ℝ |>.comp complexifyVectorL2)

/-- The bounded real-linear heat map agrees with the Fourier definition. -/
theorem realHeatOperatorCLM_apply
    (t : ℝ) (ht : 0 ≤ t) (b : RealVectorL2) :
    realHeatOperatorCLM t ht b = realHeatOperator t ht b := by
  simp [realHeatOperatorCLM, heatSemigroupCLM_apply, realHeatOperator]

end CKN.Leray

end

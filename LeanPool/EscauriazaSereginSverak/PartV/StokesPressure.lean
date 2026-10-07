/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices

/-!
# Pressure for a forced Stokes equation

The pressure of a tensor forcing is the negative of its canonical double
Riesz transform, as in `lem:pv-stokes`.
-/

public section

open CKN

open MeasureTheory
open scoped ENNReal


noncomputable section

namespace ESS

/-- The canonical pressure paired with a space-time tensor forcing. -/
@[expose] def pvStokesPressure (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → CKN.Foundation.Parabolic.ParabolicPoint → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure CKN.Foundation.Parabolic.ParabolicPoint)) :
    CKN.Foundation.Parabolic.ParabolicPoint → ℝ :=
  -CKN.Leray.rieszPressureSpaceTime r hr F hF

end ESS

end

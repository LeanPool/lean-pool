/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The normalised Haar measure on the torus

Mathlib's Fourier analysis on the torus `𝕋^d = UnitAddTorus d` uses
`Mathlib.Analysis.Fourier.AddCircleMulti` and works with the probability Haar measure
`AddCircle.haarAddCircle` on each circle factor. A local instance makes it the measure `volume`.
Outside that file,
the global instance `AddCircle.measureSpace` applies instead, whose `volume` is equal but not
definitionally equal, so `L_2(𝕋^d)` would be a different type from the one carrying Mathlib's
Fourier basis `UnitAddTorus.mFourierBasis`.

This file makes Mathlib's instance available as a **scoped instance**: after
`open scoped TorusHaar`, `volume` on `UnitAddCircle` and on `UnitAddTorus d` is the
normalised Haar measure of Mathlib's Fourier theory.  It also records that this measure is a
Haar probability measure, which gives (through Mathlib's product instances) a probability
measure on `𝕋^d` charging every nonempty open set.
-/

@[expose] public section

open MeasureTheory

namespace TorusHaar

attribute [scoped instance] instMeasureSpaceUnitAddCircle

end TorusHaar

open scoped TorusHaar

/-- The normalised Haar measure on the circle is a Haar measure. -/
instance TorusHaar.isAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The normalised Haar measure on the circle is a probability measure. -/
instance TorusHaar.isProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace TorusHaar

variable (d : Type*) [Fintype d]

/-- The scoped measure on the circle is Mathlib's normalised Haar measure. -/
theorem volume_eq_haarAddCircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle :=
  rfl

example : IsProbabilityMeasure (volume : Measure (UnitAddTorus d)) := inferInstance
example : (volume : Measure (UnitAddTorus d)).IsOpenPosMeasure := inferInstance
example : BorelSpace (UnitAddTorus d) := inferInstance
example : CompactSpace (UnitAddTorus d) := inferInstance

end TorusHaar

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicCompleted.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicUniform
public import Mathlib.MeasureTheory.Measure.NullMeasurable
/-!
# Alternative Bakry Emery Brownian dyadic completed

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianDyadicCompletedPath_measurable`, `bakryBrownianDyadic_completed_map`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous paths `C(Icc 0 1, ℝ)`, used locally in this file. -/
local instance bakryBrownianCompletedPathMeasurable :
    MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
local instance bakryBrownianCompleted_pathBorel :
    BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

/-- The dyadic Gaussian sample space with its σ-algebra completed with respect to
`bakryBrownianDyadicMeasure`. -/
abbrev BakryBrownianDyadicCompletedSample :=
  NullMeasurableSpace BakryBrownianDyadicSample bakryBrownianDyadicMeasure

/-- The completion of the dyadic Gaussian measure `bakryBrownianDyadicMeasure`. -/
def bakryBrownianDyadicCompletedMeasure : Measure BakryBrownianDyadicCompletedSample :=
  bakryBrownianDyadicMeasure.completion

instance : IsProbabilityMeasure bakryBrownianDyadicCompletedMeasure :=
  ⟨by change bakryBrownianDyadicMeasure univ = 1; exact measure_univ⟩

instance : bakryBrownianDyadicCompletedMeasure.IsComplete :=
  Measure.completion.isComplete _

/-- The dyadic Brownian path `bakryBrownianDyadicPath`, read on the completed sample space. -/
def bakryBrownianDyadicCompletedPath (ω : BakryBrownianDyadicCompletedSample) : C(Icc (0 : ℝ) 1, ℝ)
    :=
  bakryBrownianDyadicPath ω

theorem bakryBrownianDyadicCompletedPath_measurable : Measurable bakryBrownianDyadicCompletedPath :=
  bakryBrownianDyadicPath_aemeasurable.nullMeasurable.measurable'

/-- Completing the actual Gaussian sample space preserves every measurable
finite-dimensional law, including the almost-everywhere series limit. -/
theorem bakryBrownianDyadic_completed_map {E : Type*} [MeasurableSpace E]
    (f : BakryBrownianDyadicSample → E) (hf : AEMeasurable f bakryBrownianDyadicMeasure) :
    bakryBrownianDyadicCompletedMeasure.map (fun ω : BakryBrownianDyadicCompletedSample => f ω) =
      bakryBrownianDyadicMeasure.map f := by
  ext s hs
  rw [Measure.map_apply hf.nullMeasurable.measurable' hs,
    Measure.map_apply_of_aemeasurable hf hs]
  rfl

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltKilledMapping.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltOUSurvival

/-!
# Ginibre Brownian integral tilt killed mapping

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualTiltedKilledPath_map`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

/-- Measurable-mapping reduction for an actual killed coupling. Restricting
the tilted measure to literal survival and pushing the coupled original path
produces precisely the reference path weighted by the terminal action on
survival. No stochastic law or survival identity is supplied by this lemma. -/
theorem actualTiltedKilledPath_map {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (d e : Ω → ℝ≥0∞) (S : Set Ω) (hS : MeasurableSet S)
    (X Y : Ω → E)
    (hXY : ∀ᵐ ω ∂P.withDensity d, ω ∈ S → X ω = Y ω)
    (hde : ∀ᵐ ω ∂P, ω ∈ S → d ω = e ω) :
    ((P.withDensity d).restrict S).map X=(P.withDensity (S.indicator e)).map Y := by
  have hPath : X=ᵐ[(P.withDensity d).restrict S] Y :=
    (ae_restrict_iff' hS).mpr hXY
  rw [Measure.map_congr hPath, restrict_withDensity hS,← withDensity_indicator hS]
  have hDensity : S.indicator d=ᵐ[P] S.indicator e := by
    filter_upwards [hde] with ω hω
    by_cases hmem : ω∈S
    · simp only [indicator_of_mem hmem]
      exact hω hmem
    · simp only [indicator_of_notMem hmem]
  rw [withDensity_congr_ae hDensity]

end
end GinibrePoincare

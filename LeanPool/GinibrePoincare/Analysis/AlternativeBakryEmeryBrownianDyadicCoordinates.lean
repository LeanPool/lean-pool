/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicCoordinates.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicTents
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
/-!
# Alternative Bakry Emery Brownian dyadic coordinates

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianDyadic_coordinates_independent`,
`bakryBrownianDyadic_coordinate_fourth_integrable`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Independent coordinates for a unit-interval Brownian series: one linear
coordinate and one coefficient for each dyadic tent. -/
abbrev BakryBrownianDyadicIndex := Option (Σ n : ℕ, Fin (2^n))
/-- Sample space of the dyadic Brownian series: one real coefficient for each index in
`BakryBrownianDyadicIndex`. -/
abbrev BakryBrownianDyadicSample := BakryBrownianDyadicIndex → ℝ

/-- The product of independent standard Gaussians `gaussianReal 0 1` on the dyadic sample
space. -/
def bakryBrownianDyadicMeasure : Measure BakryBrownianDyadicSample :=
  Measure.infinitePi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure bakryBrownianDyadicMeasure := by
  unfold bakryBrownianDyadicMeasure
  infer_instance

theorem bakryBrownianDyadic_coordinate_law (i : BakryBrownianDyadicIndex) :
    HasLaw (fun ω : BakryBrownianDyadicSample => ω i) (gaussianReal 0 1) bakryBrownianDyadicMeasure
        := by
  exact ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

theorem bakryBrownianDyadic_coordinates_independent :
    iIndepFun (fun i (ω : BakryBrownianDyadicSample) => ω i) bakryBrownianDyadicMeasure :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- The actual Gaussian fourth moment is finite; no numerical moment value
is needed for the uniform-series convergence argument. -/
theorem bakryBrownianDyadic_coordinate_fourth_integrable (i : BakryBrownianDyadicIndex) :
    Integrable (fun ω : BakryBrownianDyadicSample => |ω i|^4) bakryBrownianDyadicMeasure := by
  have h := ((memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)).integrable_norm_pow
    (p := 4) (by decide))
  simpa only [Real.norm_eq_abs, id_eq, Function.comp_def] using
    (bakryBrownianDyadic_coordinate_law i).integrable_comp h

end
end GinibrePoincare

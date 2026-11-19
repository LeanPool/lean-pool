/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUFunctional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUConvolution
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # A measurable path functional for the actual OU convolution -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- Measurable realization of the convolution on the entire coordinate-path
space, with actual Brownian paths recovered almost surely. -/
def ginibreOUConvolutionFunctional (rate t : ℝ≥0) (path : ℝ≥0 → ℝ) : ℝ :=
  limUnder atTop (fun n => ginibreBrownianOURiemannSum (fun s p => p s) rate t n path)

theorem ginibreOUConvolutionFunctional_measurable (rate t : ℝ≥0) :
    Measurable (ginibreOUConvolutionFunctional rate t) := by
  apply StronglyMeasurable.measurable
  exact StronglyMeasurable.limUnder (fun n => by
    apply Measurable.stronglyMeasurable
    unfold ginibreBrownianOURiemannSum
    fun_prop)

theorem ginibreOUConvolutionFunctional_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) :
    (fun ω => ginibreOUConvolutionFunctional rate t (fun s => B s ω)) =ᵐ[P]
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t := by
  filter_upwards [ginibreBrownianOURiemannSum_ae_tendsto B P hB rate t] with ω hω
  exact hω.limUnder_eq

/-- The actual future convolution, driven by the actual shifted Brownian
motion, is independent of the entire Brownian past. -/
theorem ginibreBrownianOU_shift_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    IndepFun (ginibreBrownianOU (fun u ω => B (s + u) ω - B s ω)
      rate (Real.sqrt (rate : ℝ)) 0 t)
      (fun ω (v : Set.Iic s) => B v ω) P := by
  have h := (hB.indepFun_shift s).comp (ginibreOUConvolutionFunctional_measurable rate t)
    (measurable_id)
  exact h.congr
    (ginibreOUConvolutionFunctional_ae_eq _ P (hB.shift s) rate t) (Filter.Eventually.of_forall fun
        _ => rfl)

end
end GinibrePoincare

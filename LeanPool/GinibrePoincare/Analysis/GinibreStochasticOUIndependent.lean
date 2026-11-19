/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUIndependent.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUJointLaw

/-! # Independence of actual OU paths driven by independent Brownian motions -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The Ornstein–Uhlenbeck value at time `t` as a functional of the start `x` and the driving
path: `ginibreOUDecay rate t * x` plus the convolution functional of the path. -/
def ginibreOUValueFunctional (rate t : ℝ≥0) (x : ℝ) (path : ℝ≥0 → ℝ) : ℝ :=
  ginibreOUDecay rate t * x + ginibreOUConvolutionFunctional rate t path

theorem ginibreOUValueFunctional_measurable (rate t : ℝ≥0) (x : ℝ) :
    Measurable (ginibreOUValueFunctional rate t x) :=
  measurable_const.add (ginibreOUConvolutionFunctional_measurable rate t)

theorem ginibreOUValueFunctional_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) (x : ℝ) :
    (fun ω => ginibreOUValueFunctional rate t x (fun s => B s ω)) =ᵐ[P]
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x t := by
  filter_upwards [ginibreOUConvolutionFunctional_ae_eq B P hB rate t] with ω hω
  change ginibreOUDecay rate t * x +
    ginibreOUConvolutionFunctional rate t (fun s => B s ω) = _
  rw [hω]
  change Real.exp (-(rate : ℝ) * (t : ℝ)) * x +
    drivenOUPath rate 0 (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t =
      drivenOUPath rate x (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t
  conv_rhs => rw [drivenOUPath_initial_split]
  rfl

theorem ginibreBrownianOU_independent {Ω : Type*} [MeasurableSpace Ω]
    (B C : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hind : IndepFun (fun ω s => B s ω) (fun ω s => C s ω) P)
    (rateB rateC s t : ℝ≥0) (x y : ℝ) :
    IndepFun (ginibreBrownianOU B rateB (Real.sqrt (rateB : ℝ)) x s)
      (ginibreBrownianOU C rateC (Real.sqrt (rateC : ℝ)) y t) P := by
  have h := hind.comp (ginibreOUValueFunctional_measurable rateB s x)
    (ginibreOUValueFunctional_measurable rateC t y)
  exact h.congr (ginibreOUValueFunctional_ae_eq B P hB rateB s x)
    (ginibreOUValueFunctional_ae_eq C P hC rateC t y)

end
end GinibrePoincare

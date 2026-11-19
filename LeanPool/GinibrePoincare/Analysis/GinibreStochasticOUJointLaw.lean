/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUJointLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUPast

/-! # Actual two-time OU law for the Brownian-driven integral-equation solution -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianOU_two_time_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    HasLaw (fun ω => (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω,
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (s + t) ω))
      (((ginibreOUTransition rate s x).prod (gaussianReal 0 (ginibreOUVariance rate t))).map
        (fun p : ℝ × ℝ => (p.1, ginibreOUDecay rate t * p.1 + p.2))) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let μ := (ginibreOUTransition rate s x).prod (gaussianReal 0 (ginibreOUVariance rate t))
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, ginibreOUDecay rate t * p.1 + p.2)
  have hp := (ginibreBrownianOUInnovation_independent_value B P hB rate s t x).symm.hasLaw_prod
    (ginibreBrownianOU_hasLaw B P hB rate s x)
    (ginibreBrownianOUInnovation_hasLaw B P hB rate s t)
  have hF : HasLaw F (μ.map F) μ := ⟨by fun_prop, rfl⟩
  have h := hF.comp hp
  apply h.congr
  filter_upwards [ginibreBrownianOU_step_ae B P hB rate s t x] with ω hω
  change (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω,
    ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (s + t) ω) =
    (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω,
      ginibreOUDecay rate t * ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω +
        ginibreBrownianOUInnovation B rate s t ω)
  rw [hω]

end
end GinibrePoincare

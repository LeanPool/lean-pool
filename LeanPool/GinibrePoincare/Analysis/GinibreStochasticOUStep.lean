/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUStep.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUFunctional
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOUShift

/-! # Independent innovations of the actual driven OU solution -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual OU response to the fresh Brownian increments after time `s`. -/
def ginibreBrownianOUInnovation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate s t : ℝ≥0) : Ω → ℝ :=
  ginibreBrownianOU (fun u ω => B (s + u) ω - B s ω) rate (Real.sqrt (rate : ℝ)) 0 t

theorem ginibreBrownianOU_step_ae {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    ∀ᵐ ω ∂P, ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (s + t) ω =
      ginibreOUDecay rate t * ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω +
        ginibreBrownianOUInnovation B rate s t ω := by
  filter_upwards [hB.cont] with ω hcont
  let N := ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω
  have hN : Continuous N := continuous_const.mul (hcont.comp continuous_real_toNNReal)
  have h := drivenOUPath_shift (rate : ℝ) x N hN (s : ℝ) (t : ℝ)
  have hM : drivenOUPath rate (drivenOUPath rate x N s) (fun u => N ((s : ℝ) + u) - N s) t =
      drivenOUPath rate (drivenOUPath rate x N s)
        (ginibreBrownianNoise (fun u ω => B (s + u) ω - B s ω)
          (Real.sqrt (rate : ℝ)) ω) t := by
    apply drivenOUPath_congr_nonneg _ _ _ _ _ t.coe_nonneg
    intro u hu
    simp only [N, ginibreBrownianNoise, Real.toNNReal_add s.coe_nonneg hu.1,
      Real.toNNReal_coe, mul_sub]
  rw [hM] at h
  conv_rhs at h => rw [drivenOUPath_initial_split]
  simpa only [ginibreBrownianOU, ginibreBrownianOUInnovation, ginibreOUDecay,
    NNReal.coe_add, N, smul_eq_mul] using h

theorem ginibreBrownianOUInnovation_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    HasLaw (ginibreBrownianOUInnovation B rate s t)
      (gaussianReal 0 (ginibreOUVariance rate t)) P := by
  have h := ginibreBrownianOU_zero_hasLaw _ P (hB.shift s) rate t
  have hk : ginibreOUTransition rate t 0 = gaussianReal 0 (ginibreOUVariance rate t) := by
    change gaussianReal (ginibreOUDecay rate t * 0) (ginibreOUVariance rate t) = _
    rw [mul_zero]
  rw [hk] at h
  exact h

theorem ginibreBrownianOUInnovation_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    IndepFun (ginibreBrownianOUInnovation B rate s t)
      (fun ω (v : Set.Iic s) => B v ω) P :=
  ginibreBrownianOU_shift_independent_past B P hB rate s t

end
end GinibrePoincare

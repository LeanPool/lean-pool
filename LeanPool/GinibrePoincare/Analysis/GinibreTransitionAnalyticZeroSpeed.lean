/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticZeroSpeed.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroSpeed
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupPaperSpeed

/-! The actual original transition and analytic evolution coincide at zero
paper speed on every symmetric L² value. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_zero_speed_transition_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (t : ℝ≥0) :
    (∫ ω, f (ginibreBrownianMaximalProcess n 0 z B t ω) ∂P)=f z := by
  have he : (fun ω => f (ginibreBrownianMaximalProcess n 0 z B t ω)) =ᵐ[P] (fun _ => f z) :=
    (ginibreBrownianMaximalProcess_zero_speed_constant hn z hz B P hB hind).mono fun ω hω =>
        congrArg f (hω t)
  rw [integral_congr_ae he]
  simp

theorem ginibreFullRealPaperEvolution_zero_speed {n : ℕ} (hn : 0 < n) (t : ℝ≥0) :
    ginibreFullRealPaperEvolution n hn 0 t=1 := by
  ext u
  simp [ginibreFullRealPaperEvolution, ginibrePaperSpeedFactor, ginibreFullRealEvolution,
    ginibreFullEvolution_zero, ginibreFullSymmetricRe_ofReal]

theorem ginibreBrownian_zero_speed_analytic_transition
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ginibreFullSymmetricValues n) (t : ℝ≥0) :
    (∫ ω, u.val (ginibreBrownianMaximalProcess n 0 z B t ω) ∂P)=
      (ginibreFullRealPaperEvolution n hn 0 t u).val z := by
  rw [ginibreFullRealPaperEvolution_zero_speed hn t]
  exact ginibreBrownian_zero_speed_transition_integral hn z hz B P hB hind u.val t

end
end GinibrePoincare

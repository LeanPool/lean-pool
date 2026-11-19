/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianProcessFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCenterFunctional

/-! Measurable functional transport of whole center and relative process independence. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterOUPath_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    @Measurable C(ℝ, ℂ) (ℝ≥0 → ℂ) (borel _) _
      (fun N t => ginibreCenterOUValue n α z t N) := by
  let : MeasurableSpace C(ℝ, ℂ) := borel _
  let : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩
  apply Measurable.of_eval
  intro t
  exact ginibreCenterOUValue_measurable n α z t

theorem ginibreDrivenCanonicalPath_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) :
    Measurable (fun N : GinibreContinuousNoise n => fun t : ℝ≥0 => ginibreDrivenMaximalValue n α
        N.val z t) := by
  apply Measurable.of_eval
  intro t
  exact ginibreDrivenMaximalValue_measurable hn α z t

theorem ginibreBrownian_center_relative_processes_independent_of_noise {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (hNoise : @IndepFun Ω C(ℝ, ℂ) (GinibreContinuousNoise n) _ (borel _) _
      (fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))
      (fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)) P) :
    IndepFun (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))
      (fun ω t => recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω)) P := by
  let : MeasurableSpace C(ℝ, ℂ) := borel _
  let : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩
  have h := hNoise.comp (ginibreCenterOUPath_measurable n α z)
    (ginibreDrivenCanonicalPath_measurable hn α (recenteredConfiguration n z))
  have hS : (fun ω t => ginibreCenterOUValue n α z t
      (ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))) =ᵐ[P]
      (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)) := by
    filter_upwards [ginibreBrownian_center_OU_factorization hn α z hz B P hB hind] with ω hω
    funext t
    exact (hω t).symm
  have hW : (fun ω t => ginibreDrivenMaximalValue n α
      (ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)).val
      (recenteredConfiguration n z) t) =ᵐ[P]
      (fun ω t => recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω)) := by
    filter_upwards [ginibreBrownian_recentered_canonical_factorization hn α z hz B P hB hind] with ω
        hω
    funext t
    exact (hω.2 t).symm
  exact h.congr hS hW

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianProjectedNoise.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianFactorization
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticNoncollision

/-! The actual recentered process is a Borel functional of its projected continuous noise. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The recentered noise path, applying `recenteredCLM n` at every time; it still starts at
`0`. -/
def ginibreContinuousNoiseRecenter (n : ℕ) (N : GinibreContinuousNoise n) : GinibreContinuousNoise
     n :=
  ⟨(⟨recenteredCLM n, (recenteredCLM n).continuous⟩ : C(Configuration n, Configuration n)).comp
      N.val, by
    change recenteredCLM n (N.val 0) = 0
    rw [N.property, map_zero]⟩

theorem ginibreContinuousNoiseRecenter_continuous (n : ℕ) : Continuous
     (ginibreContinuousNoiseRecenter n) := by
  apply Continuous.subtype_mk
  exact ((⟨recenteredCLM n, (recenteredCLM n).continuous⟩ : C(Configuration n, Configuration
      n)).continuous_postcomp).comp continuous_subtype_val

/-- The value at time `t` of the maximal driven path started at the recentered configuration
of `z` and driven by the recentered noise. -/
def ginibreRecenteredCanonicalValue (n : ℕ) (α : ℝ) (z : Configuration n) (t : ℝ≥0)
    (N : GinibreContinuousNoise n) : Configuration n :=
  ginibreDrivenMaximalValue n α (ginibreContinuousNoiseRecenter n N).val (recenteredConfiguration n
      z) t

theorem ginibreRecenteredCanonicalValue_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (t : ℝ≥0) : Measurable (ginibreRecenteredCanonicalValue n α z t)
        :=
  (ginibreDrivenMaximalValue_measurable hn α (recenteredConfiguration n z) t).comp
    (ginibreContinuousNoiseRecenter_continuous n).measurable

theorem ginibreBrownian_recentered_canonical_factorization {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P,
      ginibreDrivenMaximalLifetime n α
        (ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)).val
        (recenteredConfiguration n z) = ⊤ ∧
      ∀ t : ℝ≥0, recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω) =
        ginibreRecenteredCanonicalValue n α z t (ginibreBrownianFullContinuousNoise n B α ω) := by
  filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hs hNoise
  let X := fun t : ℝ => ginibreBrownianMaximalProcess n α z B (Real.toNNReal t) ω
  have hN : (ginibreBrownianFullContinuousNoise n B α ω).val = ginibreConfigurationBrownianNoise n B
      α ω :=
    funext hNoise
  have heq : IsGinibreDrivenPath n α (ginibreBrownianFullContinuousNoise n B α ω).val X := by
    rw [hN]
    exact hs.2.2.2
  have hr := ginibreDrivenPath_recentered_canonical_global hs.1 hs.2.2.1 heq
  have hX0 : X 0 = z := by simpa only [X, Real.toNNReal_zero] using hs.2.1
  simp only [Real.toNNReal_zero, hs.2.1] at hr
  have hRecN : (ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)).val =
      (fun t => recenteredConfiguration n ((ginibreBrownianFullContinuousNoise n B α ω).val t)) :=
          by
    funext t
    exact recenteredCLM_apply n _
  refine ⟨?_, fun t => ?_⟩
  · rw [hRecN]
    exact hr.1
  · unfold ginibreRecenteredCanonicalValue
    rw [hRecN]
    simpa only [Real.toNNReal_coe] using (hr.2 t).symm

end
end GinibrePoincare

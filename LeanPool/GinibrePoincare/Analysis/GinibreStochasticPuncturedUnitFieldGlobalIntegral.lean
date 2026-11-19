/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticPuncturedUnitFieldGlobalIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPuncturedUnitFieldIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldGlobalIntegral

/-!
# Ginibre stochastic punctured unit field global integral

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibrePuncturedUnitField_global_continuous_integral_exists`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibrePuncturedUnitField_global_continuous_integral_exists
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖ = 1)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Ioi 0)) (i₀ : ι) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ᵐ ω ∂P, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω =>
        ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (J t)) ∧
      (∀ t, HasLaw (J t) (gaussianReal 0 t) P) := by
  classical
  classical
  have hex (n : ℕ) := ginibrePuncturedUnitField_continuous_integral_exists B P hB hind u hu hunit
    (n+1 : ℝ≥0) (by positivity) hc i₀
  choose M hM hMC hML hM0 hMS hMlaw using hex
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS⟩ := ginibreContinuousMartingale_global_of_horizon_limits P
    (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
    (fun t k ω => ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω)
    M hM hMC hML hM0 hMS
  refine ⟨J, hJM, hJC, hJL, hJ0, hJS,?_⟩
  intro t
  exact brownianUnitField_integral_limit_gaussian B P (fun i => (hB i).toIsPreBrownianReal)
    hind u hu hunit i₀ t (J t) (hJS t)

/-- The continuous-field case of the punctured global integral. -/
theorem ginibreUnitField_global_continuous_integral_exists
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖ = 1)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω)) (i₀ : ι) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ᵐ ω ∂P, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω =>
        ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (J t)) ∧
      (∀ t, HasLaw (J t) (gaussianReal 0 t) P) := by
  exact ginibrePuncturedUnitField_global_continuous_integral_exists B P hB hind u hu hunit
    (hc.mono fun ω hω => hω.continuousOn) i₀

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralExponentialLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialApproximation
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianShiftedLimit
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovVectorDensityLimit

/-!
# Ginibre Brownian integral exponential limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianVectorExponentialUniformSum_tendstoInMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The discrete stochastic exponential on the uniform grid: the exponential of the sum of the
left-point Itô sums of `F i` against `B i` minus half the Riemann energy sum. -/
def brownianVectorExponentialUniformSum {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp ((∑ i, brownianUniformLeftSum (B i) (F i) T (n+1) ω)-
    brownianVectorTimeEnergyUniformSum F T n ω/2)

/-- The stochastic-exponential density `exp (∑ i, I i ω - brownianVectorTimeEnergy F T ω / 2)`,
where `I i` stands for the stochastic integral of `F i`. -/
def brownianVectorExponentialIntegralDensity {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (I : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp ((∑ i, I i ω)-brownianVectorTimeEnergy F T ω/2)

/-- Actual stochastic integral limits and genuine energy Riemann convergence
 imply convergence in probability of the literal exponential density. -/
theorem brownianVectorExponentialUniformSum_tendstoInMeasure {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsFiniteMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ i t, Measurable (F i t))
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T))
    (hs : ∀ i n, AEStronglyMeasurable (brownianUniformLeftSum (B i) (F i) T (n + 1)) P)
    (I : ι → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P
      (fun n => brownianUniformLeftSum (B i) (F i) T (n + 1)) atTop (I i)) :
    TendstoInMeasure P (brownianVectorExponentialUniformSum B F T) atTop
      (brownianVectorExponentialIntegralDensity F T I) := by
  have he := brownianVectorTimeEnergyUniformSum_tendstoInMeasure P F T hm hc
  have hemi (n : ℕ) : AEStronglyMeasurable (brownianVectorTimeEnergyUniformSum F T n) P :=
      (brownianVectorTimeEnergyUniformSum_measurable F T hm n).aestronglyMeasurable
  have hehalf := itoTendstoInMeasure_continuous P _ _ hemi he (fun x => x/2) (by fun_prop)
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ _ _ hs hI
  have hsumm (n : ℕ) : AEStronglyMeasurable
      (fun ω => ∑ i, brownianUniformLeftSum (B i) (F i) T (n+1) ω) P := by
    convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hs i n) using 1
    funext ω
    exact (Finset.sum_apply ω Finset.univ _).symm
  have hhalf (n : ℕ) : AEStronglyMeasurable (fun ω => brownianVectorTimeEnergyUniformSum F T n ω/2)
      P := by
    convert (hemi n).mul (aestronglyMeasurable_const (b := (2 : ℝ)⁻¹)) using 1
    funext ω
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hexponent := actualTendstoInMeasure_sub P _ _ _ _ hsumm hhalf hsum hehalf
  have hexponentm (n : ℕ) : AEStronglyMeasurable (fun ω => (∑ i, brownianUniformLeftSum (B i) (F i)
      T (n+1) ω)-brownianVectorTimeEnergyUniformSum F T n ω/2) P := (hsumm n).sub (hhalf n)
  exact itoTendstoInMeasure_continuous P _ _ hexponentm hexponent Real.exp Real.continuous_exp

end
end GinibrePoincare

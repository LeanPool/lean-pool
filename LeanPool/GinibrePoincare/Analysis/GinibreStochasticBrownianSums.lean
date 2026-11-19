/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianSums.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGaussianLimit
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Exact Gaussian laws of weighted finite Brownian increment sums -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_increment_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) P := by
  have h := (hB.shift s).hasLaw_eval (t - s)
  simpa only [add_tsub_cancel_of_le hst] using h

/-- Exact law for arbitrary deterministic coefficients and increasing finite
sampling times of an actual Brownian process. -/
theorem ginibreBrownian_weighted_increments_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (n : ℕ) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) (w : Fin n → ℝ) :
    HasLaw (fun ω => ∑ i : Fin n, w i * (B (τ i.succ) ω - B (τ i.castSucc) ω))
      (gaussianReal 0 (∑ i : Fin n, NNReal.mk (w i ^ 2) (sq_nonneg _) *
        (τ i.succ - τ i.castSucc))) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let W : Fin n → Ω → ℝ := fun i ω => w i * (B (τ i.succ) ω - B (τ i.castSucc) ω)
  let V : ℝ≥0 := ∑ i : Fin n, NNReal.mk (w i ^ 2) (sq_nonneg _) * (τ i.succ - τ i.castSucc)
  have hlaw (i : Fin n) : HasLaw (W i)
      (gaussianReal 0 (NNReal.mk (w i ^ 2) (sq_nonneg _) * (τ i.succ - τ i.castSucc))) P := by
    simpa only [mul_zero] using gaussianReal_const_mul
      (ginibreBrownian_increment_hasLaw B P hB (τ i.castSucc) (τ i.succ)
        (hτ i.castSucc_lt_succ.le)) (w i)
  have hmem (i : Fin n) : MemLp (W i) 2 P := (hlaw i).hasGaussianLaw.memLp_two
  have hmean : (∫ ω, ∑ i : Fin n, W i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    apply Finset.sum_eq_zero
    intro i _
    rw [(hlaw i).integral_eq]
    exact integral_id_gaussianReal
  have hind := (hB.hasIndepIncrements n τ hτ).comp
    (fun i => (fun y : ℝ => w i * y)) (fun _ => by fun_prop)
  have hvar : Var[(fun ω => ∑ i : Fin n, W i ω); P] = (V : ℝ) := by
    have hv := IndepFun.variance_sum (s := Finset.univ) (X := W)
      (fun i _ => hmem i) (fun i _ j _ hij => hind.indepFun hij)
    have hsum : (∑ i : Fin n, W i) = (fun ω => ∑ i : Fin n, W i ω) := by
      funext ω; simp only [Finset.sum_apply]
    rw [hsum] at hv
    rw [hv]
    simp only [V, NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hlaw i).variance_eq, variance_id_gaussianReal]
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i : Fin n, w i • ContinuousLinearMap.proj i
  have hGaussian := (hB.isGaussianProcess.hasGaussianLaw_increments (t := τ)).map_fun L
  have he : (fun ω => L (fun i : Fin n => B (τ i.succ) ω - B (τ i.castSucc) ω)) =
      (fun ω => ∑ i : Fin n, W i ω) := by
    funext ω
    simp [L, W, smul_eq_mul]
  rw [he] at hGaussian
  refine ⟨hGaussian.aemeasurable, ?_⟩
  rw [hGaussian.map_eq_gaussianReal, hmean, hvar, Real.toNNReal_coe]

end
end GinibrePoincare

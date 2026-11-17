/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BernoulliGaussianCLT.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BernoulliCubeLSI
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Bernoulli Gaussian CLT
-/


@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

/-- The fair law on the two signs. -/
def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by constructor <;> norm_num⟩

instance rademacherMeasure_probability : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Independent fair signs on the countable product probability space. -/
def rademacherProduct : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => rademacherMeasure)

instance rademacherProduct_probability : IsProbabilityMeasure rademacherProduct := by
  unfold rademacherProduct
  infer_instance

/-- The normalized centered binomial sum (presented as a sum of signs). -/
def normalizedBernoulliSum (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, ω k

/-- Each coordinate has the concrete fair two-point law. -/
theorem rademacherCoordinate_hasLaw (i : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω i) rademacherMeasure rademacherProduct :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => rademacherMeasure) i).hasLaw

/-- The binomial central limit theorem on the concrete fair-sign product space. -/
theorem normalizedBernoulliSum_clt :
    TendstoInDistribution normalizedBernoulliSum atTop id
      (fun _ => rademacherProduct) (gaussianReal 0 1) := by
  have h0 : (∫ ω, ω 0 ∂rademacherProduct) = 0 := by
    have h := (rademacherCoordinate_hasLaw 0).integral_comp
      (f := fun x : ℝ => x) (by fun_prop)
    change (∫ ω, ω 0 ∂rademacherProduct) = _ at h
    rw [h]
    norm_num [rademacherMeasure, integral_bernoulliMeasure]
  have h1 : (∫ ω, (ω 0) ^ 2 ∂rademacherProduct) = 1 := by
    have h := (rademacherCoordinate_hasLaw 0).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    change (∫ ω, (ω 0) ^ 2 ∂rademacherProduct) = _ at h
    rw [h]
    norm_num [rademacherMeasure, integral_bernoulliMeasure]
  have hi : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) rademacherProduct := by
    exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (by fun_prop)
  have hd (i : ℕ) : IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω => ω 0)
      rademacherProduct rademacherProduct :=
    ⟨(rademacherCoordinate_hasLaw i).aemeasurable,
      (rademacherCoordinate_hasLaw 0).aemeasurable,
      (rademacherCoordinate_hasLaw i).map_eq.trans (rademacherCoordinate_hasLaw 0).map_eq.symm⟩
  exact tendstoInDistribution_inv_sqrt_mul_sum HasLaw.id h0 h1 hi hd

/-- Bounded continuous test integrals converge under the concrete binomial CLT. -/
theorem normalizedBernoulliSum_integral_tendsto (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, f (normalizedBernoulliSum n ω) ∂rademacherProduct)
      atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    normalizedBernoulliSum_clt.tendsto f
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h
  simp_rw [integral_map (normalizedBernoulliSum_clt.forall_aemeasurable _)
    f.continuous.aestronglyMeasurable] at h
  exact h

private theorem compact_test_integral_tendsto (f : ℝ → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => ∫ ω, f (normalizedBernoulliSum n ω) ∂rademacherProduct)
      atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C)
    (fun x y => (dist_le_norm_add_norm _ _).trans (by
      change ‖f x‖ + ‖f y‖ ≤ 2 * C
      linarith [hC x, hC y]))
  exact normalizedBernoulliSum_integral_tendsto F

/-- The CLT passes square entropy to its Gaussian limit for continuous compact tests.
This treats the logarithmic integrand at its zeros by its continuous extension. -/
theorem normalizedBernoulliSum_entropy_tendsto (f : ℝ → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => squareEntropy rademacherProduct
      (fun ω => f (normalizedBernoulliSum n ω))) atTop
      (𝓝 (squareEntropy (gaussianReal 0 1) f)) := by
  have hs : HasCompactSupport (fun x => (f x) ^ 2) := hc.mono (by
    intro x hx hz
    exact hx (by simp [hz]))
  have hm := compact_test_integral_tendsto (fun x => (f x) ^ 2) (hf.pow 2) hs
  have hl := compact_test_integral_tendsto (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2))
    (continuous_square_mul_log hf) (compactSupport_square_mul_log hc)
  have hp := Real.continuous_mul_log.continuousAt.tendsto.comp hm
  exact hl.sub hp

end
end GinibrePoincare

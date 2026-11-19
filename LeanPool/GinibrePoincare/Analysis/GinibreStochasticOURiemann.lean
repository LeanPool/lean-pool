/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOURiemann.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianSums
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUWeight
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathUniformPartition

/-! # Concrete weighted Brownian sums approaching the OU convolution -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The `i`-th point `t i / (n + 1)` of the uniform partition of `[0, t]` into `n + 1` steps, as
a nonnegative real. -/
def ginibreUniformBrownianTime (t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  (ginibreUniformTime t n i).toNNReal

theorem ginibreUniformBrownianTime_coe (t : ℝ≥0) (n i : ℕ) :
    (ginibreUniformBrownianTime t n i : ℝ) = ginibreUniformTime t n i := by
  apply Real.coe_toNNReal
  unfold ginibreUniformTime
  positivity

theorem ginibreUniformBrownianTime_mono (t : ℝ≥0) (n : ℕ) :
    Monotone (ginibreUniformBrownianTime t n) := by
  intro i j hij
  exact Real.toNNReal_mono (ginibreUniformTime_mono t t.coe_nonneg n hij)

/-- The Riemann sum of the Ornstein–Uhlenbeck stochastic weight against the increments of `B`
over the uniform partition of `[0, t]` into `n + 1` steps. -/
def ginibreBrownianOURiemannSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (n + 1), ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) *
    (B (ginibreUniformBrownianTime t n (i.val + 1)) ω -
      B (ginibreUniformBrownianTime t n i) ω)

/-- The variance `∑ wᵢ² (tᵢ₊₁ - tᵢ)` of `ginibreBrownianOURiemannSum`, with `wᵢ` the
Ornstein–Uhlenbeck stochastic weight at the grid time `tᵢ`. -/
def ginibreBrownianOURiemannVariance (rate t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ∑ i : Fin (n + 1),
    NNReal.mk (ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) ^ 2) (sq_nonneg _) *
      (ginibreUniformBrownianTime t n (i.val + 1) - ginibreUniformBrownianTime t n i)

theorem ginibreBrownianOURiemannSum_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate t : ℝ≥0) (n : ℕ) :
    HasLaw (ginibreBrownianOURiemannSum B rate t n)
      (gaussianReal 0 (ginibreBrownianOURiemannVariance rate t n)) P := by
  exact ginibreBrownian_weighted_increments_hasLaw B P hB (n + 1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
    (fun i => ginibreOUStochasticWeight rate t (ginibreUniformTime t n i))

theorem ginibreBrownianOURiemannVariance_coe (rate t : ℝ≥0) (n : ℕ) :
    (ginibreBrownianOURiemannVariance rate t n : ℝ) =
      ∑ i ∈ Finset.range (n + 1),
        ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) ^ 2 *
          (ginibreUniformTime t n (i + 1) - ginibreUniformTime t n i) := by
  unfold ginibreBrownianOURiemannVariance
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk]
  simp_rw [NNReal.coe_sub (ginibreUniformBrownianTime_mono t n (Nat.le_succ _)),
    ginibreUniformBrownianTime_coe]
  exact Fin.sum_univ_eq_sum_range (fun i =>
    ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) ^ 2 *
      (ginibreUniformTime t n (i + 1) - ginibreUniformTime t n i)) (n + 1)

theorem ginibreBrownianOURiemannVariance_tendsto (rate t : ℝ≥0) :
    Tendsto (ginibreBrownianOURiemannVariance rate t) atTop (𝓝 (ginibreOUVariance rate t)) := by
  have hc : Continuous (fun s : ℝ =>
      2 * (rate : ℝ) * ginibreOUStochasticWeight rate t s ^ 2) := by
    unfold ginibreOUStochasticWeight
    fun_prop
  have h := ginibreUniformScalarRiemann_tendsto
    (fun s => ginibreOUStochasticWeight rate t s ^ 2)
    (fun s => 2 * (rate : ℝ) * ginibreOUStochasticWeight rate t s ^ 2)
    (ginibreOUStochasticWeight_sq_hasDerivAt rate t) hc t t.coe_nonneg
  rw [ginibreOUStochasticWeight_variance_integral] at h
  have he := (continuous_real_toNNReal.tendsto (ginibreOUVariance rate t : ℝ)).comp h
  simpa only [Function.comp_def, ← ginibreBrownianOURiemannVariance_coe, Real.toNNReal_coe] using he

end
end GinibrePoincare

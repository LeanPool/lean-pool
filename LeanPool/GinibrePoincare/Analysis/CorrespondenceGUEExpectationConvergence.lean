/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEExpectationConvergence.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUENormalization
/-!
# Correspondence GUE expectation convergence

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledRegularized_expectation_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem gueDoubledRegularized_weighted_integral_tendsto {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) (hf : Continuous f)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun k => ∫ x, Real.exp (-gueDoubledRegularizedPotential n
      (gueRegularizationScale k) x)*f x) atTop
      (nhds (∫ x, gueDoubledOrderedDensity n x*f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => gueDoubledDomination n x*C)
  · intro k
    exact ((Real.continuous_exp.comp (gueDoubledRegularizedPotential_contDiff n
        (gueRegularizationScale_pos k)).continuous.neg).mul hf).aestronglyMeasurable
  · exact (gueDoubledDomination_integrable hn).mul_const C
  · intro k
    filter_upwards [] with x
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (gueDoubledRegularized_density_bound n k x) (hb x)
      (norm_nonneg _) (le_trans (Real.exp_pos _).le (gueDoubledRegularized_density_bound n k x))
  · filter_upwards [] with x
    exact (gueDoubledRegularized_density_tendsto n x).mul tendsto_const_nhds

theorem gueDoubledRegularized_partition_tendsto {n : ℕ} (hn : 0 < n) :
    Tendsto (fun k => ∫ x, Real.exp (-gueDoubledRegularizedPotential n
      (gueRegularizationScale k) x)) atTop
      (nhds (∫ x, gueDoubledOrderedDensity n x)) := by
  simpa using gueDoubledRegularized_weighted_integral_tendsto hn (fun _ => 1)
    continuous_const 1 (by norm_num) (by intro x; norm_num)

/-- Actual normalized ordered GUE expectation, including the independent auxiliary Gaussian. -/
def gueDoubledOrderedExpectation (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) : ℝ :=
  (∫ x, gueDoubledOrderedDensity n x*f x)/(∫ x, gueDoubledOrderedDensity n x)

theorem gueDoubledRegularized_expectation_tendsto {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun k => ∫ x, f x ∂bakryEmeryNormalizedGibbs volume
      (gueDoubledRegularizedPotential n (gueRegularizationScale k))) atTop
      (nhds (gueDoubledOrderedExpectation n f)) := by
  simp_rw [bakryEmeryNormalizedGibbs_integral volume _
    (gueDoubledRegularizedPotential_contDiff n (gueRegularizationScale_pos _)).continuous]
  exact (gueDoubledRegularized_weighted_integral_tendsto hn f hf C hC hb).div
    (gueDoubledRegularized_partition_tendsto hn) (ne_of_gt (gueDoubledOrdered_partition_pos hn))

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathRiemann.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOU

/-! # Deterministic summation by parts for Brownian convolution approximation -/

@[expose] public section
open MeasureTheory
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A finite weighted increment sum, with the endpoint correction written
exactly. No differentiability of the increment path is required. -/
theorem ginibreWeightedIncrements_by_parts (w : ℕ → ℝ) (N : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range n, w i • (N (i + 1) - N i)) =
      w n • N n - w 0 • N 0 -
        ∑ i ∈ Finset.range n, (w (i + 1) - w i) • N (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [smul_sub, sub_smul]
    abel

/-- Exact ordinary-integral error formula for the finite weighted increments.
It reduces stochastic convolution convergence to uniform continuity of paths. -/
theorem ginibreWeightedIncrements_integral_error (w w' : ℝ → ℝ) (N : ℝ → E)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hN : Continuous N)
    (τ : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, w (τ i) • (N (τ (i + 1)) - N (τ i))) -
      (w (τ n) • N (τ n) - w (τ 0) • N (τ 0) -
        ∫ s in (τ 0)..(τ n), w' s • N s) =
      ∑ i ∈ Finset.range n,
        ∫ s in (τ i)..(τ (i + 1)), w' s • (N s - N (τ (i + 1))) := by
  rw [ginibreWeightedIncrements_by_parts (fun i => w (τ i)) (fun i => N (τ i)) n]
  have hI := intervalIntegral.sum_integral_adjacent_intervals (n := n) (a := τ) (μ := volume)
    (f := fun s => w' s • N s)
    (fun i _ => (hw'.smul hN).intervalIntegrable _ _)
  rw [← hI]
  have hterm (i : ℕ) :
      (∫ s in (τ i)..(τ (i + 1)), w' s • N s) -
        (w (τ (i + 1)) - w (τ i)) • N (τ (i + 1)) =
      ∫ s in (τ i)..(τ (i + 1)), w' s • (N s - N (τ (i + 1))) := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := τ i) (b := τ (i + 1))
      (fun s _ => hw s) (hw'.intervalIntegrable _ _)
    rw [← hFTC, ← intervalIntegral.integral_smul_const]
    rw [← intervalIntegral.integral_sub
      (f := fun s => w' s • N s) (g := fun s => w' s • N (τ (i + 1)))
      (a := τ i) (b := τ (i + 1)) (μ := volume)
      ((hw'.smul hN).intervalIntegrable _ _)
      ((hw'.smul continuous_const).intervalIntegrable _ _)]
    congr 1
    funext s
    exact (smul_sub _ _ _).symm
  rw [← Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_sub_distrib]
  abel

/-- Quantitative pathwise convergence estimate. The oscillation bound is only
needed within each sampling interval. -/
theorem ginibreWeightedIncrements_integral_error_bound (w w' : ℝ → ℝ) (N : ℝ → E)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hN : Continuous N)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ) (C ε : ℝ) (hC : 0 ≤ C) (_ : 0 ≤ ε)
    (hbound : ∀ i < n, ∀ s ∈ Set.uIoc (τ i) (τ (i + 1)), ‖w' s‖ ≤ C)
    (hosc : ∀ i < n, ∀ s ∈ Set.uIoc (τ i) (τ (i + 1)),
      ‖N s - N (τ (i + 1))‖ ≤ ε) :
    ‖(∑ i ∈ Finset.range n, w (τ i) • (N (τ (i + 1)) - N (τ i))) -
      (w (τ n) • N (τ n) - w (τ 0) • N (τ 0) -
        ∫ s in (τ 0)..(τ n), w' s • N s)‖ ≤ C * ε * (τ n - τ 0) := by
  rw [ginibreWeightedIncrements_integral_error w w' N hw hw' hN τ n]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        ‖∫ s in (τ i)..(τ (i + 1)), w' s • (N s - N (τ (i + 1)))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, (C * ε) * (τ (i + 1) - τ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hib : i < n := Finset.mem_range.mp hi
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := τ i) (b := τ (i + 1)) (C := C * ε)
        (f := fun s => w' s • (N s - N (τ (i + 1)))) (fun s hs => by
          rw [norm_smul]
          exact mul_le_mul (hbound i hib s hs) (hosc i hib s hs) (norm_nonneg _) hC)
      simpa only [abs_of_nonneg (sub_nonneg.mpr (hτ (Nat.le_succ i)))] using hnorm
    _ = C * ε * (τ n - τ 0) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]

end
end GinibrePoincare

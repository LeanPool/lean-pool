/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoUniformChain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftVariation
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoPartitionRemainder

/-!
# Finite dimensional Ito uniform chain

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoUniformNNTime_zero`, `itoVolterra_uniform_chain_identity`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem itoUniformNNTime_zero (T : ℝ≥0) (N : ℕ) : itoUniformNNTime T N 0 = 0 := by
  simp [itoUniformNNTime, itoUniformTime]

/-- Exact discrete chain identity on the actual Brownian sampling grid. -/
theorem itoUniformPathTaylor_identity (f : E → ℝ) (z : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) :
    f (z T)-f (z 0) =
      (∑ i : Fin (n+1), fderiv ℝ f (z (ginibreUniformBrownianTime T n i))
        (z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i))) +
      (1/2 : ℝ)*(∑ i : Fin (n+1), itoDirectionalHessian f (z (ginibreUniformBrownianTime T n i))
        (z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i))) +
      (∑ i : Fin (n+1), itoTaylorRemainder f (z (ginibreUniformBrownianTime T n i))
        (z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i))) := by
  have h := itoTaylor_partition_identity f (fun i => z (itoUniformNNTime T (n+1) i)) (n+1)
  have hzero : ginibreUniformBrownianTime T n 0 = 0 := by
    simp [ginibreUniformBrownianTime, ginibreUniformTime]
  simp only [itoUniformNNTime_end T (n+1) (Nat.succ_pos n),
    itoUniformNNTime_eq_brownianTime] at h
  simpa only [← Fin.sum_univ_eq_sum_range, hzero] using h

/-- The actual Volterra equation identifies each actual increment with noise plus drift. -/
theorem itoVolterra_uniform_increment (z W : ℝ≥0 → E) (b : ℝ → E) (T : ℝ≥0)
    (hb : ContinuousOn b (Set.Icc (0 : ℝ) T))
    (hz : ∀ t ∈ Set.Icc 0 T,
      z t = z 0 + (W t - W 0) + ∫ s in (0 : ℝ)..(t : ℝ), b s)
    (n : ℕ) (i : Fin (n + 1)) :
    z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i) =
      (W (ginibreUniformBrownianTime T n (i.val+1))-W (ginibreUniformBrownianTime T n i)) +
        itoUniformDriftIncrement b T n i := by
  rw [hz _ ⟨bot_le, ginibreUniformBrownianTime_le_end T n _ (Nat.succ_le_of_lt i.is_lt)⟩,
    hz _ ⟨bot_le, ginibreUniformBrownianTime_le_end T n _ (Nat.le_of_lt i.is_lt)⟩,
    ← itoUniformDriftIncrement_eq_volterra_difference b T hb n i]
  abel

/-- Exact uniform-grid chain rule with the original Volterra noise and drift split. -/
theorem itoVolterra_uniform_chain_identity (f : E → ℝ) (z W : ℝ≥0 → E) (b : ℝ → E)
    (T : ℝ≥0) (hb : ContinuousOn b (Set.Icc (0 : ℝ) T))
    (hz : ∀ t ∈ Set.Icc 0 T,
      z t = z 0 + (W t - W 0) + ∫ s in (0 : ℝ)..(t : ℝ), b s) (n : ℕ) :
    let a := fun i : Fin (n+1) => W (ginibreUniformBrownianTime T n (i.val+1))-
      W (ginibreUniformBrownianTime T n i)
    let d := fun i : Fin (n+1) => itoUniformDriftIncrement b T n i
    f (z T)-f (z 0) =
      (∑ i : Fin (n+1), fderiv ℝ f (z (ginibreUniformBrownianTime T n i)) (a i)) +
      (∑ i : Fin (n+1), fderiv ℝ f (z (ginibreUniformBrownianTime T n i)) (d i)) +
      (1/2 : ℝ)*(∑ i : Fin (n+1), itoDirectionalHessian f
        (z (ginibreUniformBrownianTime T n i)) (a i+d i)) +
      (∑ i : Fin (n+1), itoTaylorRemainder f
        (z (ginibreUniformBrownianTime T n i)) (a i+d i)) := by
  dsimp only
  rw [itoUniformPathTaylor_identity f z T n]
  simp_rw [itoVolterra_uniform_increment z W b T hb hz n, map_add]
  rw [Finset.sum_add_distrib]

end
end GinibrePoincare

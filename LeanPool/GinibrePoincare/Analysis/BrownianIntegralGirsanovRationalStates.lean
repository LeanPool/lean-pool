/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovRationalStates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovRationalGrid

/-!
# Brownian integral Girsanov rational states

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianGirsanovRationalGrid_states_identDistrib`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Full joint law of every rational subdivision state of the corrected
finite path, compared directly with the actual original vector Brownian path. -/
theorem brownianGirsanovRationalGrid_states_identDistrib
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (T : ℝ≥0) (q m : ℕ) (hq : 0 < q) (hm : 0 < m)
    (hh : ∀ k, @Measurable Ω (ι → ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (itoUniformNNTime T (q * m) k)) _ (h k)) :
    IdentDistrib
      (fun ω (p : Fin (q+1)) i => brownianGirsanovCorrectedPrefix B h
        (itoUniformNNTime T (q*m)) i (p.val*m) ω)
      (fun ω (p : Fin (q+1)) i => B i (T*(p.val : ℝ≥0)/(q : ℝ≥0)) ω-B i 0 ω)
      (P.withDensity (fun ω => ENNReal.ofReal
        (brownianPredictableVectorGaussianDensity B h (itoUniformNNTime T (q*m)) (q*m) ω))) P := by
  classical
  let f := fun (a : Fin (q*m) → ι→ℝ) (p : Fin (q+1)) (i : ι) =>
    ∑ k : Fin (p.val*m), a ⟨k.val, lt_of_lt_of_le k.isLt
      (Nat.mul_le_mul_right m (Nat.le_of_lt_succ p.isLt))⟩ i
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro i
    apply Finset.measurable_sum
    intro k hk
    exact (measurable_pi_apply i).comp (measurable_pi_apply _)
  have hl := brownianPredictableVectorGaussianDensity_corrected_grid_identDistrib B P hB hind h
    (itoUniformNNTime T (q*m)) (itoUniformNNTime_mono _ _) hh (q*m) f hf
  have hc : (fun ω => f (fun (k : Fin (q*m)) i =>
      B i (itoUniformNNTime T (q*m) (k.val+1)) ω-B i (itoUniformNNTime T (q*m) k) ω-
        h k ω i*((itoUniformNNTime T (q*m) (k.val+1)-itoUniformNNTime T (q*m) k : ℝ≥0) : ℝ))) =
      (fun ω (p : Fin (q+1)) i => brownianGirsanovCorrectedPrefix B h
        (itoUniformNNTime T (q*m)) i (p.val*m) ω) := by
    funext ω p i
    dsimp only [f]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => B i (itoUniformNNTime T (q*m) (k+1)) ω-
      B i (itoUniformNNTime T (q*m) k) ω-h k ω i*
      ((itoUniformNNTime T (q*m) (k+1)-itoUniformNNTime T (q*m) k : ℝ≥0) : ℝ)) (p.val*m)]
    rfl
  have hb : (fun ω => f (fun (k : Fin (q*m)) i =>
      B i (itoUniformNNTime T (q*m) (k.val+1)) ω-B i (itoUniformNNTime T (q*m) k) ω)) =
      (fun ω (p : Fin (q+1)) i => B i (T*(p.val : ℝ≥0)/(q : ℝ≥0)) ω-B i 0 ω) := by
    funext ω p i
    dsimp only [f]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => B i (itoUniformNNTime T (q*m) (k+1)) ω-
      B i (itoUniformNNTime T (q*m) k) ω) (p.val*m)]
    rw [Finset.sum_range_sub (fun k => B i (itoUniformNNTime T (q*m) k) ω) (p.val*m),
      brownianUniformNNTime_rational_endpoint T p.val q m hq hm]
    have hz : itoUniformNNTime T (q*m) 0=0 := by
      change (itoUniformTime T (q*m) 0).toNNReal=0
      simp only [itoUniformTime, Nat.cast_zero, mul_zero, zero_div, Real.toNNReal_zero]
    rw [hz]
  rwa [hc, hb] at hl

end
end GinibrePoincare

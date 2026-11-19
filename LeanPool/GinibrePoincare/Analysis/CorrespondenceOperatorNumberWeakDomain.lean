/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberWeakDomain.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
/-! # First weak derivatives from the maximal number graph

The coefficient criterion for a weak derivative requires square summability of
raised-index coefficients weighted by `sqrt (n * (q j + 1))`. The number graph
provides square summability weighted by `n * totalAntiDegree`. Each coordinate
degree is at most the total degree; the raised total degree is positive, so its
number weight also dominates the square-root coordinate weight. Comparison of
nonnegative series constructs the ordinary weak derivative without adding a
regularity assumption.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- Every maximal number-domain vector has all literal distributional dbar
derivatives in Gaussian L²; the analytic domain fact is proved from its graph. -/
theorem correspondenceOperatorNumber_weak_dbar_exists {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u, v) ∈ (correspondenceOperatorNumber n hn).graph) (j : Fin n) :
    ∃D, IsGaussianWeakDbar n u D j := by
  rw [correspondenceOperatorNumber_graph] at huv
  apply (gaussianWeakDbar_exists_iff_summable hn u j).mpr
  have hs := (hasSum_norm_sq_gaussianHermiteCoefficient hn v).summable.comp_injective
    (raiseHermiteIndex_injective j)
  apply Summable.of_nonneg_of_le (fun _=>sq_nonneg _) _ hs
  intro pq
  change ‖(Real.sqrt (n*(pq.2 j+1) : ℕ) : ℂ)*gaussianHermiteCoefficient hn u (raiseHermiteIndex j
      pq)‖^2 ≤
    ‖gaussianHermiteCoefficient hn v (raiseHermiteIndex j pq)‖^2
  rw [huv (raiseHermiteIndex j pq)]
  have hj : pq.2 j+1≤totalAntiDegree (raiseHermiteIndex j pq) := by
    have h := Finset.single_le_sum (fun i _=>Nat.zero_le ((raiseHermiteIndex j pq).2 i))
      (Finset.mem_univ j)
    simpa [raiseHermiteIndex, raiseAt, totalAntiDegree] using h
  have ha : (n*(pq.2 j+1) : ℕ)≤n*totalAntiDegree (raiseHermiteIndex j pq) :=
    Nat.mul_le_mul_left n hj
  have hb : 1≤n*totalAntiDegree (raiseHermiteIndex j pq) :=
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne'
      (Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos _) hj))))
  have hsqrt : Real.sqrt (n*(pq.2 j+1) : ℕ)≤(n*totalAntiDegree (raiseHermiteIndex j pq) : ℕ) := by
    have hBR : (1 : ℝ)≤(n*totalAntiDegree (raiseHermiteIndex j pq) : ℕ) := by exact_mod_cast hb
    have hAR : ((n*(pq.2 j+1) : ℕ) : ℝ)≤(n*totalAntiDegree (raiseHermiteIndex j pq) : ℕ) := by
      exact_mod_cast ha
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnrm : ‖((n*totalAntiDegree (raiseHermiteIndex j pq) : ℕ) : ℂ)‖=
      ((n*totalAntiDegree (raiseHermiteIndex j pq) : ℕ) : ℝ) := by
    norm_cast
  rw [hnrm]
  exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg (gaussianHermiteCoefficient
      hn u (raiseHermiteIndex j pq)))) (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg
          (gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)))) 2
end
end GinibrePoincare

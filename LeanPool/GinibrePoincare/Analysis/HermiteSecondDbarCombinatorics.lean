/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteSecondDbarCombinatorics.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-! # Ordered second antiholomorphic lowering coefficients

The ordered coordinate sum includes diagonal pairs, where the second lowering
uses the exponent already reduced by one. This gives the factor m(m-1).
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare.ComplexHermite
noncomputable section

theorem sum_lowerAt_of_positive {n : ℕ} (q : Fin n → ℕ) (j : Fin n)
    (hj : 0 < q j) :
    (∑ k, lowerAt q j k) + 1 = ∑ k, q k := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : (∑ k ∈ Finset.univ.erase j, lowerAt q j k) =
      ∑ k ∈ Finset.univ.erase j, q k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [lowerAt, Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he]
  simp only [lowerAt, Function.update_self]
  omega

/-- Exact sum of the squared ordered second-lowering coefficients. -/
theorem sum_second_lowering_weights {n : ℕ} (q : Fin n → ℕ) :
    (∑ j, ∑ k, q j * lowerAt q j k) =
      (∑ j, q j) * ((∑ j, q j) - 1) := by
  classical
  simp_rw [← Finset.mul_sum]
  have he : ∀ j, q j * (∑ k, lowerAt q j k) =
      q j * ((∑ k, q k) - 1) := by
    intro j
    by_cases hj : 0 < q j
    · have h := sum_lowerAt_of_positive q j hj
      congr 1
      omega
    · have hz : q j = 0 := by omega
      simp [hz]
  simp_rw [he]
  rw [Finset.sum_mul]

/-- Weighted Parseval after lowering, retaining the target index in the weight. -/
theorem loweredCoefficients_weighted_normSq_sum (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n)
    (w : HermiteMultiIndex n → ℝ) :
    (loweredCoefficients n c j).sum (fun pq a => w pq * Complex.normSq a) =
      c.sum (fun pq a => w (lowerHermiteIndex j pq) *
        (n * pq.2 j : ℕ) * Complex.normSq a) := by
  classical
  unfold Finsupp.sum
  have hreindex :
      (∑ pq ∈ c.support.filter (fun pq => 0 < pq.2 j),
        w (lowerHermiteIndex j pq) * Complex.normSq
          ((Real.sqrt (n * pq.2 j : ℕ) : ℂ) * c pq)) =
      ∑ b ∈ (loweredCoefficients n c j).support,
        w b * Complex.normSq (loweredCoefficients n c j b) := by
    apply Finset.sum_bij (fun pq _ => lowerHermiteIndex j pq)
    · intro pq hpq
      rw [mem_support_loweredCoefficients_iff n hn]
      exact ⟨pq, (Finset.mem_filter.mp hpq).1, (Finset.mem_filter.mp hpq).2, rfl⟩
    · intro a ha b hb hab
      exact lowerHermiteIndex_injective_of_positive j
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
    · intro b hb
      rw [mem_support_loweredCoefficients_iff n hn] at hb
      obtain ⟨pq, hpq, hpos, rfl⟩ := hb
      exact ⟨pq, Finset.mem_filter.mpr ⟨hpq, hpos⟩, rfl⟩
    · intro pq hpq
      rw [loweredCoefficients_apply_lowerHermiteIndex n c j pq
        (Finset.mem_filter.mp hpq).2]
  rw [← hreindex, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pq hpq
  split_ifs with hpos
  · rw [Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by positivity)]
    ring
  · have hz : pq.2 j = 0 := by omega
    simp [hz]

/-- Exact total second-lowering energy for a genuine finite Hermite vector. -/
theorem sum_norm_sq_second_lowered (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ k : Fin n, ∑ j : Fin n,
      ‖finiteHermiteCombination n hn
        (loweredCoefficients n (loweredCoefficients n c k) j)‖ ^ 2) =
      c.sum (fun pq a => (n ^ 2 *
        (totalAntiDegree pq * (totalAntiDegree pq - 1)) : ℕ) * Complex.normSq a) := by
  classical
  simp_rw [norm_sq_finiteHermiteCombination_lowered,
    loweredCoefficients_weighted_normSq_sum n hn]
  unfold Finsupp.sum
  simp_rw [← Finset.sum_comm (s := c.support) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro pq hpq
  simp only [lowerHermiteIndex, Nat.cast_mul, Nat.cast_pow]
  have he : (∑ k : Fin n, ∑ j : Fin n,
      (pq.2 k : ℝ) * (lowerAt pq.2 k j : ℝ)) =
      (totalAntiDegree pq * (totalAntiDegree pq - 1) : ℕ) := by
    exact_mod_cast sum_second_lowering_weights pq.2
  calc
    (∑ k, ∑ j, (n : ℝ) * (lowerAt pq.2 k j : ℝ) *
      ((n : ℝ) * (pq.2 k : ℝ)) * Complex.normSq (c pq)) =
        (n : ℝ) ^ 2 * (∑ k, ∑ j,
          (pq.2 k : ℝ) * (lowerAt pq.2 k j : ℝ)) * Complex.normSq (c pq) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [he]; push_cast; ring

/-- The twice-lowered synthesis is the actual pointwise second Wirtinger derivative. -/
theorem second_dbarComponent_finiteHermiteFunction (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j k : Fin n) (z : Configuration n) :
    dbarComponent (dbarComponent (finiteHermiteFunction n hn c) k) j z =
      finiteHermiteFunction n hn
        (loweredCoefficients n (loweredCoefficients n c k) j) z := by
  have h : dbarComponent (finiteHermiteFunction n hn c) k =
      finiteHermiteFunction n hn (loweredCoefficients n c k) := by
    funext w
    exact dbarComponent_finiteHermiteFunction n hn c k w
  rw [h, dbarComponent_finiteHermiteFunction]

end
end GinibrePoincare.ComplexHermite


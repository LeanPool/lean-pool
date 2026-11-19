/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesNormalization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodrigues

/-! The exact factorial and Gaussian-precision constants in Rodrigues' formula. -/

@[expose] public section
open scoped ComplexConjugate
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

theorem rodrigues_normalization_coefficient (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    ((oneDimNormalization n p*oneDimNormalization n q : ℝ) : ℂ)*(-(n : ℂ))^(-(p+q : ℤ)) =
      (-1 : ℂ)^(p+q)/
        ((Real.sqrt (p.factorial*q.factorial : ℕ) : ℂ)*(Real.sqrt (n : ℝ) : ℂ)^(p+q)) := by
  let r : ℂ := (Real.sqrt (n : ℝ) : ℂ)
  have hr : r ≠ 0 := by
    dsimp [r]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn)))
  have hr2 : r^2=(n : ℂ) := by
    dsimp [r]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  have hp : Real.sqrt (p.factorial : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos p))
  have hq : Real.sqrt (q.factorial : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos q))
  have hs : (Real.sqrt (p.factorial*q.factorial : ℕ) : ℂ)=
      (Real.sqrt (p.factorial : ℝ) : ℂ)*(Real.sqrt (q.factorial : ℝ) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  rw [hs,← Nat.cast_add, zpow_neg, zpow_natCast]
  unfold oneDimNormalization
  push_cast
  change (r^p/(Real.sqrt (p.factorial : ℝ) : ℂ)*
      (r^q/(Real.sqrt (q.factorial : ℝ) : ℂ)))*((-(n : ℂ))^(p+q))⁻¹ =
    (-1 : ℂ)^(p+q)/((Real.sqrt (p.factorial : ℝ) : ℂ)*
      (Real.sqrt (q.factorial : ℝ) : ℂ)*r^(p+q))
  rw [← hr2]
  have hm : ((-1 : ℂ)^(p+q))^2=1 := by
    rw [← pow_mul, Nat.mul_comm (p+q) 2, pow_mul]
    norm_num
  have hden : (-r^2)^(p+q) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (pow_ne_zero _ hr))
  have hp' := Complex.ofReal_ne_zero.mpr hp
  have hq' := Complex.ofReal_ne_zero.mpr hq
  field_simp
  rw [show (-r^2)^(p+q)=(-1 : ℂ)^(p+q)*(r^2)^(p+q) by rw [neg_pow]]
  have hrp : (r^2)^(p+q) = (r^(p+q))^2 := by
    simp only [← pow_mul]
    congr 1
    omega
  rw [← pow_add,← pow_two, hrp]
  linear_combination -(r^(p+q))^2*hm

/-- The paper's literal one-variable factorial-normalized Rodrigues formula. -/
theorem normalizedEval_rodrigues_factorial (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    normalizedEval n hn p q z =
      (-1 : ℂ)^(p+q)/
        ((Real.sqrt (p.factorial*q.factorial : ℕ) : ℂ)*(Real.sqrt (n : ℝ) : ℂ)^(p+q))*
      (Real.exp ((n : ℝ)*Complex.normSq z) : ℂ)*
      (dbarOnePublic^[p] (dholOne^[q] (rodriguesGaussian n))) z := by
  rw [normalizedEval_rodrigues n hn, rodrigues_normalization_coefficient n hn]

end
end ComplexHermite
end GinibrePoincare

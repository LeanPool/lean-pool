/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodrigues.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesPolynomial
public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesRaising

/-! Actual mixed Wirtinger Rodrigues formula for the complex Hermite polynomials. -/

@[expose] public section
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

theorem eval_raise_left (ρ : ℝ) (p q : ℕ) (z : ℂ) :
    eval ρ (p+1) q z=z*eval ρ p q z-(ρ : ℂ)*(q : ℂ)*eval ρ p (q-1) z := by
  unfold eval
  rw [raw_raise_left]
  simp [Z]

theorem dbar_weighted_raw_raise (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    dbarOnePublic (fun w => eval ((n : ℝ)⁻¹) p q w*rodriguesGaussian n w) z =
      -(n : ℂ)*eval ((n : ℝ)⁻¹) (p+1) q z*rodriguesGaussian n z := by
  rw [rodrigues_dbar_weighted_raw, eval_raise_left]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
 ; ring

/-- Literal actual Gaussian derivative, with all smoothness derived internally. -/
theorem iterate_wirtinger_rodrigues_raw (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    dbarOnePublic^[p] (dholOne^[q] (rodriguesGaussian n)) =
      fun z => (-(n : ℂ))^(p+q)*eval ((n : ℝ)⁻¹) p q z*rodriguesGaussian n z := by
  induction p with
  | zero =>
    rw [Function.iterate_zero, iterate_dholOne_rodriguesGaussian]
    funext z
    simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih]
    funext z
    have hP : Differentiable ℝ (eval ((n : ℝ)⁻¹) p q) :=
      (contDiff_diagonalEvalPublic (raw ((n : ℝ)⁻¹) p q)).differentiable (by simp)
    have hG := (contDiff_rodriguesGaussian n).differentiable (by simp)
    rw [show (fun z => (-(n : ℂ))^(p+q)*eval ((n : ℝ)⁻¹) p q z*rodriguesGaussian n z) =
      fun z => (-(n : ℂ))^(p+q)*(eval ((n : ℝ)⁻¹) p q z*rodriguesGaussian n z) by funext w; ring,
      dbarOne_const_mul (hP.fun_mul hG), dbar_weighted_raw_raise n hn]
    rw [show p+1+q=p+q+1 by omega, pow_succ]
    ring

/-- Univariate normalized Rodrigues identity with the actual Gaussian and actual
iterated real-Fréchet Wirtinger operators. -/
theorem normalizedEval_rodrigues (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    normalizedEval n hn p q z =
      ((oneDimNormalization n p*oneDimNormalization n q : ℝ) : ℂ)*
        (-(n : ℂ))^(-(p+q : ℤ))*
        (Real.exp ((n : ℝ)*Complex.normSq z) : ℂ)*
        (dbarOnePublic^[p] (dholOne^[q] (rodriguesGaussian n))) z := by
  rw [iterate_wirtinger_rodrigues_raw n hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (-(n : ℂ))^(-(p+q : ℤ)) = ((-(n : ℂ))^(p+q))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  rw [hp]
  unfold normalizedEval normalized rodriguesGaussian eval
  simp only [map_mul, MvPolynomial.eval_C]
  have he : (Real.exp ((n : ℝ)*Complex.normSq z) : ℂ)*
      (Real.exp (-(n : ℝ)*Complex.normSq z) : ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    have hz : (n : ℝ)*Complex.normSq z+ -(n : ℝ)*Complex.normSq z=0 := by ring
    rw [hz]
    simp
  have hpow : (-(n : ℂ))^(p+q) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hn')
  field_simp
  simp only [one_div, neg_mul] at *
  linear_combination -((oneDimNormalization n p*oneDimNormalization n q : ℝ) : ℂ)*
    MvPolynomial.eval ![z, conj z] (raw ((n : ℝ)⁻¹) p q)*he

end
end ComplexHermite
end GinibrePoincare

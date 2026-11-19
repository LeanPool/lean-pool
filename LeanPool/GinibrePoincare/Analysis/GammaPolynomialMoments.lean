/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GammaPolynomialMoments.lean.
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

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Gamma polynomial moments

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `gammaMoment_succ`, `gammaIntegral_monomial`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators
namespace GinibrePoincare.Laguerre
noncomputable section

/-- Integer-shape Gamma moments at rate one. -/
def gammaMoment (k j : ℕ) : ℝ := ((k+j-1).factorial : ℝ) / ((k-1).factorial : ℝ)

private theorem gamma_nat_shape (k : ℕ) (hk : 0 < k) :
    Real.Gamma (k : ℝ) = ((k-1).factorial : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [Nat.cast_add, Real.Gamma_nat_eq_factorial]

private theorem gamma_weighted_power (k j : ℕ) (hk : 0 < k) :
    (fun x : ℝ => x^j * gammaPDFReal (k : ℝ) 1 x) =
      (Ici 0).indicator (fun x => (1 / ((k-1).factorial : ℝ)) *
        (x^(k+j-1) * Real.exp (-x))) := by
  funext x
  have he : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  have hj : k+j-1 = j+(k-1) := by omega
  by_cases hx : 0 ≤ x
  · simp only [gammaPDFReal, ite_true, gamma_nat_shape k hk,
      ← he, Real.rpow_natCast, one_mul, Set.indicator, mem_Ici, hx, ite_true, hj, pow_add]
    ring
  · simp [gammaPDFReal, hx, Set.indicator]

private theorem integrable_pow_exp (j : ℕ) :
    IntegrableOn (fun x : ℝ => x^j * Real.exp (-x)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (j : ℝ)+1) (by positivity)
  simpa [Real.rpow_natCast, mul_comm] using h

private theorem integral_pow_exp (j : ℕ) :
    (∫ x : ℝ in Ioi 0, x^j * Real.exp (-x)) = (j.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ)+1) (r := 1)
    (by positivity) (by norm_num)
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

/-- All nonnegative integer powers are genuinely integrable under the Gamma law. -/
theorem integrable_pow_gamma (k j : ℕ) (hk : 0 < k) :
    Integrable (fun x : ℝ => x^j) (gammaMeasure (k : ℝ) 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold gammaMeasure
  rw [integrable_withDensity_iff (f := gammaPDF (k : ℝ) 1) (μ := volume) (by unfold gammaPDF;
                                                                               fun_prop)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg (a := (k : ℝ)) (r := 1) hkR (by
      norm_num) _)]
  rw [gamma_weighted_power k j hk, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrable_pow_exp (k+j-1)).const_mul _

/-- Exact moments of the actual integer-shape Gamma distribution. -/
theorem integral_pow_gamma (k j : ℕ) (hk : 0 < k) :
    (∫ x : ℝ, x^j ∂gammaMeasure (k : ℝ) 1) = gammaMoment k j := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF (k : ℝ) 1) (μ := volume) (by
      unfold gammaPDF; fun_prop)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg (a := (k : ℝ)) (r := 1) hkR (by
      norm_num) _), smul_eq_mul]
  rw [show (fun x : ℝ => gammaPDFReal (k : ℝ) 1 x * x^j) =
      (fun x : ℝ => x^j * gammaPDFReal (k : ℝ) 1 x) by funext x; ring,
    gamma_weighted_power k j hk, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi, integral_const_mul, integral_pow_exp]
  simp [gammaMoment, div_eq_mul_inv, mul_comm]

/-- Gamma moments satisfy the rising-factorial recurrence. -/
theorem gammaMoment_succ (k j : ℕ) (hk : 0 < k) :
    gammaMoment k (j+1) = ((k : ℝ)+j) * gammaMoment k j := by
  have he : k+(j+1)-1 = (k+j-1)+1 := by omega
  have he' : (k+j-1)+1 = k+j := by omega
  unfold gammaMoment
  rw [he, Nat.factorial_succ, he']
  push_cast
  ring

/-- Every polynomial is integrable under the actual Gamma distribution. -/
theorem integrable_polynomial_gamma (k : ℕ) (hk : 0 < k) (P : Polynomial ℝ) :
    Integrable (fun x => P.eval x) (gammaMeasure (k : ℝ) 1) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.fun_add hQ
  | monomial j a => simpa using (integrable_pow_gamma k j hk).const_mul a

/-- Integration against the actual Gamma measure as a linear functional on polynomials. -/
def gammaIntegral (k : ℕ) (hk : 0 < k) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ x, P.eval x ∂gammaMeasure (k : ℝ) 1
  map_add' P Q := by
    simp only [Polynomial.eval_add]
    exact integral_add (integrable_polynomial_gamma k hk P) (integrable_polynomial_gamma k hk Q)
  map_smul' c P := by simp [Polynomial.eval_smul, integral_const_mul]

/-- The Gamma polynomial functional evaluates monomials by the exact moment formula. -/
theorem gammaIntegral_monomial (k : ℕ) (hk : 0 < k) (j : ℕ) (a : ℝ) :
    gammaIntegral k hk (Polynomial.monomial j a) = a * gammaMoment k j := by
  simp [gammaIntegral, Polynomial.eval_monomial, integral_const_mul, integral_pow_gamma k j hk]

end
end GinibrePoincare.Laguerre

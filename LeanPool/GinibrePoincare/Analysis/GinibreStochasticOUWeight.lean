/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOUWeight.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreOUTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Concrete exponential OU convolution and variance weights -/

@[expose] public section
open MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Deterministic weight of the Brownian increment in the actual OU convolution. -/
def ginibreOUStochasticWeight (rate : ℝ≥0) (t s : ℝ) : ℝ :=
  Real.sqrt (rate : ℝ) * Real.exp (-(rate : ℝ) * (t - s))

theorem ginibreOUStochasticWeight_hasDerivAt (rate : ℝ≥0) (t s : ℝ) :
    HasDerivAt (ginibreOUStochasticWeight rate t)
      ((rate : ℝ) * ginibreOUStochasticWeight rate t s) s := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(rate : ℝ) * (t - u)))
      (Real.exp (-(rate : ℝ) * (t - s)) * (rate : ℝ)) s := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_mul_neg, mul_one] using
      (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-(rate : ℝ))).exp
  have hh : HasDerivAt (ginibreOUStochasticWeight rate t)
      (Real.sqrt (rate : ℝ) * (Real.exp (-(rate : ℝ) * (t - s)) * (rate : ℝ))) s :=
    he.const_mul (Real.sqrt (rate : ℝ))
  convert hh using 1
  unfold ginibreOUStochasticWeight
  ring

theorem ginibreOUStochasticWeight_sq (rate : ℝ≥0) (t s : ℝ) :
    ginibreOUStochasticWeight rate t s ^ 2 =
      (rate : ℝ) * Real.exp (2 * (-(rate : ℝ) * (t - s))) := by
  rw [ginibreOUStochasticWeight, mul_pow, Real.sq_sqrt rate.coe_nonneg,
    pow_two, ← Real.exp_add]
  congr 2
  ring

theorem ginibreOUStochasticWeight_sq_hasDerivAt (rate : ℝ≥0) (t s : ℝ) :
    HasDerivAt (fun u => ginibreOUStochasticWeight rate t u ^ 2)
      (2 * (rate : ℝ) * ginibreOUStochasticWeight rate t s ^ 2) s := by
  have hh : HasDerivAt (fun u : ℝ => ginibreOUStochasticWeight rate t u ^ 2)
      (2 * ginibreOUStochasticWeight rate t s *
        ((rate : ℝ) * ginibreOUStochasticWeight rate t s)) s := by
    convert! (ginibreOUStochasticWeight_hasDerivAt rate t s).pow 2 using 1;
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  convert hh using 1
  ring

theorem ginibreOUStochasticWeight_variance_integral (rate t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), ginibreOUStochasticWeight rate t s ^ 2) =
      (ginibreOUVariance rate t : ℝ) := by
  have hd (s : ℝ) : HasDerivAt
      (fun u => (1 / 2 : ℝ) * Real.exp (2 * (-(rate : ℝ) * ((t : ℝ) - u))))
      (ginibreOUStochasticWeight rate t s ^ 2) s := by
    have he : HasDerivAt
        (fun u : ℝ => Real.exp (2 * (-(rate : ℝ) * ((t : ℝ) - u))))
        (Real.exp (2 * (-(rate : ℝ) * ((t : ℝ) - s))) * (2 * (rate : ℝ))) s := by
      simpa only [Pi.sub_apply, id_eq, zero_sub, neg_mul_neg, mul_one] using
        ((((hasDerivAt_const s (t : ℝ)).sub (hasDerivAt_id s)).const_mul
          (-(rate : ℝ))).const_mul 2).exp
    have hh : HasDerivAt
        (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (2 * (-(rate : ℝ) * ((t : ℝ) - u))))
        ((1 / 2 : ℝ) * (Real.exp (2 * (-(rate : ℝ) * ((t : ℝ) - s))) *
          (2 * (rate : ℝ)))) s := he.const_mul (1 / 2 : ℝ)
    convert hh using 1
    rw [ginibreOUStochasticWeight_sq]
    ring
  have hint : IntervalIntegrable (fun s => ginibreOUStochasticWeight rate t s ^ 2)
      volume 0 t := by
    unfold ginibreOUStochasticWeight
    exact (by fun_prop : Continuous (fun s : ℝ =>
      (Real.sqrt (rate : ℝ) * Real.exp (-(rate : ℝ) * ((t : ℝ) - s))) ^ 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hint,
    ginibreOUVariance_coe]
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero, ginibreOUDecay]
  rw [pow_two, ← Real.exp_add]
  ring_nf

end
end GinibrePoincare

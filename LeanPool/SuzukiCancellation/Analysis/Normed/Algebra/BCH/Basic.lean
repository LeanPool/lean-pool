/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Logarithm

/-!
# The Baker–Campbell–Hausdorff element

The BCH element is `log (exp a * exp b)`, using Mathlib's exponential and logarithm.
Its definition is available in a topological ring; the inverse identity needs the
Banach-algebra hypotheses and the sufficient bound `‖a‖ + ‖b‖ < log 2`.

## Main results

* `exp_bch`: the exponential of the BCH element is the product of exponentials.
* `bch_eq_add_of_commute`: commuting inputs give their sum in the convergence range.
* `bch_zero`, `zero_bch`: zero is a local identity for the BCH operation.
* `norm_bch_sub_le_of_logPartialSum`: transfer a finite logarithm error to BCH.
* `norm_bch_sub_le_div_of_logPartialSum`: combine homogeneous polynomial and scalar tail budgets.

Quantitative commutator bounds are in `BCHCommutator`; the analytic exp/log facts
are in `FQFP.Analysis.Normed.Algebra.Logarithm`.
-/

@[expose] public noncomputable section

open NormedSpace

namespace FQFP.BCH

/-- The BCH element is the logarithm of the ordered product of exponentials. -/
def bch {𝔸 : Type*} [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]
    (a b : 𝔸) : 𝔸 := log (exp a * exp b)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- **The structural BCH theorem** on the sufficient convergence range `‖a‖ + ‖b‖ < log 2`. -/
theorem exp_bch (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    exp (bch a b) = exp a * exp b :=
  exp_log (norm_exp_mul_exp_sub_one_lt_one a b hab)

/-- For commuting inputs, the BCH element is their sum on the convergence range. -/
theorem bch_eq_add_of_commute {a b : 𝔸} (h : Commute a b)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) : bch a b = a + b := by
  rw [bch, ← exp_add_of_commute h]
  exact log_exp_of_norm_lt _ ((norm_add_le a b).trans_lt hab)

/-- Zero is a right identity for BCH on the convergence range. -/
@[simp]
theorem bch_zero (a : 𝔸) (ha : ‖a‖ < Real.log 2) : bch a 0 = a := by
  simpa using bch_eq_add_of_commute (Commute.zero_right a) (by simpa using ha)

/-- Zero is a left identity for BCH on the convergence range. -/
@[simp]
theorem zero_bch (a : 𝔸) (ha : ‖a‖ < Real.log 2) : bch 0 a = a := by
  simpa using bch_eq_add_of_commute (Commute.zero_left a) (by simpa using ha)

/-- A finite logarithm approximation gives a BCH bound after adding its analytic tail. -/
theorem norm_bch_sub_le_of_logPartialSum (a b C : 𝔸) (n : ℕ) {B : ℝ}
    (hab : ‖a‖ + ‖b‖ < Real.log 2)
    (hpoly : ‖logPartialSum 𝔸 n (exp a * exp b - 1) - C‖ ≤ B) :
    ‖bch a b - C‖ ≤
      (Real.exp (‖a‖ + ‖b‖) - 1) ^ n / (2 - Real.exp (‖a‖ + ‖b‖)) + B := by
  have he : Real.exp (‖a‖ + ‖b‖) < 2 := by
    calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono hab
         _ = 2 := Real.exp_log (by norm_num)
  have hlog := norm_log_one_add_sub_logPartialSum_le_of_norm_le
    (exp a * exp b - 1) n (norm_exp_mul_exp_sub_one_le a b)
    (show Real.exp (‖a‖ + ‖b‖) - 1 < 1 by linarith only [he])
  rw [show 1 + (exp a * exp b - 1) = exp a * exp b by abel] at hlog
  have hdecomp : bch a b - C =
      (log (exp a * exp b) - logPartialSum 𝔸 n (exp a * exp b - 1)) +
        (logPartialSum 𝔸 n (exp a * exp b - 1) - C) := by rw [bch]; abel
  rw [hdecomp]
  simpa only [show 1 - (Real.exp (‖a‖ + ‖b‖) - 1) =
    2 - Real.exp (‖a‖ + ‖b‖) by ring, div_eq_mul_inv] using norm_add_le_of_le hlog hpoly

/-- Homogeneous finite logarithm and scalar tail budgets give a BCH remainder bound. -/
theorem norm_bch_sub_le_div_of_logPartialSum (a b C : 𝔸) (n : ℕ) {B E K : ℝ}
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hB : 0 ≤ B)
    (hpoly : ‖logPartialSum 𝔸 n (exp a * exp b - 1) - C‖ ≤ B * (‖a‖ + ‖b‖) ^ n)
    (hexp : (Real.exp (‖a‖ + ‖b‖) - 1) ^ n ≤ E * (‖a‖ + ‖b‖) ^ n)
    (hbudget : E + B ≤ K) :
    ‖bch a b - C‖ ≤ K * (‖a‖ + ‖b‖) ^ n / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  obtain ⟨hd, hd1⟩ := exp_log_two_denominator_bounds hs hab
  have hBtail : B * s ^ n * (2 - Real.exp s) ≤ B * s ^ n := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hd1 (mul_nonneg hB (pow_nonneg hs n))
  calc
    _ ≤ (Real.exp s - 1) ^ n / (2 - Real.exp s) + B * s ^ n :=
      norm_bch_sub_le_of_logPartialSum a b C n hab hpoly
    _ ≤ (E + B) * s ^ n / (2 - Real.exp s) := by
      rw [div_add' _ _ _ (ne_of_gt hd)]
      apply div_le_div_of_nonneg_right _ hd.le
      exact (add_le_add hexp hBtail).trans_eq (by ring)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget (pow_nonneg hs n)) hd.le

end FQFP.BCH

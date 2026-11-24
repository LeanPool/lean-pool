/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialDerivative

/-!
# Formal logarithms of palindromic exponential products

Reversal and negation invert an ordered exponential product. Uniqueness of
formal logarithms therefore makes the logarithm of every palindrome odd.

## Main results

* `formalLog_eq_neg_of_mul_eq_one`: logarithms of inverse series are negatives.
* `expListLogCoeff_eq_zero_of_reverse_eq`: every even coefficient vanishes.
-/

@[expose] public noncomputable section

namespace FQFP

open PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Reversing and negating the arguments gives a right inverse. -/
theorem expListSeries_mul_reverse_neg (l : List A) :
    expListSeries l * expListSeries (l.reverse.map Neg.neg) = 1 := by
  induction l with
  | nil => simp [expListSeries_nil]
  | cons a l ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        expListSeries_append, expListSeries_cons_eq_exponentialCurve, expListSeries_nil,
        mul_one]
      rw [mul_assoc, ← mul_assoc (expListSeries l), ih, one_mul,
        exponentialCurve_mul_neg]

/-- Formal logarithms of mutually inverse unit-constant series are negatives. -/
theorem formalLog_eq_neg_of_mul_eq_one (p q : PowerSeries A)
    (hp : constantCoeff p = 1) (hpq : p * q = 1) :
    formalLog q = -formalLog p := by
  have hi : formalExp (-formalLog p) * p = 1 := by
    simpa only [neg_neg, formalExp_formalLog p hp] using
      formalExp_mul_neg (-formalLog p) (by simp)
  have hqexp : q = formalExp (-formalLog p) := by
    calc
      q = (formalExp (-formalLog p) * p) * q := by rw [hi, one_mul]
      _ = formalExp (-formalLog p) := by rw [mul_assoc, hpq, mul_one]
  rw [hqexp, formalLog_formalExp _ (by simp)]

/-- Negating a reversed exponential list negates its formal logarithm. -/
theorem expListLogCoeff_reverse_neg (l : List A) (n : ℕ) :
    expListLogCoeff (l.reverse.map Neg.neg) n = -expListLogCoeff l n := by
  have h := congrArg (coeff n) (formalLog_eq_neg_of_mul_eq_one
    (expListSeries l) (expListSeries (l.reverse.map Neg.neg))
    (by simp [expListSeries]) (expListSeries_mul_reverse_neg l))
  simpa only [coeff_formalLog_expListSeries, map_neg] using h

/-- Every even homogeneous logarithm coefficient of a palindrome vanishes. -/
theorem expListLogCoeff_eq_zero_of_reverse_eq (l : List A) (hl : l.reverse = l)
    (n : ℕ) (hn : Even n) : expListLogCoeff l n = 0 := by
  have h := expListLogCoeff_reverse_neg l n
  rw [hl, show l.map Neg.neg = l.map (fun a ↦ (-1 : ℚ) • a) by simp,
    expListLogCoeff_smul, hn.neg_one_pow, one_smul] at h
  have htwo : (2 : ℚ) • expListLogCoeff l n = 0 := by
    simpa only [two_smul] using (neg_eq_iff_add_eq_zero.mp h.symm)
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- A palindromic exponential product agrees quadratically with the exponential of its sum. -/
theorem expListTerm_two_of_reverse_eq (l : List A) (hl : l.reverse = l) :
    expListTerm l 2 = (2 : ℚ)⁻¹ • l.sum ^ 2 := by
  have he := expListLogCoeff_eq_zero_of_reverse_eq l hl 2 (by decide)
  norm_num [expListLogCoeff, Finset.sum_range_succ, positivePowerCoeff, ← sq] at he
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using he)

end FQFP

/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SymmetricDefectSeries
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.ConjugationCoefficients

/-!
# Formal coefficients of ordered conjugations

The multinomial conjugation coefficients agree with coefficients of the
corresponding formal exponential products. Low coefficients can consequently
be read directly from the jet of a transport and its formal inverse.

## Main results

* `coeff_expListSeries_conjugate`: formal and multinomial conjugation coefficients agree.
* `coeff_expListSeries_reverse_two_of_one_eq_zero`: reversal negates the quadratic term.
* `coeff_conjugate_two_of_one_eq_zero`: the quadratic coefficient is a single bracket.
* `coeff_conjugate_three_of_one_eq_zero_of_three_eq_zero`: the cubic coefficient vanishes.
-/

@[expose] public noncomputable section

open Finset PowerSeries

namespace FQFP

variable {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]

/-- Formal ordered conjugations have exactly the multinomial coefficients. -/
theorem coeff_expListSeries_conjugate {s : ℕ} (Z : Fin s → A) (B : A) (n : ℕ) :
    coeff n (expListSeries (List.ofFn Z).reverse * C B *
      expListSeries ((List.ofFn Z).map Neg.neg)) = TrotterError.conjCoeff Z B n := by
  induction s generalizing n with
  | zero =>
      by_cases hn : n = 0
      · subst n
        simp [TrotterError.conjCoeff_zero, expListSeries_nil]
      · simp [TrotterError.conjCoeff_empty, hn, expListSeries_nil, coeff_C]
  | succ s ih =>
      rw [List.ofFn_succ', List.concat_eq_append]
      simp only [List.reverse_append, List.reverse_singleton, List.map_append,
        List.map_singleton, expListSeries_append,
        expListSeries_cons_eq_exponentialCurve, expListSeries_nil, mul_one]
      rw [show exponentialCurve (Z (Fin.last s)) *
          expListSeries (List.ofFn fun i ↦ Z i.castSucc).reverse * C B *
          (expListSeries ((List.ofFn fun i ↦ Z i.castSucc).map Neg.neg) *
            exponentialCurve (-Z (Fin.last s))) =
          exponentialCurve (Z (Fin.last s)) *
            (expListSeries (List.ofFn fun i ↦ Z i.castSucc).reverse * C B *
              expListSeries ((List.ofFn fun i ↦ Z i.castSucc).map Neg.neg)) *
                exponentialCurve (-Z (Fin.last s)) by noncomm_ring]
      rw [coeff_exponentialCurve_conjugate, TrotterError.conjCoeff_succ]
      simp only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_inv, Rat.cast_natCast,
        ad_rat_pow_eq_adPow, ih]

omit [Algebra ℝ A] in
/-- Reversing a zero-linear exponential list negates its quadratic coefficient. -/
theorem coeff_expListSeries_reverse_two_of_one_eq_zero (l : List A)
    (h1 : coeff 1 (expListSeries l) = 0) :
    coeff 2 (expListSeries l.reverse) = -coeff 2 (expListSeries l) := by
  let Q := expListSeries (l.map Neg.neg)
  have hQ0 : coeff 0 Q = 1 := by simp [Q, expListSeries]
  have hV0 : coeff 0 (expListSeries l.reverse) = 1 := by simp [expListSeries]
  have hscale (k : ℕ) : coeff k Q = (-1 : ℚ) ^ k • coeff k (expListSeries l) := by
    dsimp [Q]
    rw [coeff_expListSeries, coeff_expListSeries,
      show l.map Neg.neg = l.map (fun a ↦ (-1 : ℚ) • a) by simp,
      expListTerm_smul]
  have hQ1 : coeff 1 Q = 0 := by rw [hscale, h1, smul_zero]
  have hQ2 : coeff 2 Q = coeff 2 (expListSeries l) := by
    rw [hscale]
    norm_num
  have hinv : Q * expListSeries l.reverse = 1 := by
    simpa [Q] using expListSeries_mul_reverse_neg (l.map Neg.neg)
  have h := congrArg (coeff 2) hinv
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, hQ0, hV0, hQ1, hQ2] at h
  simpa only [coeff_expListSeries] using eq_neg_of_add_eq_zero_left h

omit [Algebra ℝ A] [Algebra ℚ A] in
/-- A transport with no linear term conjugates quadratically by its quadratic coefficient. -/
theorem coeff_conjugate_two_of_one_eq_zero (U V : PowerSeries A) (B : A)
    (hUV : U * V = 1) (hU0 : coeff 0 U = 1) (hV0 : coeff 0 V = 1)
    (hU1 : coeff 1 U = 0) :
    coeff 2 (U * C B * V) = ⁅coeff 2 U, B⁆ := by
  have h1 := congrArg (coeff 1) hUV
  have h2 := congrArg (coeff 2) hUV
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero, hU0, hV0, hU1, Nat.reduceAdd, Nat.reduceSub,
    mul_one, one_mul, zero_mul, mul_zero, add_zero, zero_add, coeff_one,
    ite_false] at h1 h2
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero, coeff_C, hU0, hV0, hU1, h1,
    Nat.reduceAdd, Nat.reduceSub, mul_one, one_mul, zero_mul, mul_zero,
    add_zero, zero_add]
  rw [show coeff 2 V = -coeff 2 U from eq_neg_of_add_eq_zero_left h2]
  simp only [Ring.lie_def, mul_neg]
  abel

omit [Algebra ℝ A] [Algebra ℚ A] in
/-- Vanishing linear and cubic transport coefficients also cancel the cubic conjugation. -/
theorem coeff_conjugate_three_of_one_eq_zero_of_three_eq_zero
    (U V : PowerSeries A) (B : A) (hUV : U * V = 1)
    (hU0 : coeff 0 U = 1) (hV0 : coeff 0 V = 1)
    (hU1 : coeff 1 U = 0) (hU3 : coeff 3 U = 0) :
    coeff 3 (U * C B * V) = 0 := by
  have h1 := congrArg (coeff 1) hUV
  have h3 := congrArg (coeff 3) hUV
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero, hU0, hV0, hU1, Nat.reduceAdd, Nat.reduceSub,
    mul_one, one_mul, zero_mul, mul_zero, add_zero, zero_add, coeff_one,
    ite_false] at h1
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero, hU0, hV0, hU1, hU3, h1,
    Nat.reduceAdd, Nat.reduceSub, mul_one, one_mul, zero_mul, mul_zero,
    add_zero, zero_add, coeff_one, ite_false] at h3
  norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero, coeff_C, hU0, hV0, hU1, hU3, h1, h3,
    Nat.reduceAdd, Nat.reduceSub, mul_one, one_mul, zero_mul, mul_zero,
    add_zero, zero_add]

end FQFP

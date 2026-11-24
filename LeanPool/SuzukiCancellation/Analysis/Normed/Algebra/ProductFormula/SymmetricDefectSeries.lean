/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.GroupedConjugation
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Conjugation
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Palindromic

/-!
# Formal coefficients of symmetric defects

The logarithmic half-defect has the same finite coefficient recurrence as the
actual conjugation recurrence. Formal differentiation and inverse products keep
this identification independent of estimates and matrix representations.

## Main results

* `coeff_halfDefectSeries`: coefficients are the grouped conjugation coefficients.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries TrotterError

section

variable {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The formal logarithmic half-defect, with an explicit inverse exponential list. -/
def halfDefectSeries (l : List A) (G : A) : PowerSeries A :=
  expListSeries (l.reverse.map Neg.neg) * seriesDerivative (expListSeries l) -
    (1 / 2 : ℝ) • (expListSeries (l.reverse.map Neg.neg) * C G * expListSeries l)

/-- Rational and real adjoint powers agree on the underlying associative ring. -/
lemma ad_rat_pow_eq_adPow (a b : A) (n : ℕ) :
    (LieAlgebra.ad ℚ A a ^ n) b = adPow a n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, LieAlgebra.ad_apply, ad_pow_succ, ih]

omit [Algebra ℝ A] in
/-- Reversed negative exponential lists are also left inverses. -/
lemma expListSeries_reverse_neg_mul (l : List A) :
    expListSeries (l.reverse.map Neg.neg) * expListSeries l = 1 := by
  simpa [← List.map_reverse, List.map_map] using
    expListSeries_mul_reverse_neg (l.reverse.map Neg.neg)

omit [Algebra ℝ A] in
/-- Appending an exponential is multiplication by its formal exponential curve. -/
lemma expListSeries_append_singleton (l : List A) (a : A) :
    expListSeries (l ++ [a]) = expListSeries l * exponentialCurve a := by
  rw [expListSeries_append, expListSeries_cons_eq_exponentialCurve, expListSeries_nil, mul_one]

/-- The formal half-defect obeys the same conjugation-and-kick update as the actual one. -/
lemma halfDefectSeries_append_singleton (l : List A) (a G : A) :
    halfDefectSeries (l ++ [a]) G =
      exponentialCurve (-a) * halfDefectSeries l G * exponentialCurve a + C a := by
  have ha : exponentialCurve (-a) * C a = C a * exponentialCurve (-a) := by
    simpa only [map_neg, mul_neg, neg_mul, neg_inj] using exponentialCurve_mul_C (-a)
  simp only [halfDefectSeries, List.reverse_append, List.reverse_singleton, List.map_append,
    List.map_singleton, expListSeries_append,
    expListSeries_cons_eq_exponentialCurve, expListSeries_nil, mul_one,
    seriesDerivative_mul, seriesDerivative_exponentialCurve]
  simp only [mul_add, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
  simp only [← mul_assoc]
  rw [show exponentialCurve (-a) * expListSeries (l.reverse.map Neg.neg) *
      expListSeries l = exponentialCurve (-a) by
        rw [mul_assoc, expListSeries_reverse_neg_mul, mul_one]]
  rw [ha, mul_assoc (C a), show exponentialCurve (-a) * exponentialCurve a = 1 by
    simpa using exponentialCurve_mul_neg (-a), mul_one]
  abel

/-- The formal and grouped recursions have exactly the same normalized coefficients. -/
theorem coeff_halfDefectSeries {s : ℕ} (Z : Fin s → A) (G : A) (n : ℕ) :
    coeff n (halfDefectSeries (List.ofFn Z) G) =
      groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) n := by
  induction s generalizing n with
  | zero =>
      simp [halfDefectSeries, expListSeries_nil, groupedConjCoeff, coeff_C]
      split_ifs <;> simp_all
  | succ s ih =>
      rw [List.ofFn_succ', List.concat_eq_append, halfDefectSeries_append_singleton]
      simp only [map_add, coeff_C, groupedConjCoeff]
      congr 1
      rw [show coeff n (exponentialCurve (-Z (Fin.last s)) *
          halfDefectSeries (List.ofFn fun i ↦ Z i.castSucc) G *
          exponentialCurve (Z (Fin.last s))) = _ from
        by simpa only [neg_neg] using (coeff_exponentialCurve_conjugate (-Z (Fin.last s))
          (halfDefectSeries (List.ofFn fun i ↦ Z i.castSucc) G) n)]
      simp only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_inv, Rat.cast_natCast,
        ad_rat_pow_eq_adPow]
      apply sum_congr rfl
      intro q _
      rw [ih]

omit [Algebra ℚ A] in
/-- Simultaneous scaling of generators, kicks and seed preserves the total homogeneous degree. -/
lemma groupedConjCoeff_smul {s : ℕ} (Z K : Fin s → A) (B : A) (c : ℝ) (n : ℕ) :
    groupedConjCoeff (fun i ↦ c • Z i) (fun i ↦ c • K i) (c • B) n =
      c ^ (n + 1) • groupedConjCoeff Z K B n := by
  induction s generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [groupedConjCoeff, hn]
  | succ s ih =>
      simp only [groupedConjCoeff, ih, smul_add, smul_sum, adPow_smul_left,
        map_smul, smul_smul]
      congr 1
      · apply sum_congr rfl
        intro q hq
        congr 1
        calc
          _ = (c ^ q * c ^ (n - q + 1)) * (Nat.factorial q : ℝ)⁻¹ := by ring
          _ = _ := by
            rw [← pow_add, show q + (n - q + 1) = n + 1 by
              have := mem_range.mp hq
              lia]
      · by_cases hn : n = 0 <;> simp [hn]

/-- Reflection changes the degree-`n` half-defect coefficient by `(-1)^(n+1)`. -/
lemma coeff_halfDefectSeries_neg {s : ℕ} (Z : Fin s → A) (G : A) (n : ℕ) :
    coeff n (halfDefectSeries ((List.ofFn Z).map Neg.neg) (-G)) =
      (-1 : ℝ) ^ (n + 1) • coeff n (halfDefectSeries (List.ofFn Z) G) := by
  rw [List.map_ofFn, coeff_halfDefectSeries, coeff_halfDefectSeries]
  simpa [Function.comp_def] using
    groupedConjCoeff_smul (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) (-1) n

omit [Algebra ℝ A] in
/-- Differentiating the reverse half-product differentiates the inverse at reflected time. -/
lemma seriesDerivative_reverse_expListSeries (l : List A) :
    seriesDerivative (expListSeries l.reverse) =
      -(expListSeries l.reverse * seriesDerivative (expListSeries (l.map Neg.neg)) *
        expListSeries l.reverse) := by
  have hinv : expListSeries (l.map Neg.neg) * expListSeries l.reverse = 1 := by
    simpa using expListSeries_mul_reverse_neg (l.map Neg.neg)
  have hleft : expListSeries l.reverse * expListSeries (l.map Neg.neg) = 1 := by
    simpa using expListSeries_mul_reverse_neg l.reverse
  have hd := congrArg seriesDerivative hinv
  rw [seriesDerivative_mul, show seriesDerivative (1 : PowerSeries A) = 0 from
    by simpa using seriesDerivative_C (1 : A)] at hd
  have hh := congrArg (fun x ↦ expListSeries l.reverse * x) hd
  simp only [mul_add, ← mul_assoc, hleft, one_mul, mul_zero] at hh
  exact (eq_neg_of_add_eq_zero_right hh)

/-- The formal symmetric residual factors through the reflected half-defect. -/
theorem symmetricResidualSeries_eq_halfDefect (l : List A) (G : A) :
    seriesDerivative (expListSeries l * expListSeries l.reverse) -
      (1 / 2 : ℝ) • (C G * (expListSeries l * expListSeries l.reverse) +
        (expListSeries l * expListSeries l.reverse) * C G) =
      expListSeries l * (halfDefectSeries l G -
        halfDefectSeries (l.map Neg.neg) (-G)) * expListSeries l.reverse := by
  have hinv : expListSeries (l.map Neg.neg) * expListSeries l.reverse = 1 := by
    simpa using expListSeries_mul_reverse_neg (l.map Neg.neg)
  have hmap : ((l.map Neg.neg).reverse.map Neg.neg) = l.reverse := by
    simp [← List.map_reverse, List.map_map]
  rw [seriesDerivative_mul, seriesDerivative_reverse_expListSeries]
  simp only [halfDefectSeries, hmap, map_neg, mul_neg, neg_mul, smul_neg,
    sub_neg_eq_add, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  simp only [← mul_assoc, expListSeries_mul_reverse_neg, one_mul]
  simp only [mul_assoc, hinv, mul_one, smul_add]
  module

end

variable {A : Type*} [Semiring A]

/-- A unit-constant left factor preserves the first potentially nonzero coefficient. -/
lemma coeff_mul_eq_right_of_lt_eq_zero (U T : PowerSeries A) (n : ℕ)
    (hU : coeff 0 U = 1) (hT : ∀ k < n, coeff k T = 0) :
    coeff n (U * T) = coeff n T := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_eq_single 0]
  · simp [hU]
  · intro i hi hi0
    rw [hT (n - i) (by
      have := mem_range.mp hi
      lia), mul_zero]
  · simp

/-- A unit-constant right factor preserves the first potentially nonzero coefficient. -/
lemma coeff_mul_eq_left_of_lt_eq_zero (T V : PowerSeries A) (n : ℕ)
    (hV : coeff 0 V = 1) (hT : ∀ k < n, coeff k T = 0) :
    coeff n (T * V) = coeff n T := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_eq_single n]
  · simp [hV]
  · intro i hi hin
    rw [hT i (by
      have := mem_range.mp hi
      lia), zero_mul]
  · simp

/-- Transport by two unit-constant series preserves the first nonzero residual coefficient. -/
theorem coeff_middle_eq_of_lt_eq_zero (U T V : PowerSeries A)
    (hU : coeff 0 U = 1) (hV : coeff 0 V = 1) (n : ℕ)
    (hD : ∀ k < n, coeff k (U * T * V) = 0) :
    coeff n T = coeff n (U * T * V) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      have ht (k : ℕ) (hk : k < n) : coeff k T = 0 :=
        (ih k hk (fun j hj ↦ hD j (hj.trans hk))).trans (hD k hk)
      rw [coeff_mul_eq_left_of_lt_eq_zero _ _ _ hV (fun k hk ↦ by
        rw [coeff_mul_eq_right_of_lt_eq_zero U T k hU (fun j hj ↦ ht j (hj.trans hk)),
          ht k hk]), coeff_mul_eq_right_of_lt_eq_zero U T n hU ht]

end FQFP

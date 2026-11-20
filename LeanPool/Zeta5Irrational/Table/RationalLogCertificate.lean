/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

/-!
# Exact arithmetic for rational logarithm certificates

Horner's rule evaluates the odd reciprocal series and its optional geometric tail as
an unreduced fraction using integer arithmetic. The scoped instances decide the
original series inequalities by cross-multiplication, so the table proofs can keep
their existing kernel-checked certificates.
-/

open Finset

namespace Zeta5Irrational.LogarithmCertificates

/-- Horner evaluation of the odd reciprocal coefficients at `numerator / denominator`.
The returned fraction is left unreduced to avoid repeated GCD computations. The
geometric tail, when requested, is the final Horner coefficient. -/
@[expose] public def horner (numerator denominator : ℕ) (tail : Bool) (start : ℕ) :
    ℕ → ℕ × ℕ
  | 0 => if tail then (denominator, (2 * start + 1) * (denominator - numerator)) else (0, 1)
  | terms + 1 =>
    let next := horner numerator denominator tail (start + 1) terms
    (denominator * next.2 + (2 * start + 1) * numerator * next.1,
      (2 * start + 1) * denominator * next.2)

private lemma horner_denominator_pos {numerator denominator : ℕ}
    (h : numerator < denominator) (tail : Bool) (start terms : ℕ) :
    0 < (horner numerator denominator tail start terms).2 := by
  induction terms generalizing start with
  | zero =>
    cases tail
    · exact Nat.zero_lt_one
    · exact Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt h)
  | succ terms ih =>
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.succ_pos _) (Nat.zero_lt_of_lt h)) (ih (start + 1))

private def polynomial (z : ℚ) (tail : Bool) (start terms : ℕ) : ℚ :=
  (∑ i ∈ range terms, z ^ i / (2 * ((start + i : ℕ) : ℚ) + 1)) +
    if tail then z ^ terms / ((2 * ((start + terms : ℕ) : ℚ) + 1) * (1 - z)) else 0

private lemma polynomial_succ (z : ℚ) (tail : Bool) (start terms : ℕ) :
    polynomial z tail start (terms + 1) =
      1 / (2 * (start : ℚ) + 1) + z * polynomial z tail (start + 1) terms := by
  have addIndex (i : ℕ) : start + (i + 1) = start + 1 + i := by omega
  have sumShift :
      (∑ i ∈ range terms, z ^ (i + 1) / (2 * ((start + (i + 1) : ℕ) : ℚ) + 1)) =
        z * ∑ i ∈ range terms, z ^ i / (2 * ((start + 1 + i : ℕ) : ℚ) + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_succ', mul_div_assoc, addIndex i]
  unfold polynomial
  rw [sum_range_succ', sumShift, pow_zero, Nat.add_zero, mul_add]
  cases tail
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, mul_zero]
    exact add_comm _ _
  · simp only [↓reduceIte, pow_succ', mul_div_assoc, addIndex terms]
    ac_rfl

private lemma horner_eq {numerator denominator : ℕ} (h : numerator < denominator)
    (tail : Bool) (start terms : ℕ) :
    ((horner numerator denominator tail start terms).1 : ℚ) /
        (horner numerator denominator tail start terms).2 =
      polynomial ((numerator : ℚ) / denominator) tail start terms := by
  have denominatorPos : (0 : ℚ) < denominator := by exact_mod_cast Nat.zero_lt_of_lt h
  have numeratorLt : (numerator : ℚ) < denominator := by exact_mod_cast h
  have oddPos (k : ℕ) : (0 : ℚ) < 2 * (k : ℚ) + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by decide) (Nat.cast_nonneg _)) zero_lt_one
  induction terms generalizing start with
  | zero =>
    cases tail
    · simp [horner, polynomial]
    · simp only [horner, polynomial, sum_range_zero, pow_zero,
        ↓reduceIte, zero_add, Nat.add_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, Nat.cast_sub h.le]
      have hsub : (0 : ℚ) < (denominator : ℚ) - numerator := sub_pos.mpr numeratorLt
      field_simp [denominatorPos.ne', hsub.ne', (oddPos start).ne']
  | succ terms ih =>
    rw [polynomial_succ, ← ih (start + 1)]
    simp only [horner, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    have nextPos : (0 : ℚ) < (horner numerator denominator tail (start + 1) terms).2 :=
      Nat.cast_pos.mpr (horner_denominator_pos h tail (start + 1) terms)
    field_simp [denominatorPos.ne', nextPos.ne', (oddPos start).ne']

private lemma polynomial_as_sum (z : ℚ) (tail : Bool) (terms : ℕ) :
    2 * z * polynomial (z ^ 2) tail 0 terms =
      2 * ∑ k ∈ range terms, (1 / (2 * (k : ℚ) + 1)) * z ^ (2 * k + 1) +
        if tail then 2 * z ^ (2 * terms + 1) / ((2 * (terms : ℚ) + 1) * (1 - z ^ 2))
        else 0 := by
  have term (k : ℕ) :
      z * ((z ^ 2) ^ k / (2 * (k : ℚ) + 1)) =
        (1 / (2 * (k : ℚ) + 1)) * z ^ (2 * k + 1) := by
    rw [pow_add, pow_mul, pow_one]
    ring
  unfold polynomial
  rw [mul_assoc, mul_add, mul_sum, mul_add]
  simp only [Nat.zero_add, term]
  congr 1
  cases tail
  · simp
  · simp only [↓reduceIte, pow_add, pow_mul, pow_one]
    ring

private lemma fraction_le_rat (numerator denominator : ℕ) (h : 0 < denominator) (limit : ℚ) :
    (numerator : ℚ) / denominator ≤ limit ↔
      (numerator : ℤ) * limit.den ≤ limit.num * denominator := by
  have denominatorPos : (0 : ℚ) < denominator := Nat.cast_pos.mpr h
  have limitDenPos : (0 : ℚ) < limit.den := Nat.cast_pos.mpr limit.pos
  conv_lhs => rhs; rw [← limit.num_div_den]
  rw [div_le_div_iff₀ denominatorPos limitDenPos]
  exact_mod_cast Iff.rfl

private lemma rat_le_fraction (numerator denominator : ℕ) (h : 0 < denominator) (limit : ℚ) :
    limit ≤ (numerator : ℚ) / denominator ↔
      limit.num * (denominator : ℤ) ≤ (numerator : ℤ) * limit.den := by
  have denominatorPos : (0 : ℚ) < denominator := Nat.cast_pos.mpr h
  have limitDenPos : (0 : ℚ) < limit.den := Nat.cast_pos.mpr limit.pos
  conv_lhs => lhs; rw [← limit.num_div_den]
  rw [div_le_div_iff₀ limitDenPos denominatorPos]
  exact_mod_cast Iff.rfl

/-- The exact truncated logarithm series as a fraction. The input is at least one. -/
@[expose] public def seriesFraction (r : ℚ) (tail : Bool) (terms : ℕ) : ℕ × ℕ :=
  let numerator := r.num.toNat - r.den
  let denominator := r.num.toNat + r.den
  let series := horner (numerator ^ 2) (denominator ^ 2) tail 0 terms
  (2 * numerator * series.1, denominator * series.2)

private lemma seriesFraction_correct {r : ℚ} (hr : 1 ≤ r) (tail : Bool) (terms : ℕ) :
    0 < (seriesFraction r tail terms).2 ∧
      ((seriesFraction r tail terms).1 : ℚ) / (seriesFraction r tail terms).2 =
        2 * ((r - 1) / (r + 1)) * polynomial (((r - 1) / (r + 1)) ^ 2) tail 0 terms := by
  let numerator := r.num.toNat - r.den
  let denominator := r.num.toNat + r.den
  let z := (r - 1) / (r + 1)
  have castNumerator : ((r.num.toNat : ℕ) : ℤ) = r.num :=
    Int.toNat_of_nonneg (Rat.num_nonneg.mpr (zero_le_one.trans hr))
  have inputRepresentation : ((r.num.toNat : ℕ) : ℚ) / r.den = r := by
    rw [← Int.cast_natCast, castNumerator, Rat.num_div_den]
  have inputDenominatorPos : (0 : ℚ) < r.den := Nat.cast_pos.mpr r.pos
  have denominatorLeNumerator : r.den ≤ r.num.toNat := by
    rw [← inputRepresentation, le_div_iff₀ inputDenominatorPos, one_mul] at hr
    exact_mod_cast hr
  have numeratorLt : numerator < denominator :=
    (Nat.sub_le _ _).trans_lt (Nat.lt_add_of_pos_right r.pos)
  have zRepresentation : (numerator : ℚ) / denominator = z := by
    simp only [numerator, denominator, z, Nat.cast_sub denominatorLeNumerator, Nat.cast_add]
    conv_rhs => rw [← inputRepresentation]
    have sumPos : 0 < (r.num.toNat : ℚ) + r.den :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) inputDenominatorPos
    field_simp [inputDenominatorPos.ne', sumPos.ne']
  have squared : numerator ^ 2 < denominator ^ 2 := Nat.pow_lt_pow_left numeratorLt (by decide)
  constructor
  · exact Nat.mul_pos (Nat.zero_lt_of_lt numeratorLt)
      (horner_denominator_pos squared tail 0 terms)
  · let series := horner (numerator ^ 2) (denominator ^ 2) tail 0 terms
    change ((2 * numerator * series.1 : ℕ) : ℚ) / ((denominator * series.2 : ℕ) : ℚ) =
      2 * z * polynomial (z ^ 2) tail 0 terms
    have squareRepresentation : ((numerator ^ 2 : ℕ) : ℚ) / (denominator ^ 2 : ℕ) = z ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_pow, ← div_pow, zRepresentation]
    calc
      _ = 2 * ((numerator : ℚ) / denominator) * ((series.1 : ℚ) / series.2) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        rw [← div_mul_div_comm, mul_div_assoc]
      _ = _ := by
        dsimp only [series]
        rw [horner_eq squared tail 0 terms, zRepresentation, squareRepresentation]

/-- Cross-multiplication checks the upper logarithm series with its geometric tail. -/
public lemma upper_comparison (r bound : ℚ) (terms : ℕ) (hr : 1 ≤ r) :
    let fraction := seriesFraction r true terms
    ((fraction.1 : ℤ) * bound.den ≤ bound.num * fraction.2) ↔
      (1 ≤ r ∧
        2 * ∑ k ∈ range terms, (1 / (2 * (k : ℚ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1) +
          2 * ((r - 1) / (r + 1)) ^ (2 * terms + 1) /
            ((2 * (terms : ℚ) + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) ≤ bound) := by
  dsimp only
  let fraction := seriesFraction r true terms
  have h := seriesFraction_correct hr true terms
  have comparison := fraction_le_rat fraction.1 fraction.2 h.1 bound
  have equality := h.2.trans (polynomial_as_sum _ true _)
  rw [← comparison, equality, and_iff_right hr]
  rfl

/-- Cross-multiplication checks the lower logarithm series. -/
public lemma lower_comparison (r bound : ℚ) (terms : ℕ) (hr : 1 ≤ r) :
    let fraction := seriesFraction r false terms
    (bound.num * (fraction.2 : ℤ) ≤ (fraction.1 : ℤ) * bound.den) ↔
      (1 ≤ r ∧ bound ≤
        2 * ∑ k ∈ range terms, (1 / (2 * (k : ℚ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1)) := by
  dsimp only
  let fraction := seriesFraction r false terms
  have h := seriesFraction_correct hr false terms
  have comparison := rat_le_fraction fraction.1 fraction.2 h.1 bound
  have equality := h.2.trans ((polynomial_as_sum _ false _).trans (add_zero _))
  rw [← comparison, equality, and_iff_right hr]

/-- Decide closed upper logarithm certificates using their unreduced fraction. -/
public scoped instance (priority := 1100) upperDecidable (r bound : ℚ) (terms : ℕ) :
    Decidable (1 ≤ r ∧
      2 * ∑ k ∈ range terms, (1 / (2 * (k : ℚ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1) +
        2 * ((r - 1) / (r + 1)) ^ (2 * terms + 1) /
          ((2 * (terms : ℚ) + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) ≤ bound) :=
  if hr : 1 ≤ r then decidable_of_iff _ (upper_comparison r bound terms hr)
  else isFalse fun valid => hr valid.1

/-- Decide closed lower logarithm certificates using their unreduced fraction. -/
public scoped instance (priority := 1100) lowerDecidable (r bound : ℚ) (terms : ℕ) :
    Decidable (1 ≤ r ∧ bound ≤
      2 * ∑ k ∈ range terms, (1 / (2 * (k : ℚ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1)) :=
  if hr : 1 ≤ r then decidable_of_iff _ (lower_comparison r bound terms hr)
  else isFalse fun valid => hr valid.1

end Zeta5Irrational.LogarithmCertificates

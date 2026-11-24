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
# Exact arithmetic for rational arctangent certificates

The alternating series is a polynomial in the negative square of the argument, times
the argument itself. Horner evaluation keeps an unreduced integer numerator and
denominator, so checking a closed bound does not require normalizing every term.
-/

open Finset

namespace Zeta5Irrational.ArctangentCertificates

/-- Evaluate the alternating polynomial as an unreduced fraction. -/
@[expose] public def horner (numerator denominator : ℤ) (start : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | terms + 1 =>
    let next := horner numerator denominator (start + 1) terms
    let odd : ℤ := (2 * (start : ℤ) + 1)
    (denominator * next.2 - odd * numerator * next.1, odd * denominator * next.2)

private lemma horner_denominator_pos {numerator denominator : ℤ} (h : 0 < denominator)
    (start terms : ℕ) : 0 < (horner numerator denominator start terms).2 := by
  induction terms generalizing start with
  | zero => exact Int.zero_lt_one
  | succ terms ih =>
    have oddPos : 0 < 2 * (start : ℤ) + 1 :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by decide) (Int.natCast_nonneg _)) zero_lt_one
    exact mul_pos (mul_pos oddPos h) (ih (start + 1))

private def polynomial (z : ℚ) (start terms : ℕ) : ℚ :=
  ∑ i ∈ range terms, (-z) ^ i / (2 * ((start + i : ℕ) : ℚ) + 1)

private lemma polynomial_succ (z : ℚ) (start terms : ℕ) :
    polynomial z start (terms + 1) =
      1 / (2 * (start : ℚ) + 1) - z * polynomial z (start + 1) terms := by
  have sumShift :
      (∑ i ∈ range terms, (-z) ^ (i + 1) / (2 * ((start + (i + 1) : ℕ) : ℚ) + 1)) =
        -z * polynomial z (start + 1) terms := by
    rw [polynomial, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_succ', mul_div_assoc, Nat.add_right_comm, ← Nat.add_assoc]
  rw [polynomial, sum_range_succ', pow_zero, Nat.add_zero, sumShift, neg_mul, sub_eq_add_neg,
    add_comm]

private lemma horner_eq {numerator denominator : ℤ} (h : 0 < denominator) (start terms : ℕ) :
    ((horner numerator denominator start terms).1 : ℚ) /
        (horner numerator denominator start terms).2 =
      polynomial ((numerator : ℚ) / denominator) start terms := by
  have denominatorPos : (0 : ℚ) < denominator := Int.cast_pos.mpr h
  have oddPos (k : ℕ) : (0 : ℚ) < 2 * (k : ℚ) + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by decide) (Nat.cast_nonneg _)) zero_lt_one
  induction terms generalizing start with
  | zero => simp [horner, polynomial]
  | succ terms ih =>
    rw [polynomial_succ, ← ih (start + 1)]
    simp only [horner, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      Int.cast_natCast]
    have nextPos : (0 : ℚ) < (horner numerator denominator (start + 1) terms).2 :=
      Int.cast_pos.mpr (horner_denominator_pos h (start + 1) terms)
    field_simp [denominatorPos.ne', nextPos.ne', (oddPos start).ne']

private lemma polynomial_as_sum (z : ℚ) (terms : ℕ) :
    z * polynomial (z ^ 2) 0 terms =
      ∑ i ∈ range terms, (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1)) := by
  rw [polynomial, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [Nat.zero_add, ← neg_one_mul (z ^ 2), mul_pow, pow_add, pow_mul, pow_one]
  ring

/-- Evaluate a finite arctangent series as an unreduced fraction. -/
@[expose] public def seriesFraction (z : ℚ) (terms : ℕ) : ℤ × ℤ :=
  let fraction := horner (z.num ^ 2) ((z.den : ℤ) ^ 2) 0 terms
  (z.num * fraction.1, z.den * fraction.2)

private lemma seriesFraction_correct (z : ℚ) (terms : ℕ) :
    0 < (seriesFraction z terms).2 ∧
      ((seriesFraction z terms).1 : ℚ) / (seriesFraction z terms).2 =
        ∑ i ∈ range terms, (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1)) := by
  have denominatorPos : (0 : ℤ) < z.den := Int.natCast_pos.mpr z.pos
  have squarePos : (0 : ℤ) < (z.den : ℤ) ^ 2 := pow_pos denominatorPos _
  refine ⟨mul_pos denominatorPos (horner_denominator_pos squarePos 0 terms), ?_⟩
  have squareRepresentation : ((z.num ^ 2 : ℤ) : ℚ) / (((z.den : ℤ) ^ 2 : ℤ) : ℚ) = z ^ 2 := by
    rw [Int.cast_pow, Int.cast_pow, ← div_pow, Int.cast_natCast, Rat.num_div_den]
  dsimp only [seriesFraction]
  rw [Int.cast_mul, Int.cast_mul, ← div_mul_div_comm, Int.cast_natCast, Rat.num_div_den,
    horner_eq squarePos, squareRepresentation, polynomial_as_sum]

/-- Cross-multiplication is equivalent to the rational upper comparison. -/
public lemma upper_comparison (z bound : ℚ) (terms : ℕ) :
    let fraction := seriesFraction z terms
    (fraction.1 * bound.den ≤ bound.num * fraction.2) ↔
      (∑ i ∈ range terms, (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1))) ≤ bound := by
  dsimp only
  have denominatorPos : (0 : ℚ) < (seriesFraction z terms).2 :=
    Int.cast_pos.mpr (seriesFraction_correct z terms).1
  have boundPos : (0 : ℚ) < bound.den := Nat.cast_pos.mpr bound.pos
  rw [← (seriesFraction_correct z terms).2]
  conv_rhs => rhs; rw [← bound.num_div_den]
  rw [div_le_div_iff₀ denominatorPos boundPos]
  exact_mod_cast Iff.rfl

/-- Cross-multiplication is equivalent to the rational lower comparison. -/
public lemma lower_comparison (z bound : ℚ) (terms : ℕ) :
    let fraction := seriesFraction z terms
    (bound.num * fraction.2 ≤ fraction.1 * bound.den) ↔
      bound ≤ ∑ i ∈ range terms, (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1)) := by
  dsimp only
  have denominatorPos : (0 : ℚ) < (seriesFraction z terms).2 :=
    Int.cast_pos.mpr (seriesFraction_correct z terms).1
  have boundPos : (0 : ℚ) < bound.den := Nat.cast_pos.mpr bound.pos
  rw [← (seriesFraction_correct z terms).2]
  conv_rhs => lhs; rw [← bound.num_div_den]
  rw [div_le_div_iff₀ boundPos denominatorPos]
  exact_mod_cast Iff.rfl

/-- Check an upper bound against the odd partial sum of the alternating series. -/
public scoped instance (priority := 1100) upperDecidable (z bound : ℚ) (terms : ℕ) :
    Decidable (0 ≤ z ∧ z < 1 ∧ ∑ i ∈ range (2 * terms + 1),
      (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1)) ≤ bound) := by
  exact if hz : 0 ≤ z ∧ z < 1 then
    decidable_of_iff _ ((upper_comparison z bound _).trans
      ⟨fun valid => ⟨hz.1, hz.2, valid⟩, fun valid => valid.2.2⟩)
  else isFalse fun valid => hz ⟨valid.1, valid.2.1⟩

/-- Check a lower bound against the even partial sum of the alternating series. -/
public scoped instance (priority := 1100) lowerDecidable (z bound : ℚ) (terms : ℕ) :
    Decidable (0 ≤ z ∧ z < 1 ∧ bound ≤ ∑ i ∈ range (2 * terms),
      (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1))) := by
  exact if hz : 0 ≤ z ∧ z < 1 then
    decidable_of_iff _ ((lower_comparison z bound _).trans
      ⟨fun valid => ⟨hz.1, hz.2, valid⟩, fun valid => valid.2.2⟩)
  else isFalse fun valid => hz ⟨valid.1, valid.2.1⟩

end Zeta5Irrational.ArctangentCertificates

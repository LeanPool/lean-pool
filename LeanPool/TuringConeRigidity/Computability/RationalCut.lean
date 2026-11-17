/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/RationalCut.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import LeanPool.TuringConeRigidity.Computability.RationalCoding
public import LeanPool.TuringConeRigidity.Effective.UniformOracle

/-!
# Rational Cut
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
namespace RationalCoding

/-- The positive part of the canonical numerator. -/
def positiveNumerator (n : ℕ) : ℕ := if negative n then 0 else numeratorMagnitude n
/-- The absolute value of the negative part of the canonical numerator. -/
def negativeNumerator (n : ℕ) : ℕ := if negative n then numeratorMagnitude n else 0

theorem positiveNumerator_primrec : Primrec positiveNumerator :=
  Primrec.ite (Primrec.eq.comp negative_primrec (Primrec.const true)) (Primrec.const 0)
    numeratorMagnitude_primrec

theorem negativeNumerator_primrec : Primrec negativeNumerator :=
  Primrec.ite (Primrec.eq.comp negative_primrec (Primrec.const true)) numeratorMagnitude_primrec
    (Primrec.const 0)

theorem signed_query_value (n : ℕ) : (rationalEnumeration n : ℝ) =
    ((positiveNumerator n : ℝ)-(negativeNumerator n : ℝ))/(denominator n : ℝ) := by
  rw [query_value]
  cases hn : negative n <;> simp [positiveNumerator,negativeNumerator,hn]

/-- Strict comparison of two rational codes using natural-number cross-products. -/
def ltCode (i j : ℕ) : Prop :=
  positiveNumerator i*denominator j + negativeNumerator j*denominator i <
    positiveNumerator j*denominator i + negativeNumerator i*denominator j

instance (i j : ℕ) : Decidable (ltCode i j) := inferInstanceAs (Decidable (_ < _))

theorem ltCode_primrec : PrimrecRel ltCode :=
  Primrec.nat_lt.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (positiveNumerator_primrec.comp Primrec.fst)
        (denominator_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (negativeNumerator_primrec.comp Primrec.snd)
        (denominator_primrec.comp Primrec.fst)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (positiveNumerator_primrec.comp Primrec.snd)
        (denominator_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (negativeNumerator_primrec.comp Primrec.fst)
        (denominator_primrec.comp Primrec.snd)))

theorem ltCode_iff (i j : ℕ) :
    ltCode i j ↔ (rationalEnumeration i : ℝ) < (rationalEnumeration j : ℝ) := by
  have hi : (0 : ℝ) < denominator i := by exact_mod_cast denominator_pos i
  have hj : (0 : ℝ) < denominator j := by exact_mod_cast denominator_pos j
  rw [signed_query_value,signed_query_value,div_lt_div_iff₀ hi hj]
  constructor
  · intro h
    have hh : (positiveNumerator i : ℝ)*denominator j + negativeNumerator j*denominator i <
        (positiveNumerator j : ℝ)*denominator i + negativeNumerator i*denominator j := by
      exact_mod_cast h
    nlinarith
  · intro h
    change positiveNumerator i*denominator j + negativeNumerator j*denominator i <
      positiveNumerator j*denominator i + negativeNumerator i*denominator j
    have hh : (positiveNumerator i : ℝ)*denominator j + negativeNumerator j*denominator i <
        (positiveNumerator j : ℝ)*denominator i + negativeNumerator i*denominator j := by nlinarith
    exact_mod_cast hh
end RationalCoding

theorem rational_cut_computable (q : ℚ) :
    Primrec (fun n => if cut (q : ℝ) n then (1 : ℕ) else 0) := by
  have hp := Primrec.ite
    (RationalCoding.ltCode_primrec.comp Primrec.id (Primrec.const (Encodable.encode q)))
    (Primrec.const 1) (Primrec.const 0)
  apply hp.of_eq
  intro n
  have hq : rationalEnumeration (Encodable.encode q) = q := by simp [rationalEnumeration]
  have he : RationalCoding.ltCode n (Encodable.encode q) ↔ (rationalEnumeration n : ℝ) < q := by
    rw [RationalCoding.ltCode_iff,hq]
  by_cases h : (rationalEnumeration n : ℝ) < q
  · simp [he,h,cut]
  · simp [he,h,cut]

theorem rational_cut_reduces (q : ℚ) (A : Oracle) : Reduces (cut (q : ℝ)) A := by
  exact RecursiveIn.iff_nat.mpr (UniformOracle.total_primrec (rational_cut_computable q))

end TuringRigidity

end OAI

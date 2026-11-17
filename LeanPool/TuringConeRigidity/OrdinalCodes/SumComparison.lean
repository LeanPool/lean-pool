/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/SumComparison.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.RationalCut

/-!
# Sum Comparison
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RationalCoding

def sumLeft (z : ℕ × ℕ × ℕ) : ℕ :=
  positiveNumerator z.1 * denominator z.2.1 * denominator z.2.2 +
    negativeNumerator z.2.1 * denominator z.1 * denominator z.2.2 +
    negativeNumerator z.2.2 * denominator z.1 * denominator z.2.1

def sumRight (z : ℕ × ℕ × ℕ) : ℕ :=
  negativeNumerator z.1 * denominator z.2.1 * denominator z.2.2 +
    positiveNumerator z.2.1 * denominator z.1 * denominator z.2.2 +
    positiveNumerator z.2.2 * denominator z.1 * denominator z.2.1

private theorem polynomial_primrec {p a b : ℕ → ℕ} (hp : Primrec p)
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun z : ℕ × ℕ × ℕ =>
      p z.1*denominator z.2.1*denominator z.2.2 +
      a z.2.1*denominator z.1*denominator z.2.2 +
      b z.2.2*denominator z.1*denominator z.2.1) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (hp.comp Primrec.fst)
      (denominator_primrec.comp (Primrec.fst.comp Primrec.snd)))
      (denominator_primrec.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (ha.comp (Primrec.fst.comp Primrec.snd))
      (denominator_primrec.comp Primrec.fst))
      (denominator_primrec.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (hb.comp (Primrec.snd.comp Primrec.snd))
      (denominator_primrec.comp Primrec.fst))
      (denominator_primrec.comp (Primrec.fst.comp Primrec.snd)))

theorem sumLeft_primrec : Primrec sumLeft :=
  polynomial_primrec positiveNumerator_primrec negativeNumerator_primrec negativeNumerator_primrec

theorem sumRight_primrec : Primrec sumRight :=
  polynomial_primrec negativeNumerator_primrec positiveNumerator_primrec positiveNumerator_primrec

theorem sum_difference (i j k : ℕ) :
    ((rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i : ℝ))*
      ((denominator i : ℝ)*denominator j*denominator k) =
        (sumRight (i,j,k) : ℝ)-(sumLeft (i,j,k) : ℝ) := by
  have hi : (denominator i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos i))
  have hj : (denominator j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos j))
  have hk : (denominator k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos k))
  rw [signed_query_value,signed_query_value,signed_query_value]
  simp only [sumLeft,sumRight,Nat.cast_add,Nat.cast_mul]
  field_simp
  ring

theorem lt_sum_iff (i j k : ℕ) :
    sumLeft (i,j,k) < sumRight (i,j,k) ↔
      (rationalEnumeration i : ℝ) < (rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ) := by
  have hd : (0 : ℝ) < (denominator i : ℝ)*denominator j*denominator k := by
    exact mul_pos (mul_pos (by exact_mod_cast denominator_pos i)
      (by exact_mod_cast denominator_pos j)) (by exact_mod_cast denominator_pos k)
  constructor
  · intro h
    have hh : (sumLeft (i,j,k) : ℝ) < (sumRight (i,j,k) : ℝ) := by exact_mod_cast h
    have hp : 0 < ((rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i
      : ℝ))*
        ((denominator i : ℝ)*denominator j*denominator k) := by
      rw [sum_difference]; exact sub_pos.mpr hh
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp hp)
  · intro h
    have hh := mul_pos (sub_pos.mpr h) hd
    rw [sum_difference] at hh
    exact_mod_cast sub_pos.mp hh

theorem sum_lt_iff (i j k : ℕ) :
    sumRight (i,j,k) < sumLeft (i,j,k) ↔
      (rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ) < (rationalEnumeration i : ℝ) := by
  have hd : (0 : ℝ) < (denominator i : ℝ)*denominator j*denominator k := by
    exact mul_pos (mul_pos (by exact_mod_cast denominator_pos i)
      (by exact_mod_cast denominator_pos j)) (by exact_mod_cast denominator_pos k)
  constructor
  · intro h
    have hh : (sumRight (i,j,k) : ℝ) < (sumLeft (i,j,k) : ℝ) := by exact_mod_cast h
    have hp : ((rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i : ℝ))*
        ((denominator i : ℝ)*denominator j*denominator k) < 0 := by
      rw [sum_difference]; exact sub_neg.mpr hh
    have hh' : (rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i :
      ℝ)<0 := by
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hn) hd.le)) hp
    exact sub_neg.mp hh'
  · intro h
    have hh := mul_neg_of_neg_of_pos (sub_neg.mpr h) hd
    rw [sum_difference] at hh
    exact_mod_cast sub_neg.mp hh

end TuringRigidity.RationalCoding

end OAI

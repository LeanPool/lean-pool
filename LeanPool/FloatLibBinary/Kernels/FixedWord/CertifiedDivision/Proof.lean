/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.CertifiedDivision.Runtime
import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Proof
import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Restoring128Proof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Compiler

/-!
# Verified fixed-word division candidates

The radix-`2^32` runtime loop is a candidate generator. Its quotient and remainder are
accepted when native multiplication and addition independently certify the exact Euclidean
division equation and remainder bound. If that check rejects the candidate, the runtime selects a
restoring accumulator; this module proves that accumulator equal to the logical recurrence and
certifies its result on normalized inputs of `precision + 1` bits with `64 < precision ≤ 126`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.CertifiedDivision

private theorem widenLow_toNat (value : FloatLib.Numerics.FixedWord.UInt128) :
    (widenLow value).toNat = value.toNat := by
  unfold widenLow FloatLib.Numerics.FixedWord.UInt256.toNat
    FloatLib.Numerics.FixedWord.UInt128.toNat
  simp

/-- Both candidate shifts of an in-range precision lie strictly between one and two words. -/
theorem CandidateShift.toNat_bounds (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126) (shift : CandidateShift) :
    64 < shift.toNat precision ∧ shift.toNat precision < 128 := by
  cases shift <;> simp [CandidateShift.toNat] <;> omega

private theorem widenShift_toNat (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126)
    (value : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift) :
    (FloatLib.Numerics.FixedWord.UInt256.ofUInt128ShiftedLeft value
        (shift.toNat precision)).toNat =
      value.toNat * 2 ^ shift.toNat precision := by
  have hbounds := CandidateShift.toNat_bounds precision hprecision shift
  rw [FloatLib.Numerics.FixedWord.UInt256.toNat_ofUInt128ShiftedLeft value _
    hbounds.1 hbounds.2, Nat.shiftLeft_eq]

/--
The executable certificate accepts every representable Euclidean decomposition for the two shifts
used by two-limb division.

This is completeness of the independent checker, not of the speculative Algorithm D generator.
-/
theorem certificate_complete (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128)
    (hdecomposition :
      quotient.toNat * den.toNat + remainder.toNat =
        num.toNat * 2 ^ shift.toNat precision)
    (hremainder : remainder.toNat < den.toNat) :
    certificate precision num den shift quotient remainder = true := by
  let product := FloatLib.Numerics.FixedWord.mul128 quotient den
  let lowRemainder := widenLow remainder
  let sum := FloatLib.Numerics.FixedWord.add256 product lowRemainder
  let target :=
    FloatLib.Numerics.FixedWord.UInt256.ofUInt128ShiftedLeft num (shift.toNat precision)
  have hbounds := CandidateShift.toNat_bounds precision hprecision shift
  have hproduct :
      product.toNat = quotient.toNat * den.toNat := by
    simpa only [product] using
      FloatLib.Numerics.FixedWord.mul128_toNat quotient den
  have htarget :
      target.toNat = num.toNat * 2 ^ shift.toNat precision := by
    simpa only [target] using
      widenShift_toNat precision hprecision num shift
  have htargetFit : target.toNat < 2 ^ 256 := by
    rw [htarget]
    calc
      num.toNat * 2 ^ shift.toNat precision < 2 ^ 128 * 2 ^ shift.toNat precision :=
        Nat.mul_lt_mul_of_pos_right
          (FloatLib.Numerics.FixedWord.UInt128.toNat_lt num) (by positivity)
      _ = 2 ^ (128 + shift.toNat precision) := by rw [pow_add]
      _ ≤ 2 ^ 256 := by
        apply Nat.pow_le_pow_right (by decide)
        omega
  have hsumExact :
      sum.value.toNat + sum.carry.toNat * 2 ^ 256 =
        target.toNat := by
    have hadd :=
      FloatLib.Numerics.FixedWord.add256_toNat product lowRemainder
    change
      sum.value.toNat + sum.carry.toNat * 2 ^ 256 =
        product.toNat + lowRemainder.toNat at hadd
    rw [hproduct, show lowRemainder.toNat = remainder.toNat by
      simpa only [lowRemainder] using widenLow_toNat remainder,
      hdecomposition, ← htarget] at hadd
    exact hadd
  have hcarryNat : sum.carry.toNat = 0 := by
    omega
  have hcarry : sum.carry = 0 :=
    UInt64.toNat_inj.mp <| by simpa using hcarryNat
  have hsumValue : sum.value = target := by
    apply FloatLib.Numerics.FixedWord.UInt256.toNat_injective
    omega
  simp only [certificate, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hcarry, hsumValue⟩,
    (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff remainder den).2
      hremainder⟩

/--
A successful native certificate proves the exact quotient/remainder decomposition and Euclidean
remainder bound. The proof does not depend on the radix-`2^32` candidate generator.
-/
theorem certificate_sound (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128)
    (hvalid :
      certificate precision num den shift quotient remainder = true) :
    quotient.toNat * den.toNat + remainder.toNat =
        num.toNat * 2 ^ shift.toNat precision ∧
      remainder.toNat < den.toNat := by
  let product := FloatLib.Numerics.FixedWord.mul128 quotient den
  let sum := FloatLib.Numerics.FixedWord.add256 product (widenLow remainder)
  simp only [certificate, Bool.and_eq_true, beq_iff_eq] at hvalid
  rcases hvalid with ⟨⟨hsumCarry, hsumValue⟩, hremainder⟩
  have hproduct :
      product.toNat = quotient.toNat * den.toNat := by
    simpa only [product] using FloatLib.Numerics.FixedWord.mul128_toNat quotient den
  have hsum :
      sum.value.toNat =
        product.toNat + (widenLow remainder).toNat := by
    simpa only [sum] using
      FloatLib.Numerics.FixedWord.add256_value_toNat_of_carry_zero
        product (widenLow remainder) hsumCarry
  have hsumValueNat :
      sum.value.toNat =
        (FloatLib.Numerics.FixedWord.UInt256.ofUInt128ShiftedLeft num
          (shift.toNat precision)).toNat :=
    congrArg FloatLib.Numerics.FixedWord.UInt256.toNat hsumValue
  constructor
  · rw [← widenShift_toNat precision hprecision num shift,
      ← hsumValueNat, hsum, hproduct, widenLow_toNat]
  · exact
      (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff remainder den).1 hremainder

/--
The allocation-light restoring repair agrees with the logical two-limb recurrence.

Runtime code calls the primitive-word accumulator directly. This theorem is the proof boundary
that lets the mathematical argument continue through `quotientSteps128`.
-/
theorem restoringCandidate_eq_quotientSteps128 (precision : Nat)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift) :
    restoringCandidate precision num den shift =
      FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128
        den (shift.toNat precision) (restoringInitial num den) := by
  unfold restoringCandidate
  exact
    FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128Impl_eq_quotientSteps128
      den (shift.toNat precision) (restoringInitial num den)

/--
The restoring repair produces a certified candidate for normalized `precision + 1`-bit
significands.

The shift is `precision` when the numerator is at least the denominator and `precision + 1`
otherwise. Those are exactly the two cases selected by the two-limb backends.
-/
theorem restoringCandidate_complete (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (hnum : 2 ^ precision ≤ num.toNat ∧ num.toNat < 2 ^ (precision + 1))
    (hden : 2 ^ precision ≤ den.toNat ∧ den.toNat < 2 ^ (precision + 1))
    (hshift :
      shift =
        if den.toNat ≤ num.toNat then
          CandidateShift.exact
        else
          CandidateShift.extra) :
    certificate precision num den shift
        (restoringCandidate precision num den shift).quotient
        (restoringCandidate precision num den shift).remainder =
      true := by
  have hdenFit : den.toNat < 2 ^ 127 :=
    hden.2.trans_le <| Nat.pow_le_pow_right (by decide) (by omega)
  have hpowSucc : 2 ^ (precision + 1) = 2 ^ precision * 2 := pow_succ 2 precision
  have hpowLe : 2 ^ (precision + 1) ≤ 2 ^ 128 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  by_cases hle : den.toNat ≤ num.toNat
  · have hless :
        FloatLib.Numerics.FixedWord.UInt128.less num den = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact (Nat.not_lt_of_ge hle)
        ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff num den).1
          htrue)
    have hshiftExact : shift = CandidateShift.exact := by
      simpa [hle] using hshift
    subst shift
    let initial :
        FloatLib.Numerics.FixedWord.RestoringQuotient.QuotientState
          FloatLib.Numerics.FixedWord.UInt128 :=
      { quotient := ⟨0, 1⟩
        remainder := FloatLib.Numerics.FixedWord.UInt128.sub num den }
    have hremainderNat :
        initial.remainder.toNat = num.toNat - den.toNat := by
      simpa only [initial] using
        FloatLib.Numerics.FixedWord.UInt128.sub_toNat num den hle
    have hremainder : initial.remainder.toNat < den.toNat := by
      rw [hremainderNat]
      have hnumLtTwice : num.toNat < den.toNat * 2 := by
        calc
          num.toNat < 2 ^ (precision + 1) := hnum.2
          _ = 2 ^ precision * 2 := hpowSucc
          _ ≤ den.toNat * 2 := Nat.mul_le_mul_right 2 hden.1
      omega
    have hcapacity :
        (initial.quotient.toNat + 1) * 2 ^ precision ≤ 2 ^ 128 := by
      have hquotientNat : initial.quotient.toNat = 1 := by
        simp [initial, FloatLib.Numerics.FixedWord.UInt128.toNat]
      rw [hquotientNat, show (1 + 1) * 2 ^ precision = 2 ^ (precision + 1) by
        rw [hpowSucc]; ring]
      exact hpowLe
    let result :=
      FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128
        den precision initial
    have hspec :=
      FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128_spec
        den precision initial hdenFit hremainder hcapacity
    have hinitial :
        initial.quotient.toNat * den.toNat + initial.remainder.toNat =
          num.toNat := by
      have hquotientNat : initial.quotient.toNat = 1 := by
        simp [initial, FloatLib.Numerics.FixedWord.UInt128.toNat]
      rw [hquotientNat, hremainderNat]
      omega
    have hdecomposition :
        result.quotient.toNat * den.toNat + result.remainder.toNat =
          num.toNat * 2 ^ precision := by
      rw [hspec.1, hinitial]
    have hcertificate :=
      certificate_complete precision hprecision num den .exact
        result.quotient result.remainder hdecomposition hspec.2.1
    have hinitialState : restoringInitial num den = initial := by
      simp [restoringInitial, hless, initial]
    have hrepair :
        restoringCandidate precision num den .exact = result := by
      rw [restoringCandidate_eq_quotientSteps128, hinitialState]
      rfl
    rw [hshiftExact, hrepair]
    exact hcertificate
  · have hnumLt : num.toNat < den.toNat := Nat.lt_of_not_ge hle
    have hless :
        FloatLib.Numerics.FixedWord.UInt128.less num den = true :=
      (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff num den).2
        hnumLt
    have hshiftExtra : shift = CandidateShift.extra := by
      simpa [hle] using hshift
    subst shift
    let initial :
        FloatLib.Numerics.FixedWord.RestoringQuotient.QuotientState
          FloatLib.Numerics.FixedWord.UInt128 :=
      { quotient := ⟨0, 0⟩, remainder := num }
    have hremainder : initial.remainder.toNat < den.toNat := by
      simpa only [initial] using hnumLt
    have hcapacity :
        (initial.quotient.toNat + 1) * 2 ^ (precision + 1) ≤ 2 ^ 128 := by
      have hquotientNat : initial.quotient.toNat = 0 := by
        simp [initial, FloatLib.Numerics.FixedWord.UInt128.toNat]
      rw [hquotientNat, zero_add, one_mul]
      exact hpowLe
    let result :=
      FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128
        den (precision + 1) initial
    have hspec :=
      FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128_spec
        den (precision + 1) initial hdenFit hremainder hcapacity
    have hinitial :
        initial.quotient.toNat * den.toNat + initial.remainder.toNat =
          num.toNat := by
      simp [initial, FloatLib.Numerics.FixedWord.UInt128.toNat]
    have hdecomposition :
        result.quotient.toNat * den.toNat + result.remainder.toNat =
          num.toNat * 2 ^ (precision + 1) := by
      rw [hspec.1, hinitial]
    have hcertificate :=
      certificate_complete precision hprecision num den .extra
        result.quotient result.remainder hdecomposition hspec.2.1
    have hinitialState : restoringInitial num den = initial := by
      simp [restoringInitial, hless, initial]
    have hrepair :
        restoringCandidate precision num den .extra = result := by
      rw [restoringCandidate_eq_quotientSteps128, hinitialState]
      rfl
    rw [hshiftExtra, hrepair]
    exact hcertificate

/--
An independently rejected Algorithm D candidate selects the restoring repair.

The conclusion holds for any operands whose candidate fails the certificate.
-/
theorem checkedCandidate_eq_repair_of_certificate_false (precision : Nat)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (hrejected :
      certificate precision num den shift
          (candidate precision num den shift).1
          (candidate precision num den shift).2 =
        false) :
    checkedCandidate precision num den shift =
      { quotient := (restoringCandidate precision num den shift).quotient
        remainder := (restoringCandidate precision num den shift).remainder } := by
  simp [checkedCandidate, hrejected]

/--
The checked candidate is complete on the normalized two-limb division domain.

The fast candidate is used when its independent certificate succeeds; otherwise the proved
restoring loop supplies the quotient and remainder. Thus the selected pair itself is certified,
without a second runtime check or an unreachable backend fallback.
-/
theorem checkedCandidate_complete (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (hnum : 2 ^ precision ≤ num.toNat ∧ num.toNat < 2 ^ (precision + 1))
    (hden : 2 ^ precision ≤ den.toNat ∧ den.toNat < 2 ^ (precision + 1))
    (hshift :
      shift =
        if den.toNat ≤ num.toNat then
          CandidateShift.exact
        else
          CandidateShift.extra) :
    certificate precision num den shift
        (checkedCandidate precision num den shift).quotient
        (checkedCandidate precision num den shift).remainder =
      true := by
  by_cases hfast :
      certificate precision num den shift
          (candidate precision num den shift).1
          (candidate precision num den shift).2 =
        true
  · simp [checkedCandidate, hfast]
  · have hrejected :
        certificate precision num den shift
            (candidate precision num den shift).1
            (candidate precision num den shift).2 =
          false :=
      Bool.eq_false_iff.mpr hfast
    rw [checkedCandidate_eq_repair_of_certificate_false
      precision num den shift hrejected]
    exact restoringCandidate_complete precision hprecision num den shift hnum hden hshift

/--
The candidate selected by the fast-check-or-repair runtime path satisfies Euclidean division.

This is the consumer-facing form of `checkedCandidate_complete`: callers receive the exact
equation and strict remainder bound directly, without reopening the executable certificate.
-/
theorem checkedCandidate_sound (precision : Nat)
    (hprecision : 64 < precision ∧ precision ≤ 126)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (hnum : 2 ^ precision ≤ num.toNat ∧ num.toNat < 2 ^ (precision + 1))
    (hden : 2 ^ precision ≤ den.toNat ∧ den.toNat < 2 ^ (precision + 1))
    (hshift :
      shift =
        if den.toNat ≤ num.toNat then
          CandidateShift.exact
        else
          CandidateShift.extra) :
    (checkedCandidate precision num den shift).quotient.toNat * den.toNat +
          (checkedCandidate precision num den shift).remainder.toNat =
        num.toNat * 2 ^ shift.toNat precision ∧
      (checkedCandidate precision num den shift).remainder.toNat < den.toNat :=
  certificate_sound precision hprecision num den shift
    (checkedCandidate precision num den shift).quotient
    (checkedCandidate precision num den shift).remainder <|
    checkedCandidate_complete precision hprecision num den shift hnum hden hshift

private theorem lowBit_eq_parity (value : FloatLib.Numerics.FixedWord.UInt128) :
    ((value.lo &&& 1) == 0) ↔ value.toNat % 2 = 0 := by
  simp only [beq_iff_eq]
  have hmod :
      value.toNat % 2 = value.lo.toNat % 2 := by
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat
    norm_num [Nat.add_mod, Nat.mul_mod]
  rw [hmod]
  constructor
  · intro h
    have hnat := congrArg UInt64.toNat h
    rw [UInt64.toNat_and] at hnat
    simpa [Nat.and_one_is_mod] using hnat
  · intro h
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and]
    simpa [Nat.and_one_is_mod] using h

/--
Native quotient rounding agrees with exact nearest-even rational rounding for a certified
Euclidean decomposition.
-/
theorem roundQuotient_toNat
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128) (numerator : Nat)
    (hdenFit : den.toNat < 2 ^ 127)
    (hdecomposition :
      quotient.toNat * den.toNat + remainder.toNat = numerator)
    (hremainder : remainder.toNat < den.toNat)
    (hquotientFit : quotient.toNat + 1 < 2 ^ 128) :
    (roundQuotient den quotient remainder).toNat =
      Numerics.roundQuotientEven numerator den.toNat := by
  have hdenPositive : 0 < den.toNat := by omega
  have hdivision :
      numerator / den.toNat = quotient.toNat ∧
        numerator % den.toNat = remainder.toNat :=
    (Nat.div_mod_unique hdenPositive).2 <| by
      refine ⟨?_, hremainder⟩
      simpa only [Nat.add_comm, Nat.mul_comm] using hdecomposition
  have hquotient := hdivision.1
  have hremainderEq := hdivision.2
  let doubled := FloatLib.Numerics.FixedWord.add128 remainder remainder
  have hdoubleFit :
      remainder.toNat + remainder.toNat < 2 ^ 128 := by
    nlinarith
  have hdoubleCarry : doubled.carry = 0 := by
    simpa only [doubled] using
      FloatLib.Numerics.FixedWord.add128_carry_eq_zero_of_lt
        remainder remainder hdoubleFit
  have hdouble :
      doubled.value.toNat = 2 * remainder.toNat := by
    simpa only [doubled, two_mul] using
      FloatLib.Numerics.FixedWord.add128_value_toNat_of_lt
        remainder remainder hdoubleFit
  have hincrement :
      quotient.increment.toNat = quotient.toNat + 1 :=
    FloatLib.Numerics.FixedWord.UInt128.increment_toNat quotient hquotientFit
  have heven := lowBit_eq_parity quotient
  by_cases hbelow : 2 * remainder.toNat < den.toNat
  · have hnativeAbove :
        FloatLib.Numerics.FixedWord.UInt128.less den doubled.value = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hlt :=
        (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff den doubled.value).1 htrue
      rw [hdouble] at hlt
      omega
    have hnativeEqual : doubled.value ≠ den := by
      intro heq
      have hnat := congrArg FloatLib.Numerics.FixedWord.UInt128.toNat heq
      rw [hdouble] at hnat
      omega
    unfold roundQuotient Numerics.roundQuotientEven
    simp [doubled, hdoubleCarry, hnativeAbove, hnativeEqual,
      hbelow, hquotient, hremainderEq]
  · by_cases habove : den.toNat < 2 * remainder.toNat
    · have hnativeAbove :
          FloatLib.Numerics.FixedWord.UInt128.less den doubled.value = true := by
        apply (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff den doubled.value).2
        rw [hdouble]
        exact habove
      unfold roundQuotient Numerics.roundQuotientEven
      simp [doubled, hdoubleCarry, hnativeAbove, hbelow, habove,
        hquotient, hremainderEq, hincrement]
    · have htie : 2 * remainder.toNat = den.toNat := by
        omega
      have hnativeAbove :
          FloatLib.Numerics.FixedWord.UInt128.less den doubled.value = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        have hlt :=
          (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff den doubled.value).1 htrue
        rw [hdouble, htie] at hlt
        omega
      have hnativeEqual : doubled.value = den := by
        apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
        rw [hdouble, htie]
      have hlessSelf :
          FloatLib.Numerics.FixedWord.UInt128.less den den = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact (Nat.lt_irrefl den.toNat)
          ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff den den).1 htrue)
      unfold roundQuotient Numerics.roundQuotientEven
      simp [doubled, hdoubleCarry, hnativeEqual, hlessSelf,
        htie, hquotient, hremainderEq, heven]
      by_cases hparity : quotient.toNat % 2 = 0
      · simp [hparity]
      · simp [hparity, hincrement]

/-- Native quotient rounding returns the input quotient or its successor when incrementing fits. -/
theorem roundQuotient_toNat_eq_or
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128)
    (hquotientFit : quotient.toNat + 1 < 2 ^ 128) :
    (roundQuotient den quotient remainder).toNat = quotient.toNat ∨
      (roundQuotient den quotient remainder).toNat = quotient.toNat + 1 := by
  have hincrement :
      quotient.increment.toNat = quotient.toNat + 1 :=
    FloatLib.Numerics.FixedWord.UInt128.increment_toNat quotient hquotientFit
  unfold roundQuotient
  dsimp only
  split
  · exact Or.inr hincrement
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr hincrement
    · exact Or.inl rfl

end FloatLib.Numerics.FixedWord.CertifiedDivision

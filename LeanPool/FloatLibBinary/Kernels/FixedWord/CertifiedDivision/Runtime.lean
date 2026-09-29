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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Runtime

/-!
# Certified fixed-word division runtime

The radix-`2^32` loop generates a quotient and remainder candidate for two normalized two-limb
significands of `precision + 1` bits, for any precision from 65 to 126. A separate executable
certificate checks the exact Euclidean equation and remainder bound. Rejected candidates select
the allocation-light restoring accumulator. Mathematical soundness, completeness of the repair,
and equality between that accumulator and the logical recurrence are isolated in
`CertifiedDivision.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.CertifiedDivision

open FloatLib.Numerics.FixedWord

/--
Scaling distance for a normalized quotient of two `precision + 1`-bit significands.

Division needs exactly these two cases: `precision` when the numerator is at least the
denominator, and `precision + 1` otherwise. Keeping the choice closed prevents an unsupported
distance from silently selecting one of the fixed-word layouts.
-/
inductive CandidateShift where
  /-- Scale the numerator by `2^precision`. -/
  | exact
  /-- Scale the numerator by `2^(precision + 1)`. -/
  | extra
  deriving DecidableEq, Repr

namespace CandidateShift

/-- Natural-number exponent represented by a candidate shift for `precision + 1`-bit operands. -/
@[inline] def toNat (precision : Nat) : CandidateShift → Nat
  | .exact => precision
  | .extra => precision + 1

end CandidateShift

/-- A mask selecting the low radix-`2^32` digit of a native word. -/
def radix32Mask : UInt64 := 0xffffffff

/-- The radix `2^32`, represented in a native 64-bit word. -/
def radix32Base : UInt64 := 0x100000000

/-- Read radix-`2^32` digit `index` for `index < 4`; larger indices also return digit 3. -/
@[inline] def wordDigit32 (value : FloatLib.Numerics.FixedWord.UInt128) : Nat → UInt64
  | 0 => low32 value.lo
  | 1 => high32 value.lo
  | 2 => low32 value.hi
  | _ => high32 value.hi

/-- Pack four little-endian digits, each below `2^32`, into a 128-bit word. -/
@[inline] def wordsOfDigits32
    (d0 d1 d2 d3 : UInt64) : FloatLib.Numerics.FixedWord.UInt128 :=
  {
    lo := d0 ||| (d1 <<< 32)
    hi := d2 ||| (d3 <<< 32)
  }

/--
Apply the at-most-two quotient-digit corrections required by normalized Knuth division.
-/
@[inline] def adjustQuotientDigit
    (qhat rhat v3 v2 nextDigit : UInt64) : UInt64 × UInt64 :=
  let adjustOnce (q r : UInt64) : UInt64 × UInt64 :=
    if r < radix32Base &&
        q * v2 > (r <<< 32) + nextDigit then
      (q - 1, r + v3)
    else
      (q, r)
  let first := adjustOnce qhat rhat
  adjustOnce first.1 first.2

/-- Result of one radix-`2^32` long-division step. -/
structure Radix32StepResult where
  /-- Least-significant remainder digit. -/
  d0 : UInt64
  /-- Second remainder digit. -/
  d1 : UInt64
  /-- Third remainder digit. -/
  d2 : UInt64
  /-- Fourth remainder digit. -/
  d3 : UInt64
  /-- Most-significant remainder digit. -/
  d4 : UInt64
  /-- Quotient digit selected by this step. -/
  quotient : UInt64
  deriving DecidableEq, Repr

/--
Consume one radix-`2^32` quotient digit from a five-digit partial dividend.
-/
@[inline] def radix32Step
    (v0 v1 v2 v3 d0 d1 d2 d3 d4 : UInt64) :
    Radix32StepResult :=
  let estimate :=
    if d4 == v3 then
      (radix32Mask, d3 + v3)
    else
      let pair := (d4 <<< 32) + d3
      (pair / v3, pair % v3)
  let adjusted :=
    adjustQuotientDigit estimate.1 estimate.2 v3 v2 d2
  let qhat := adjusted.1
  let product0 := qhat * v0
  let subtrahend0 := low32 product0
  let borrow0 : UInt64 := if d0 < subtrahend0 then 1 else 0
  let out0 :=
    if borrow0 == 1 then d0 + radix32Base - subtrahend0
    else d0 - subtrahend0
  let product1 := qhat * v1 + (product0 >>> 32)
  let subtrahend1 := low32 product1 + borrow0
  let borrow1 : UInt64 := if d1 < subtrahend1 then 1 else 0
  let out1 :=
    if borrow1 == 1 then d1 + radix32Base - subtrahend1
    else d1 - subtrahend1
  let product2 := qhat * v2 + (product1 >>> 32)
  let subtrahend2 := low32 product2 + borrow1
  let borrow2 : UInt64 := if d2 < subtrahend2 then 1 else 0
  let out2 :=
    if borrow2 == 1 then d2 + radix32Base - subtrahend2
    else d2 - subtrahend2
  let product3 := qhat * v3 + (product2 >>> 32)
  let subtrahend3 := low32 product3 + borrow2
  let borrow3 : UInt64 := if d3 < subtrahend3 then 1 else 0
  let out3 :=
    if borrow3 == 1 then d3 + radix32Base - subtrahend3
    else d3 - subtrahend3
  let highSubtrahend := (product3 >>> 32) + borrow3
  let negative := d4 < highSubtrahend
  let out4 :=
    if negative then d4 + radix32Base - highSubtrahend
    else d4 - highSubtrahend
  if negative then
    let sum0 := out0 + v0
    let add0 := low32 sum0
    let sum1 := out1 + v1 + (sum0 >>> 32)
    let add1 := low32 sum1
    let sum2 := out2 + v2 + (sum1 >>> 32)
    let add2 := low32 sum2
    let sum3 := out3 + v3 + (sum2 >>> 32)
    let add3 := low32 sum3
    {
      d0 := add0
      d1 := add1
      d2 := add2
      d3 := add3
      d4 := low32 (out4 + (sum3 >>> 32))
      quotient := qhat - 1
    }
  else
    {
      d0 := out0
      d1 := out1
      d2 := out2
      d3 := out3
      d4 := out4
      quotient := qhat
    }

/--
Generate a quotient/remainder candidate for a normalized numerator and denominator of
`precision + 1` bits, with `64 < precision ≤ 126`.

The intended result is `(num * 2^(shift.toNat precision)) / den` together with the corresponding
remainder. Knuth's Algorithm D runs in radix `2^32` after normalizing the divisor by
`127 - precision` bits so that its leading bit is bit 127. The numerator receives the same
normalization, which places the scaled dividend at `num * 2^127` or `num * 2^128` independently
of the precision, so the digit layout below does not depend on the format. The shift argument has
only the two layouts supported by this kernel.

The Algorithm D result remains a speculative fast candidate: callers independently check it with
`certificate`. `checkedCandidate` retains this exact hot path and invokes a proved restoring
divider only after a failed certificate.
-/
@[inline] def candidate (precision : Nat)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift) :
    FloatLib.Numerics.FixedWord.UInt128 × FloatLib.Numerics.FixedWord.UInt128 :=
  let normalization := 127 - precision
  let normalized := FloatLib.Numerics.FixedWord.UInt128.shiftLeft den normalization
  let v0 := wordDigit32 normalized 0
  let v1 := wordDigit32 normalized 1
  let v2 := wordDigit32 normalized 2
  let v3 := wordDigit32 normalized 3
  let n0 := wordDigit32 num 0
  let n1 := wordDigit32 num 1
  let n2 := wordDigit32 num 2
  let n3 := wordDigit32 num 3
  let exact :=
    match shift with
    | .exact => true
    | .extra => false
  let u0 : UInt64 := 0
  let u1 : UInt64 := 0
  let u2 : UInt64 := 0
  let u3 := if exact then low32 (n0 <<< 31) else 0
  let u4 :=
    if exact then low32 ((n0 >>> 1) ||| (n1 <<< 31)) else n0
  let u5 :=
    if exact then low32 ((n1 >>> 1) ||| (n2 <<< 31)) else n1
  let u6 :=
    if exact then low32 ((n2 >>> 1) ||| (n3 <<< 31)) else n2
  let u7 := if exact then n3 >>> 1 else n3
  let step3 := radix32Step v0 v1 v2 v3 u3 u4 u5 u6 u7
  let step2 :=
    radix32Step v0 v1 v2 v3 u2
      step3.d0 step3.d1 step3.d2 step3.d3
  let step1 :=
    radix32Step v0 v1 v2 v3 u1
      step2.d0 step2.d1 step2.d2 step2.d3
  let step0 :=
    radix32Step v0 v1 v2 v3 u0
      step1.d0 step1.d1 step1.d2 step1.d3
  (
    wordsOfDigits32
      step0.quotient step1.quotient step2.quotient step3.quotient,
    FloatLib.Numerics.FixedWord.UInt128.shiftRight
      (wordsOfDigits32 step0.d0 step0.d1 step0.d2 step0.d3) normalization
  )

/-- Embed a 128-bit word into the low half of a 256-bit word. -/
@[inline] def widenLow
    (value : FloatLib.Numerics.FixedWord.UInt128) : FloatLib.Numerics.FixedWord.UInt256 :=
  ⟨0, 0, value.hi, value.lo⟩

/--
Independently certify a quotient/remainder candidate for the selected scaling distance.

The check is the exact Euclidean equation
`quotient * den + remainder = num * 2^(shift.toNat precision)`, computed in 256 bits without
carry, together with `remainder < den`. For `64 < precision ≤ 126`, `certificate_sound` shows
that the check implies that the candidate is the true quotient and remainder.
-/
@[inline] def certificate (precision : Nat)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128) : Bool :=
  let product := FloatLib.Numerics.FixedWord.mul128 quotient den
  let sum := FloatLib.Numerics.FixedWord.add256 product (widenLow remainder)
  sum.carry == 0 &&
    sum.value ==
      FloatLib.Numerics.FixedWord.UInt256.ofUInt128ShiftedLeft num (shift.toNat precision) &&
    FloatLib.Numerics.FixedWord.UInt128.less remainder den

/-- Quotient and remainder selected for normalized two-limb division. -/
structure CandidateResult where
  /-- Quotient of the scaled numerator. -/
  quotient : FloatLib.Numerics.FixedWord.UInt128
  /-- Euclidean remainder of the scaled numerator. -/
  remainder : FloatLib.Numerics.FixedWord.UInt128
  deriving DecidableEq, Repr

/--
Initial quotient and remainder for operands with `0 < den` and `num < 2 * den`.
-/
@[inline] def restoringInitial
    (num den : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.RestoringQuotient.QuotientState
      FloatLib.Numerics.FixedWord.UInt128 :=
  let less := FloatLib.Numerics.FixedWord.UInt128.less num den
  if less then
    { quotient := ⟨0, 0⟩, remainder := num }
  else
    { quotient := ⟨0, 1⟩
      remainder := FloatLib.Numerics.FixedWord.UInt128.sub num den }

/--
Recompute a scaled quotient with the allocation-light two-limb restoring loop.

This is a cold repair path. Normalized significands differ by less than a factor of two, so the
initial quotient is zero or one and the selected shift generates the required `precision + 1`
quotient bits. `restoringCandidate_eq_quotientSteps128` proves that this direct accumulator call
equals the logical restoring recurrence.
-/
@[inline] def restoringCandidate (precision : Nat)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift) :
    FloatLib.Numerics.FixedWord.RestoringQuotient.QuotientState
      FloatLib.Numerics.FixedWord.UInt128 :=
  FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128Impl
    den (shift.toNat precision) (restoringInitial num den)

/--
Run the fast Algorithm D candidate and repair a failed certificate with restoring division.

The common path is one Algorithm D candidate plus one certificate. If that check rejects the
candidate, the function selects the restoring-division result instead. The proof module shows
that this selected pair is exact on the normalized domain, so the backend does not need an
additional failure branch.
-/
@[inline] def checkedCandidate (precision : Nat)
    (num den : FloatLib.Numerics.FixedWord.UInt128) (shift : CandidateShift) :
    CandidateResult :=
  let fast := candidate precision num den shift
  if certificate precision num den shift fast.1 fast.2 then
    { quotient := fast.1, remainder := fast.2 }
  else
    let repaired := restoringCandidate precision num den shift
    { quotient := repaired.quotient
      remainder := repaired.remainder }

/--
Round a certified quotient to nearest, ties to even.

`roundQuotient_toNat` requires `den < 2^127`, `remainder < den`, and the incremented quotient
below `2^128`; the two-word backends satisfy these for their normalized operands.
-/
@[inline] def roundQuotient
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  let doubled := FloatLib.Numerics.FixedWord.add128 remainder remainder
  if doubled.carry != 0 ||
      FloatLib.Numerics.FixedWord.UInt128.less den doubled.value then
    quotient.increment
  else if doubled.value == den then
    if (quotient.lo &&& 1) == 0 then quotient else quotient.increment
  else
    quotient

end FloatLib.Numerics.FixedWord.CertifiedDivision

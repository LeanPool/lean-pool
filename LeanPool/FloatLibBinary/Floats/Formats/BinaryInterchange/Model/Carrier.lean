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


import Mathlib.Data.Nat.Bitwise
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Storage

/-!
# Descriptor-indexed binary-interchange proof model

`Model fmt` is the bit-exact specification carrier for the binary-interchange family.
Statically declared formats use
`FloatLib.Floats.ExecFloat F`, whose runtime representation is selected by `EncodedFormat F`.

This model stores `BitVec fmt.bitWidth` so descriptor-generic specifications and refinement proofs
can quantify over a runtime-selected layout. Concrete format packages bridge their direct runtime
codes to this model at the proof boundary.

## References

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Sections 3.4 and 6.2,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

/--
Descriptor-indexed bit-level proof model for format `fmt`.

The carrier is `BitVec fmt.bitWidth`; every stored bit is part of the format.
-/
structure Model (fmt : FloatFormat) where
  /-- Raw binary storage pattern. -/
  bits : FloatFormat.ExecWord fmt
  deriving DecidableEq, Repr

namespace Model

/-- Wrap a storage word as a `Model`. -/
@[inline] def ofBits {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) : Model fmt := ⟨b⟩

/-- Wrap a `Nat` pattern, reduced to the format's exact bit width. -/
@[inline] def ofNatBits {fmt : FloatFormat} (n : Nat) : Model fmt :=
  ofBits (FloatFormat.ofWordNat fmt n)

/-- Extract the raw storage word. -/
@[inline] def toBits {fmt : FloatFormat} (x : Model fmt) : FloatFormat.ExecWord fmt := x.bits

/-- Return the encoded bit pattern as a natural number. -/
@[inline] def toNatBits {fmt : FloatFormat} (x : Model fmt) : Nat :=
  x.bits.toNat

/-- Every encoded word lies below the radix determined by its stored width. -/
theorem toNatBits_lt_two_pow {fmt : FloatFormat} (x : Model fmt) :
    x.toNatBits < 2 ^ fmt.bitWidth :=
  x.bits.toFin.isLt

/-- Wrap a `UInt32` pattern, truncating it when the destination has fewer than 32 bits. -/
@[inline] def ofUInt32 {fmt : FloatFormat} (b : UInt32) : Model fmt :=
  ofNatBits b.toNat

/-- Re-encoding the exact natural-number bit pattern preserves a binary value. -/
@[simp] theorem ofNatBits_toNatBits {fmt : FloatFormat} (x : Model fmt) :
    ofNatBits x.toNatBits = x := by
  cases x with
  | mk bits =>
      apply congrArg ofBits
      change BitVec.ofNat fmt.bitWidth bits.toNat = bits
      rw [BitVec.ofNat_toNat]
      simp

/-- An in-range natural-number pattern is not changed by fixed-width encoding. -/
@[simp] theorem toNatBits_ofNatBits_of_lt {fmt : FloatFormat} (bits : Nat)
    (hbits : bits < 2 ^ fmt.bitWidth) :
    (ofNatBits (fmt := fmt) bits).toNatBits = bits := by
  change (BitVec.ofNat fmt.bitWidth bits).toNat = bits
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbits]

/-- Wrapping a storage word and reading it back is the identity. -/
@[simp] theorem toBits_ofBits {fmt : FloatFormat} (b : FloatFormat.ExecWord fmt) :
    toBits (ofBits (fmt := fmt) b) = b :=
  rfl

/-- Rewrapping the storage word of a value is the identity. -/
@[simp] theorem ofBits_toBits {fmt : FloatFormat} (x : Model fmt) :
    ofBits (toBits x) = x := by
  cases x
  rfl

instance {fmt : FloatFormat} : Inhabited (Model fmt) where
  default := ofNatBits 0

/-! ## Field extraction and classification -/

/-- Whether the sign bit is set. -/
@[inline] def signBit {fmt : FloatFormat} (x : Model fmt) : Bool :=
  (x.bits &&& FloatFormat.signMask fmt) != 0

/-- The executable sign test is the most significant bit of the storage word. -/
theorem signBit_eq_msb {fmt : FloatFormat} (x : Model fmt) :
    signBit x = x.bits.msb := by
  unfold signBit FloatFormat.signMask FloatFormat.ofWordNat FloatFormat.signMaskNat
    FloatFormat.signBitIndex
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  rw [BitVec.toNat_ne, BitVec.toNat_and, BitVec.toNat_ofNat]
  have hwidth : 0 < fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have hexponent : fmt.bitWidth - 1 < fmt.bitWidth :=
    Nat.sub_one_lt (Nat.ne_of_gt hwidth)
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hexponent)]
  rw [Nat.and_two_pow]
  have htestBit : x.bits.toNat.testBit (fmt.bitWidth - 1) = x.bits.msb := by
    simpa [BitVec.getLsbD] using (BitVec.msb_eq_getLsbD_last x.bits).symm
  rw [htestBit]
  cases x.bits.msb <;> simp

/-- The biased exponent field as a natural number. -/
@[inline] def expField {fmt : FloatFormat} (x : Model fmt) : Nat :=
  ((x.bits >>> fmt.fracWidth) &&& FloatFormat.expAllOnes fmt).toNat

/-- The low `fracWidth` bits of the fraction field. -/
@[inline] def fracField {fmt : FloatFormat} (x : Model fmt) : Nat :=
  (x.bits &&& FloatFormat.fracMask fmt).toNat

/-- Whether `x` has an IEEE NaN bit pattern. -/
@[inline] def IEEE.isNaN {fmt : FloatFormat} (x : Model fmt) : Bool :=
  expField x == FloatFormat.expAllOnesNat fmt && fracField x != 0

/-- Whether `x` has an IEEE quiet-NaN bit pattern. -/
@[inline] def IEEE.isQNaN {fmt : FloatFormat} (x : Model fmt) : Bool :=
  IEEE.isNaN x && (x.bits &&& FloatFormat.quietBit fmt) != 0

/-- Whether `x` has an IEEE signaling-NaN bit pattern. -/
@[inline] def IEEE.isSNaN {fmt : FloatFormat} (x : Model fmt) : Bool :=
  IEEE.isNaN x && (x.bits &&& FloatFormat.quietBit fmt) == 0

/-- Whether `x` has an IEEE infinity bit pattern. -/
@[inline] def IEEE.isInf {fmt : FloatFormat} (x : Model fmt) : Bool :=
  expField x == FloatFormat.expAllOnesNat fmt && fracField x == 0

/-- Whether `x` has an IEEE signed-zero bit pattern. -/
@[inline] def IEEE.isZero {fmt : FloatFormat} (x : Model fmt) : Bool :=
  expField x == 0 && fracField x == 0

/-- Whether `x` has an IEEE finite bit pattern. -/
@[inline] def IEEE.isFinite {fmt : FloatFormat} (x : Model fmt) : Bool :=
  expField x != FloatFormat.expAllOnesNat fmt

/-! ## Policy-aware classification -/

/-- Whether `x` is one of the NaN encodings selected by its complete format. -/
@[inline] def isNaN {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match fmt.encoding with
  | .ieee => IEEE.isNaN x
  | .finiteMaxNaN =>
      expField x == fmt.expAllOnesNat && fracField x == fmt.fracMaskNat
  | .finiteUnsignedZero => x.bits == fmt.signMask
  | .finite => false

/--
Whether `x` is a quiet NaN.

The non-IEEE policies represented by `FloatFormat.Encoding` do not distinguish signaling from
quiet NaNs, so every NaN in those formats is classified as quiet.
-/
@[inline] def isQNaN {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match fmt.encoding with
  | .ieee => IEEE.isQNaN x
  | .finiteMaxNaN | .finiteUnsignedZero => isNaN x
  | .finite => false

/-- Whether `x` is a signaling NaN. Only the IEEE encoding has signaling NaNs. -/
@[inline] def isSNaN {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match fmt.encoding with
  | .ieee => IEEE.isSNaN x
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => false

/-- A value that is not a NaN cannot be a signaling NaN. -/
theorem isSNaN_eq_false_of_isNaN_eq_false {fmt : FloatFormat}
    (x : Model fmt) (hx : isNaN x = false) :
    isSNaN x = false := by
  cases hencoding : fmt.encoding <;>
    simp_all [isSNaN, isNaN, IEEE.isSNaN]

/-- Whether `x` is an infinity. Only the IEEE encoding contains infinities. -/
@[inline] def isInf {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match fmt.encoding with
  | .ieee => IEEE.isInf x
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => false

/-- Whether `x` denotes zero under its complete format. -/
@[inline] def isZero {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match fmt.encoding with
  | .finiteUnsignedZero => x.bits == 0
  | .ieee | .finiteMaxNaN | .finite => IEEE.isZero x

/-- Whether `x` denotes a finite value under its complete format. -/
@[inline] def isFinite {fmt : FloatFormat} (x : Model fmt) : Bool :=
  match fmt.encoding with
  | .ieee => IEEE.isFinite x
  | .finiteMaxNaN | .finiteUnsignedZero => !isNaN x
  | .finite => true

/-- Whether `x` is a finite subnormal under its complete format. -/
@[inline] def isSubnormal {fmt : FloatFormat} (x : Model fmt) : Bool :=
  expField x == 0 && fracField x != 0

/-! ## Encoding and constants -/

/-- Pack a sign, biased exponent, and fraction into one exact-width storage word. -/
@[inline] def mkBits (fmt : FloatFormat) (sign : Bool) (exp : Nat) (frac : Nat) :
    FloatFormat.ExecWord fmt :=
  let s : FloatFormat.ExecWord fmt := if sign then FloatFormat.signMask fmt else 0
  let e : FloatFormat.ExecWord fmt :=
    (FloatFormat.ofWordNat fmt exp &&& FloatFormat.expAllOnes fmt) <<< fmt.fracWidth
  let f : FloatFormat.ExecWord fmt :=
    FloatFormat.ofWordNat fmt frac &&& FloatFormat.fracMask fmt
  s ||| e ||| f

/-- Construct a value from its sign, exponent, and fraction fields. -/
@[inline] def ofFields (fmt : FloatFormat) (sign : Bool) (exp : Nat) (frac : Nat) :
    Model fmt :=
  ofBits (mkBits fmt sign exp frac)

/-- Positive zero. -/
@[inline] def posZero (fmt : FloatFormat) : Model fmt :=
  ofNatBits 0

/-- The negative-zero bit pattern; it denotes NaN in FNUZ formats. -/
@[inline] def negZero (fmt : FloatFormat) : Model fmt :=
  ofBits (FloatFormat.signMask fmt)

/-- Positive one. -/
@[inline] def posOne (fmt : FloatFormat) : Model fmt :=
  ofFields fmt false fmt.exponentBias 0

/-- Negative one. -/
@[inline] def negOne (fmt : FloatFormat) : Model fmt :=
  ofFields fmt true fmt.exponentBias 0

/-- The positive-infinity IEEE bit pattern; use `infinityOption` for policy-aware construction. -/
@[inline] def posInf (fmt : FloatFormat) : Model fmt :=
  ofBits (FloatFormat.expMask fmt)

/-- The negative-infinity IEEE bit pattern; use `infinityOption` for policy-aware construction. -/
@[inline] def negInf (fmt : FloatFormat) : Model fmt :=
  ofBits (FloatFormat.signMask fmt ||| FloatFormat.expMask fmt)

/-- Finite value of greatest magnitude with the requested sign. -/
@[inline] def maxFinite (fmt : FloatFormat) (sign : Bool) : Model fmt :=
  ofFields fmt sign fmt.maxFiniteExpField fmt.maxFiniteFracField

/-- Largest finite positive value. -/
@[inline] def posMaxFinite (fmt : FloatFormat) : Model fmt :=
  maxFinite fmt false

/-- Finite value with the largest negative magnitude. -/
@[inline] def negMaxFinite (fmt : FloatFormat) : Model fmt :=
  maxFinite fmt true

/-- The canonical IEEE quiet-NaN bit pattern; use `canonicalNaNOption` for other encodings. -/
@[inline] def canonicalNaN (fmt : FloatFormat) : Model fmt :=
  ofBits (FloatFormat.expMask fmt ||| FloatFormat.quietBit fmt)

/-! ## Policy-aware constants -/

/-- Signed zero, canonicalizing negative zero when the format has only one zero. -/
@[inline] def zero (fmt : FloatFormat) (sign : Bool) : Model fmt :=
  if sign && fmt.supportsSignedZero then negZero fmt else posZero fmt

/-- Signed infinity when the format supports it. -/
@[inline] def infinityOption (fmt : FloatFormat) (sign : Bool) : Option (Model fmt) :=
  if fmt.supportsInfinity then some (if sign then negInf fmt else posInf fmt) else none

/-- A canonical NaN when the format has a NaN encoding. -/
@[inline] def canonicalNaNOption (fmt : FloatFormat) : Option (Model fmt) :=
  match fmt.encoding with
  | .ieee => some (canonicalNaN fmt)
  | .finiteMaxNaN =>
      some (ofFields fmt false fmt.expAllOnesNat fmt.fracMaskNat)
  | .finiteUnsignedZero => some (negZero fmt)
  | .finite => none

/--
Total result for an invalid operation in the complete format descriptor.

Formats with a NaN encoding use their canonical NaN. A format whose every bit pattern is numeric
uses positive zero because it has no exceptional result to encode.
-/
@[inline] def invalidResult (fmt : FloatFormat) : Model fmt :=
  match fmt.encoding with
  | .ieee => canonicalNaN fmt
  | .finiteMaxNaN =>
      ofFields fmt false fmt.expAllOnesNat fmt.fracMaskNat
  | .finiteUnsignedZero => negZero fmt
  | .finite => posZero fmt

/--
Signed infinity when the format supports it, otherwise the same-sign largest finite value.

This constructs a range boundary for saturation and interval endpoints. Nonsaturating
conversion, arithmetic, and exact reductions use `nativeOverflow`, which may return NaN
when the format reserves an exceptional encoding.
-/
@[inline] def infinityOrMaxFinite (fmt : FloatFormat) (sign : Bool) : Model fmt :=
  match fmt.encoding with
  | .ieee => if sign then negInf fmt else posInf fmt
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => maxFinite fmt sign

/-- Conventional IEEE policy zero is the usual signed zero. -/
@[simp] theorem zero_eq_signedZero_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) :
    zero fmt sign = if sign then negZero fmt else posZero fmt := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  cases sign <;>
    simp [zero, FloatFormat.supportsSignedZero, hencoding]

/-- Conventional IEEE invalid operations return the canonical NaN. -/
@[simp] theorem invalidResult_eq_canonicalNaN_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    invalidResult fmt = canonicalNaN fmt := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  simp [invalidResult, hencoding]

/-! ## NaN propagation -/

/-- Set the quiet bit of a NaN, leaving non-NaN values unchanged. -/
@[inline] def quietNaN {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match fmt.encoding with
  | .ieee =>
      if IEEE.isNaN x then ofBits (x.bits ||| FloatFormat.quietBit fmt) else x
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => x

/-- Return `x` quieted when it is a NaN. -/
@[inline] def chooseNaN1 {fmt : FloatFormat} (x : Model fmt) : Option (Model fmt) :=
  if isNaN x then some (quietNaN x) else none

/-- Select signaling NaNs before quiet NaNs, breaking ties from left to right. -/
@[inline] def chooseNaN2 {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  if isSNaN x then some (quietNaN x)
  else if isSNaN y then some (quietNaN y)
  else if isNaN x then some (quietNaN x)
  else if isNaN y then some (quietNaN y)
  else none

/-- Ternary NaN selection used by fused multiply-add. -/
@[inline] def chooseNaN3 {fmt : FloatFormat} (x y z : Model fmt) : Option (Model fmt) :=
  if isSNaN x then some (quietNaN x)
  else if isSNaN y then some (quietNaN y)
  else if isSNaN z then some (quietNaN z)
  else if isNaN x then some (quietNaN x)
  else if isNaN y then some (quietNaN y)
  else if isNaN z then some (quietNaN z)
  else none

/--
Return a selected NaN, or continue with evidence that NaN selection produced no result.

The continuation proof is erased. Keeping this dependent boundary beside the NaN selectors lets
operations rule out impossible ordinary branches without duplicating selection logic.
-/
@[inline] def withNaNSelection {fmt : FloatFormat}
    (selected : Option (Model fmt))
    (otherwise : selected = none → Model fmt) : Model fmt :=
  if hselected : selected = none then
    otherwise hselected
  else
    selected.get (by
      cases h : selected with
      | none => exact (hselected h).elim
      | some nan => simp)

/-- A failed NaN selection enters the ordinary operation. -/
@[simp] theorem withNaNSelection_of_none {fmt : FloatFormat}
    (selected : Option (Model fmt))
    (otherwise : selected = none → Model fmt)
    (hselected : selected = none) :
    withNaNSelection selected otherwise = otherwise hselected := by
  simp [withNaNSelection, hselected]

/-- A successful NaN selection returns the selected NaN. -/
@[simp] theorem withNaNSelection_of_some {fmt : FloatFormat}
    (selected : Option (Model fmt))
    (otherwise : selected = none → Model fmt)
    (nan : Model fmt) (hselected : selected = some nan) :
    withNaNSelection selected otherwise = nan := by
  simp [withNaNSelection, hselected]

/-! ## Sign and adjacency -/

/-- Flip only the stored sign bit, without interpreting the format's encoding policy. -/
@[inline] def toggleSign {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  ofBits (x.bits ^^^ FloatFormat.signMask fmt)

/-- Toggling the stored sign bit preserves the fraction field. -/
@[simp] theorem fracField_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    fracField (toggleSign x) = fracField x := by
  unfold toggleSign fracField ofBits FloatFormat.fracMask FloatFormat.ofWordNat
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < fmt.fracWidth
  · have hne : fmt.bitWidth - 1 ≠ i := by
      unfold FloatFormat.bitWidth
      omega
    simp [BitVec.toNat_and, BitVec.toNat_xor, Nat.testBit_and, Nat.testBit_xor,
      FloatFormat.fracMaskNat, FloatFormat.signMask_toNat,
      Nat.testBit_two_pow_of_ne hne, hi]
  · simp [BitVec.toNat_and, BitVec.toNat_xor, Nat.testBit_and,
    FloatFormat.fracMaskNat, hi]

/-- Toggling the stored sign bit preserves the exponent field. -/
@[simp] theorem expField_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    expField (toggleSign x) = expField x := by
  unfold toggleSign expField ofBits FloatFormat.expAllOnes FloatFormat.ofWordNat
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < fmt.expWidth
  · have hne : fmt.bitWidth - 1 ≠ fmt.fracWidth + i := by
      unfold FloatFormat.bitWidth
      omega
    simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_xor,
      Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
      FloatFormat.expAllOnesNat, FloatFormat.signMask_toNat,
      Nat.testBit_two_pow_of_ne hne, hi]
  · simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_xor,
      Nat.testBit_and, Nat.testBit_shiftRight, FloatFormat.expAllOnesNat, hi]

/-- Toggling the stored sign bit complements the decoded sign. -/
@[simp] theorem signBit_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    signBit (toggleSign x) = !signBit x := by
  rw [signBit_eq_msb, signBit_eq_msb]
  unfold toggleSign ofBits
  rw [BitVec.msb_xor]
  have hmask : (FloatFormat.signMask fmt).msb = true := by
    have hwidth : 0 < fmt.bitWidth := by
      unfold FloatFormat.bitWidth
      omega
    rw [BitVec.msb_eq_getLsbD_last]
    simp [BitVec.getLsbD, FloatFormat.signMask, FloatFormat.ofWordNat,
      FloatFormat.signMaskNat, FloatFormat.signBitIndex, hwidth]
  rw [hmask]
  cases x.bits.msb <;> rfl

/-- Toggling the stored sign bit twice restores the original word. -/
@[simp] theorem toggleSign_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    toggleSign (toggleSign x) = x := by
  apply congrArg ofBits
  change (x.bits ^^^ FloatFormat.signMask fmt) ^^^
      FloatFormat.signMask fmt = x.bits
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Toggling the stored sign bit preserves IEEE NaN classification. -/
@[simp] theorem IEEE.isNaN_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isNaN (toggleSign x) = IEEE.isNaN x := by
  simp [IEEE.isNaN]

/-- Toggling the stored sign bit preserves IEEE infinity classification. -/
@[simp] theorem IEEE.isInf_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isInf (toggleSign x) = IEEE.isInf x := by
  simp [IEEE.isInf]

/-- Toggling the stored sign bit preserves IEEE zero classification. -/
@[simp] theorem IEEE.isZero_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isZero (toggleSign x) = IEEE.isZero x := by
  simp [IEEE.isZero]

/-- Toggling the stored sign bit preserves IEEE finiteness. -/
@[simp] theorem IEEE.isFinite_toggleSign {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isFinite (toggleSign x) = IEEE.isFinite x := by
  simp [IEEE.isFinite]

/--
Negate an encoded value according to its format.

Formats with signed zero use the flat sign-bit operation. An unsigned-zero format preserves its
single zero and reserved NaN encodings instead of exchanging them.
-/
@[inline] def neg {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if fmt.supportsSignedZero then
    toggleSign x
  else if isNaN x || isZero x then
    x
  else
    toggleSign x

/-- Formats with signed zero implement negation as a flat stored-sign toggle. -/
theorem neg_eq_toggleSign_of_supportsSignedZero {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.supportsSignedZero = true) :
    neg x = toggleSign x := by
  simp [neg, hfmt]

/-- An unsigned-zero format preserves a NaN under negation. -/
theorem neg_eq_self_of_not_supportsSignedZero_of_isNaN {fmt : FloatFormat}
    (x : Model fmt) (hfmt : fmt.supportsSignedZero = false)
    (hx : isNaN x = true) :
    neg x = x := by
  simp [neg, hfmt, hx]

/-- An unsigned-zero format preserves its single zero under negation. -/
theorem neg_eq_self_of_not_supportsSignedZero_of_isZero {fmt : FloatFormat}
    (x : Model fmt) (hfmt : fmt.supportsSignedZero = false)
    (hx : isZero x = true) :
    neg x = x := by
  simp [neg, hfmt, hx]

/-- A value that is neither NaN nor zero is negated by the raw stored-sign toggle. -/
theorem neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
    {fmt : FloatFormat} (x : Model fmt)
    (hnan : isNaN x = false) (hzero : isZero x = false) :
    neg x = toggleSign x := by
  simp [neg, hnan, hzero]

/-- Negation preserves the fraction field of every encoded value, including NaNs. -/
@[simp] theorem fracField_neg {fmt : FloatFormat} (x : Model fmt) :
    fracField (neg x) = fracField x := by
  unfold neg
  split
  · simp
  · split <;> simp_all

/-- Negation preserves the exponent field of every encoded value, including infinities and NaNs. -/
@[simp] theorem expField_neg {fmt : FloatFormat} (x : Model fmt) :
    expField (neg x) = expField x := by
  unfold neg
  split
  · simp
  · split <;> simp_all

/-- Negation toggles the sign unless an unsigned-zero format preserves zero or NaN. -/
@[simp] theorem signBit_neg {fmt : FloatFormat} (x : Model fmt) :
    signBit (neg x) =
      if fmt.supportsSignedZero then
        !signBit x
      else if isNaN x || isZero x then
        signBit x
      else
        !signBit x := by
  unfold neg
  split
  · simp
  · split <;> simp_all

/-- Negation preserves IEEE NaN classification. -/
@[simp] theorem IEEE.isNaN_neg {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isNaN (neg x) = IEEE.isNaN x := by
  simp [IEEE.isNaN]

/-- Negation preserves IEEE infinity classification. -/
@[simp] theorem IEEE.isInf_neg {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isInf (neg x) = IEEE.isInf x := by
  simp [IEEE.isInf]

/-- Negation preserves IEEE zero classification. -/
@[simp] theorem IEEE.isZero_neg {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isZero (neg x) = IEEE.isZero x := by
  simp [IEEE.isZero]

/-- Negation preserves IEEE finiteness. -/
@[simp] theorem IEEE.isFinite_neg {fmt : FloatFormat} (x : Model fmt) :
    IEEE.isFinite (neg x) = IEEE.isFinite x := by
  simp [IEEE.isFinite]

/--
Copy the numerical sign of `signSource` onto `magnitude`.

For formats with signed zero, this is the usual quiet sign-bit operation. An unsigned-zero format
uses its sign-bit word as the NaN encoding, so zero and NaN are preserved instead of being changed
into one another. Every other finite value still receives the requested stored sign.
-/
@[inline] def copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) : Model fmt :=
  if !fmt.supportsSignedZero && (isNaN magnitude || isZero magnitude) then
    magnitude
  else if signBit magnitude == signBit signSource then
    magnitude
  else
    toggleSign magnitude

/-- Copying an already equal sign leaves the complete encoded word unchanged. -/
@[simp] theorem copySign_eq_self_of_signBit_eq {fmt : FloatFormat}
    (magnitude signSource : Model fmt)
    (hsign : signBit magnitude = signBit signSource) :
    copySign magnitude signSource = magnitude := by
  simp [copySign, hsign]

/-- An unsigned-zero format preserves its zero when a sign is copied onto it. -/
theorem copySign_eq_self_of_not_supportsSignedZero_of_isZero
    {fmt : FloatFormat} (magnitude signSource : Model fmt)
    (hfmt : fmt.supportsSignedZero = false) (hzero : isZero magnitude = true) :
    copySign magnitude signSource = magnitude := by
  simp [copySign, hfmt, hzero]

/-- An unsigned-zero format preserves its reserved NaN word when a sign is copied onto it. -/
theorem copySign_eq_self_of_not_supportsSignedZero_of_isNaN
    {fmt : FloatFormat} (magnitude signSource : Model fmt)
    (hfmt : fmt.supportsSignedZero = false) (hnan : isNaN magnitude = true) :
    copySign magnitude signSource = magnitude := by
  simp [copySign, hfmt, hnan]

/--
Absolute value under the complete format policy.

This clears an ordinary stored sign. In an unsigned-zero encoding it leaves the unique zero and
reserved NaN word intact, avoiding the raw-bit alias between those two encodings.
-/
@[inline] def abs {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  copySign x (posZero fmt)

/-- The smallest positive subnormal encoding. -/
@[inline] def posMinSubnormal (fmt : FloatFormat) : Model fmt :=
  ofNatBits 1

/-- The negative subnormal of smallest magnitude. -/
@[inline] def negMinSubnormal (fmt : FloatFormat) : Model fmt :=
  ofBits (FloatFormat.signMask fmt ||| FloatFormat.ofWordNat fmt 1)

/--
The next representable value strictly greater than `x`.

A quiet NaN and the positive endpoint are fixed. A signaling NaN becomes the corresponding quiet
NaN; since this value-only operation carries no status, the `invalid` signal IEEE 754-2019 §5.3.1
owes to a signaling operand is reported by `nextUpWithStatus` in `Operations.Runtime`. Formats
without infinity saturate at their largest finite value. In an unsigned-zero encoding, the word
immediately below the negative minimum subnormal is reserved for NaN, so that transition goes
directly to the format's unique zero.
-/
@[inline] def nextUp {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if isNaN x then
    quietNaN x
  else if isInf x && !signBit x then
    x
  else if isZero x then
    posMinSubnormal fmt
  else if !fmt.supportsSignedZero && x.bits == (negMinSubnormal fmt).bits then
    posZero fmt
  else if !fmt.supportsInfinity && x.bits == (posMaxFinite fmt).bits then
    x
  else if signBit x then
    ofBits (x.bits - 1)
  else
    ofBits (x.bits + 1)

/--
The next representable value strictly less than `x`.

A quiet NaN and the negative endpoint are fixed. A signaling NaN becomes the corresponding quiet
NaN; the `invalid` signal it owes is reported by `nextDownWithStatus` in `Operations.Runtime`.
Formats without infinity saturate at their most negative finite value.
-/
@[inline] def nextDown {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if isNaN x then
    quietNaN x
  else if isInf x && signBit x then
    x
  else if isZero x then
    negMinSubnormal fmt
  else if !fmt.supportsInfinity && x.bits == (negMaxFinite fmt).bits then
    x
  else if signBit x then
    ofBits (x.bits + 1)
  else
    ofBits (x.bits - 1)

end Model
end FloatLib.Floats.Formats.BinaryInterchange

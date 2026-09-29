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

import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Lean
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Optimized

/-!
# Widening a packed binary word

Increasing the fraction width while retaining the exponent width shifts all three fields by the
same number of bits. A single shift of the stored word therefore agrees with extracting and
repacking its fields. The destination bound is proved before compilation, avoiding a modulus.

This is a storage identity for every bit pattern. The cast runtime separately checks bias and
encoding compatibility and handles exceptional values before using it as a numerical conversion.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

private theorem toNatBits_ofFields_of_lt (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (he : exponent < 2 ^ fmt.expWidth)
    (hf : fraction < 2 ^ fmt.fracWidth) :
    (ofFields fmt sign exponent fraction).toNatBits =
      (if sign then 1 <<< (fmt.expWidth + fmt.fracWidth) else 0) |||
        (exponent <<< fmt.fracWidth) ||| fraction := by
  rw [ofFields_eq_ofFieldsImpl]
  simp only [ofFieldsImpl, mkBitsImpl, ofBits, toNatBits, BitVec.toNat_ofNatLT,
    FloatFormat.expAllOnesNat, FloatFormat.fracMaskNat,
    Nat.and_two_pow_sub_one_of_lt_two_pow he, Nat.and_two_pow_sub_one_of_lt_two_pow hf]
  rfl

/-- Shifting a stored word by the added fraction width fits the destination storage. -/
theorem toNatBits_shiftLeft_lt {src dst : FloatFormat} (x : Model src)
    (he : src.expWidth = dst.expWidth) (hf : src.fracWidth ≤ dst.fracWidth) :
    x.toNatBits <<< (dst.fracWidth - src.fracWidth) < 2 ^ dst.bitWidth := by
  have hw : src.bitWidth + (dst.fracWidth - src.fracWidth) = dst.bitWidth := by
    simp only [FloatFormat.bitWidth]
    omega
  simpa only [hw] using
    (Nat.shiftLeft_lt (m := dst.fracWidth - src.fracWidth) (toNatBits_lt_two_pow x))

/--
Increase the stored fraction width by shifting the entire word.

This operation preserves fields, without interpreting them. Numerical casts must additionally
check bias and encoding compatibility and apply their exceptional-value policy.
-/
@[inline] def widenBits {src dst : FloatFormat} (x : Model src)
    (he : src.expWidth = dst.expWidth) (hf : src.fracWidth ≤ dst.fracWidth) : Model dst :=
  ofBits (BitVec.ofNatLT (x.toNatBits <<< (dst.fracWidth - src.fracWidth))
    (toNatBits_shiftLeft_lt x he hf))

/-- Shifting the complete word agrees bit for bit with widening its explicit fields. -/
theorem widenBits_eq_ofFields {src dst : FloatFormat} (x : Model src)
    (he : src.expWidth = dst.expWidth) (hf : src.fracWidth ≤ dst.fracWidth) :
    widenBits x he hf = ofFields dst (signBit x) (expField x)
      (fracField x <<< (dst.fracWidth - src.fracWidth)) := by
  have hw : src.fracWidth + (dst.fracWidth - src.fracWidth) = dst.fracWidth := by omega
  have hexp : expField x < 2 ^ dst.expWidth := by
    simpa only [← he] using expField_lt_pow2 x
  have hfrac : fracField x <<< (dst.fracWidth - src.fracWidth) < 2 ^ dst.fracWidth := by
    simpa only [hw] using
      (Nat.shiftLeft_lt (m := dst.fracWidth - src.fracWidth) (fracField_lt_pow2 x))
  have hx := congrArg toNatBits (ofFields_signBit_expField_fracField x)
  rw [toNatBits_ofFields_of_lt src (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)] at hx
  apply congrArg Model.mk
  apply BitVec.eq_of_toNat_eq
  change (widenBits x he hf).toNatBits =
    (ofFields dst (signBit x) (expField x)
      (fracField x <<< (dst.fracWidth - src.fracWidth))).toNatBits
  rw [toNatBits_ofFields_of_lt dst (signBit x) (expField x)
    (fracField x <<< (dst.fracWidth - src.fracWidth)) hexp hfrac]
  change x.toNatBits <<< (dst.fracWidth - src.fracWidth) = _
  rw [← hx, Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib]
  cases signBit x <;> simp [← Nat.shiftLeft_add, Nat.add_assoc, hw, he]

end Model
end FloatLib.Floats.Formats.BinaryInterchange

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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Sqrt.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Square-root specification

The reference operation is descriptor-aware for every validated `FloatFormat`. The model bridge
below is intentionally restricted to conventional IEEE descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.Spec

/-- Descriptor-aware square root rounded to nearest with ties to even. -/
@[inline] def sqrt {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match chooseNaN1 x with
  | some nan => nan
  | none =>
      if isInf x then
        if signBit x then invalidResult fmt else nativeOverflow fmt false
      else if isZero x then
        x
      else if signBit x then
        invalidResult fmt
      else
        match toDyadicOption x with
        | some value =>
            FiniteSqrt.sqrtPositiveDyadic fmt value.significand value.exponent
        | none => invalidResult fmt

/--
For a positive finite conventional-IEEE value, the descriptor-aware square root agrees with the
established unpacked-model result used by the binary32 and binary64 refinements.
-/
theorem sqrt_eq_model
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt)
    (hfinite : isFinite x = true) (hnonzero : isZero x = false)
    (hnonnegative : signBit x = false) :
    sqrt x =
      ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
  obtain ⟨value, hdecode⟩ := exists_toDyadicOption_of_isFinite hfinite
  have hsign : value.negative = false :=
    (sign_eq_signBit_of_toDyadicOption_some hdecode).trans hnonnegative
  have hmantissa : value.significand ≠ 0 := by
    intro hzero
    have hzeroSource :=
      isZero_eq_true_of_toDyadicOption_some_of_mant_eq_zero hdecode hzero
    rw [hnonzero] at hzeroSource
    contradiction
  have hbridge :=
    FiniteSqrt.sqrtPositiveDyadic_eq_model_of_ieee
      hfmt x value hdecode hsign hmantissa
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  simp [sqrt, chooseNaN1, hnan, hinf, hnonzero, hnonnegative,
    hdecode, hbridge]

end Model.Spec
end FloatLib.Floats.Formats.BinaryInterchange

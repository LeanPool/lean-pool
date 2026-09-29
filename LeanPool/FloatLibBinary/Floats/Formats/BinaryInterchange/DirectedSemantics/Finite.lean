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

import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime

/-!
# Finite-operand helpers for directed arithmetic

Finite-operand classification facts support the format-generic directed arithmetic proofs.
Keeping these facts separate lets each arithmetic module focus on its exact intermediate and
rounding argument.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Unary NaN selection is inactive for a finite operand. -/
theorem chooseNaN1_none_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hx : isFinite x = true) :
    chooseNaN1 x = none := by
  simp [chooseNaN1, isNaN_eq_false_of_isFinite_eq_true x hx]

/-- NaN selection is inactive when both operands are finite. -/
theorem chooseNaN2_none_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    chooseNaN2 x y = none :=
  chooseNaN2_none_of_not_isNaN x y
    (isNaN_eq_false_of_isFinite_eq_true x hx)
    (isNaN_eq_false_of_isFinite_eq_true y hy)

/-- A finite nonzero value decodes to a dyadic with nonzero significand. -/
theorem significand_ne_zero_of_toDyadicOption_some_of_isZero_eq_false
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadicOption x = some d) (hzero : isZero x = false) :
    d.significand ≠ 0 := by
  intro hmant
  have := isZero_eq_true_of_toDyadicOption_some_of_mant_eq_zero hd hmant
  simp [hzero] at this

/-! ## Exact intermediates of finite operands -/

/-- The exact dyadic sum of two finite values denotes their real sum. -/
theorem toReal_addDyadic_of_toDyadicOption_some
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadicOption x = some dx) (hdy : toDyadicOption y = some dy) :
    (addDyadic dx dy).toReal = toReal x + toReal y := by
  rw [Dyadic.toReal_addDyadic]
  simp [toReal_eq, hdx, hdy]

/-- The exact dyadic product of two finite values denotes their real product. -/
theorem toReal_mulDyadic_of_toDyadicOption_some
    {fmt : FloatFormat} {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadicOption x = some dx) (hdy : toDyadicOption y = some dy) :
    ({ negative := Bool.xor dx.negative dy.negative
       significand := dx.significand * dy.significand
       exponent := dx.exponent + dy.exponent } : Numerics.Dyadic).toReal =
      toReal x * toReal y := by
  rw [Dyadic.toReal_mul]
  simp [toReal_eq, hdx, hdy]

/-! ## Signed zero of an exactly cancelling sum -/

/-- The signed zero chosen for an exactly cancelling sum denotes zero. -/
@[simp] theorem toReal_zeroForExactSum
    (fmt : FloatFormat) (mode : IEEERoundingMode) (leftSign rightSign : Bool) :
    toReal (zeroForExactSum fmt mode leftSign rightSign) = 0 := by
  cases mode <;> simp [zeroForExactSum]

/-- The signed zero chosen for an exactly cancelling sum is not a NaN. -/
@[simp] theorem isNaN_zeroForExactSum_eq_false
    (fmt : FloatFormat) (mode : IEEERoundingMode) (leftSign rightSign : Bool) :
    isNaN (zeroForExactSum fmt mode leftSign rightSign) = false := by
  cases mode <;> simp [zeroForExactSum]

/-- The signed zero chosen for an exactly cancelling sum denotes zero in the extended reals. -/
@[simp] theorem toEReal_zeroForExactSum
    (fmt : FloatFormat) (mode : IEEERoundingMode) (leftSign rightSign : Bool) :
    toEReal (zeroForExactSum fmt mode leftSign rightSign) = 0 := by
  cases mode <;> simp [zeroForExactSum]

/-! ## Directed operations on finite operands

For modes other than nearest-even, finite addition and multiplication reduce to rounding an exact
dyadic intermediate; finite division with a nonzero divisor rounds an exact scaled rational.
Exact cancellation has a separate signed-zero rule. Square root instead rounds the appropriate
endpoint of a dyadic bracket around the exact root. These characterisations are shared by the
enclosure, non-NaN, and finite-format proofs.
-/

/--
For finite operands, a directed addition is the directed rounding of the exact dyadic sum, or the
rounding direction's signed zero when the sum cancels exactly.
-/
theorem addWithRounding_eq_of_toDyadicOption_some
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearestEven)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadicOption x = some dx) (hdy : toDyadicOption y = some dy) :
    addWithRounding mode x y =
      if (addDyadic dx dy).significand = 0 then
        zeroForExactSum fmt mode dx.negative dy.negative
      else
        roundDyadicWithRounding fmt mode (addDyadic dx dy) := by
  have hx := isFinite_eq_true_of_toDyadicOption_some hdx
  have hy := isFinite_eq_true_of_toDyadicOption_some hdy
  have hchoose := chooseNaN2_none_of_isFinite x y hx hy
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  cases mode <;> first
    | exact absurd rfl hmode
    | simp [addWithRounding, hchoose, hxInf, hyInf, hdx, hdy]

/-- For finite operands, a directed multiplication rounds the exact dyadic product. -/
theorem mulWithRounding_eq_of_toDyadicOption_some
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearestEven)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadicOption x = some dx) (hdy : toDyadicOption y = some dy) :
    mulWithRounding mode x y =
      roundDyadicWithRounding fmt mode
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent } := by
  have hx := isFinite_eq_true_of_toDyadicOption_some hdx
  have hy := isFinite_eq_true_of_toDyadicOption_some hdy
  have hchoose := chooseNaN2_none_of_isFinite x y hx hy
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  cases mode <;> first
    | exact absurd rfl hmode
    | simp [mulWithRounding, hchoose, hxInf, hyInf, hdx, hdy]

/--
For a finite dividend and a finite nonzero divisor, a directed division rounds the exact scaled
rational quotient.
-/
theorem divWithRounding_eq_of_toDyadicOption_some
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearestEven)
    {x y : Model fmt} {dx dy : Numerics.Dyadic}
    (hdx : toDyadicOption x = some dx) (hdy : toDyadicOption y = some dy)
    (hy0 : isZero y = false) :
    divWithRounding mode x y =
      roundRatWithRoundingScaled fmt mode (Bool.xor dx.negative dy.negative)
        dx.significand dy.significand (dx.exponent - dy.exponent) := by
  have hx := isFinite_eq_true_of_toDyadicOption_some hdx
  have hy := isFinite_eq_true_of_toDyadicOption_some hdy
  have hchoose := chooseNaN2_none_of_isFinite x y hx hy
  have hxInf := isInf_eq_false_of_isFinite_eq_true x hx
  have hyInf := isInf_eq_false_of_isFinite_eq_true y hy
  have hdyMant := significand_ne_zero_of_toDyadicOption_some_of_isZero_eq_false hdy hy0
  by_cases hdxMant : dx.significand = 0
  · cases mode <;> first
      | exact absurd rfl hmode
      | simp [divWithRounding, hchoose, hxInf, hyInf, hy0, hdx, hdy, hdxMant, hdyMant,
          roundRatWithRoundingScaled, roundRatMagnitudeDirectedScaled]
  · cases mode <;> first
      | exact absurd rfl hmode
      | simp [divWithRounding, hchoose, hxInf, hyInf, hy0, hdx, hdy, hdxMant]

/-- Every directed square root fixes a finite zero. -/
theorem sqrtWithRounding_eq_self_of_isZero
    {fmt : FloatFormat} (mode : IEEERoundingMode) (hmode : mode ≠ .nearestEven)
    {x : Model fmt} (hfinite : isFinite x = true) (hzero : isZero x = true) :
    sqrtWithRounding mode x = x := by
  have hchoose := chooseNaN1_none_of_isFinite x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  cases mode <;> first
    | exact absurd rfl hmode
    | simp [sqrtWithRounding, hchoose, hinf, hzero]

/-- On a finite positive operand, `sqrtDown` rounds the lower square-root bracket downward. -/
theorem sqrtDown_eq_roundDyadicDown_of_toDyadicOption_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadicOption x = some d) (hsign : signBit x = false) (hzero : isZero x = false) :
    sqrtDown x = roundDyadicDown fmt (sqrtDyadicBracket fmt d).lower := by
  have hfinite := isFinite_eq_true_of_toDyadicOption_some hd
  simp [sqrtDown, sqrtWithRounding, chooseNaN1_none_of_isFinite x hfinite,
    isInf_eq_false_of_isFinite_eq_true x hfinite, hzero, hsign, hd]

/-- On a finite positive operand, `sqrtUp` rounds the upper square-root bracket upward. -/
theorem sqrtUp_eq_roundDyadicUp_of_toDyadicOption_some
    {fmt : FloatFormat} {x : Model fmt} {d : Numerics.Dyadic}
    (hd : toDyadicOption x = some d) (hsign : signBit x = false) (hzero : isZero x = false) :
    sqrtUp x = roundDyadicUp fmt (sqrtDyadicBracket fmt d).upper := by
  have hfinite := isFinite_eq_true_of_toDyadicOption_some hd
  simp [sqrtUp, sqrtWithRounding, chooseNaN1_none_of_isFinite x hfinite,
    isInf_eq_false_of_isFinite_eq_true x hfinite, hzero, hsign, hd]

end Model
end FloatLib.Floats.Formats.BinaryInterchange

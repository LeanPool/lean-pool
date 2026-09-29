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

public import Mathlib.Data.EReal.Basic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Special

/-!
# Extended-real interpretation of binary models

Every non-NaN `Model fmt` has an extended-real interpretation. Finite values use their exact
real decoding, while the two infinities map to `⊥` and `⊤`. The partial interpretation maps NaNs
to `none`; `toEReal` is a convenient totalization that maps that single unordered case to zero.

The definitions and proofs are uniform in `fmt`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-- Extended-real interpretation of `Model`; `none` is reserved exactly for NaNs. -/
noncomputable def toERealOption {fmt : FloatFormat} (x : Model fmt) : Option EReal :=
  if isNaN x then
    none
  else if isInf x then
    some (if signBit x then (⊥ : EReal) else (⊤ : EReal))
  else
    some (toReal x : EReal)

/-- Total extended-real interpretation, with the unordered NaN case mapped to zero. -/
noncomputable def toEReal {fmt : FloatFormat} (x : Model fmt) : EReal :=
  (toERealOption x).getD 0

/-- The partial extended-real interpretation is undefined exactly on NaNs. -/
theorem toERealOption_eq_none_iff_isNaN_eq_true {fmt : FloatFormat} (x : Model fmt) :
    toERealOption x = none ↔ isNaN x = true := by
  cases hnan : isNaN x <;> cases hinf : isInf x <;> simp [toERealOption, hnan, hinf]

/-- A value classified as infinity is not classified as NaN. -/
theorem isNaN_eq_false_of_isInf_eq_true {fmt : FloatFormat} (x : Model fmt)
    (hx : isInf x = true) :
    isNaN x = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hxIEEE : IEEE.isInf x = true := by
        simpa [isInf, hencoding] using hx
      have hparts :
          expField x = FloatFormat.expAllOnesNat fmt ∧ fracField x = 0 := by
        simpa [IEEE.isInf, Bool.and_eq_true] using hxIEEE
      simp [isNaN, hencoding, IEEE.isNaN, hparts.2]
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp [isInf, hencoding] at hx

/-- A value classified as infinity is not classified as zero. -/
theorem isZero_eq_false_of_isInf_eq_true {fmt : FloatFormat} (x : Model fmt)
    (hx : isInf x = true) :
    isZero x = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hxIEEE : IEEE.isInf x = true := by
        simpa [isInf, hencoding] using hx
      have hparts :
          expField x = FloatFormat.expAllOnesNat fmt ∧ fracField x = 0 := by
        simpa [IEEE.isInf, Bool.and_eq_true] using hxIEEE
      have hexponentNe : FloatFormat.expAllOnesNat fmt ≠ 0 :=
        (FloatFormat.expAllOnesNat_pos fmt).ne'
      simp [isZero, hencoding, IEEE.isZero, hparts.1, hexponentNe]
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp [isInf, hencoding] at hx

/-- Finite values are not infinities. -/
theorem isInf_eq_false_of_isFinite_eq_true {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    isInf x = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hxIEEE : IEEE.isFinite x = true := by
        simpa [isFinite, hencoding] using hx
      have hexp : expField x ≠ FloatFormat.expAllOnesNat fmt :=
        (bne_iff_ne).1 hxIEEE
      simp [isInf, hencoding, IEEE.isInf, hexp]
  | finiteMaxNaN | finiteUnsignedZero | finite =>
      simp [isInf, hencoding]

/-- Finite values enter `EReal` through their exact real interpretation. -/
theorem toERealOption_eq_some_toReal_of_isFinite_eq_true
    {fmt : FloatFormat} (x : Model fmt) (hx : isFinite x = true) :
    toERealOption x = some (toReal x : EReal) := by
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
  have hinf := isInf_eq_false_of_isFinite_eq_true x hx
  simp [toERealOption, hnan, hinf]

/-- Totalization agrees with every successful partial interpretation. -/
@[simp] theorem toEReal_of_toERealOption
    {fmt : FloatFormat} {x : Model fmt} {r : EReal} (hx : toERealOption x = some r) :
    toEReal x = r := by
  simp [toEReal, hx]

/-- Totalization maps the partial NaN case to zero. -/
@[simp] theorem toEReal_of_toERealOption_none
    {fmt : FloatFormat} {x : Model fmt} (hx : toERealOption x = none) :
    toEReal x = 0 := by
  simp [toEReal, hx]

/-- Direct case expansion of the total extended-real interpretation. -/
theorem toEReal_eq_ite {fmt : FloatFormat} (x : Model fmt) :
    toEReal x =
      if isNaN x then
        0
      else if isInf x then
        if signBit x then ⊥ else ⊤
      else
        (toReal x : EReal) := by
  unfold toEReal toERealOption
  cases hnan : isNaN x <;> cases hinf : isInf x <;> simp

/-- On finite values, the total interpretation is the coercion of `toReal`. -/
theorem toEReal_eq_coe_toReal_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hx : isFinite x = true) :
    toEReal x = (toReal x : EReal) := by
  exact toEReal_of_toERealOption (toERealOption_eq_some_toReal_of_isFinite_eq_true x hx)

/-- The policy-aware zero constructor denotes zero in the extended reals. -/
@[simp] theorem toEReal_zero (fmt : FloatFormat) (sign : Bool) :
    toEReal (zero fmt sign) = 0 := by
  rw [toEReal_eq_coe_toReal_of_isFinite _ <|
    isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)]
  simp

/-! ## Special values -/

/-- The partial interpretation maps an IEEE model-packed signed zero to zero. -/
@[simp] theorem toERealOption_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Float.Model.UnpackedFloat.Sign) :
    toERealOption (ofModel fmt (.zero sign)) = some 0 := by
  simp [toERealOption, hfmt]

/-- The total interpretation maps an IEEE model-packed signed zero to zero. -/
theorem toEReal_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Float.Model.UnpackedFloat.Sign) :
    toEReal (ofModel fmt (.zero sign)) = 0 := by
  exact toEReal_of_toERealOption (toERealOption_ofModel_zero fmt hfmt sign)

/-- The partial interpretation maps a model-packed infinity to the endpoint selected by its sign. -/
@[simp] theorem toERealOption_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Float.Model.UnpackedFloat.Sign) :
    toERealOption (ofModel fmt (.infinity sign)) =
      some (if modelSignBit sign then (⊥ : EReal) else (⊤ : EReal)) := by
  have hsupports :=
    FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  simp [toERealOption, hsupports]

/-- The total interpretation maps a model-packed infinity to the endpoint selected by its sign. -/
theorem toEReal_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Float.Model.UnpackedFloat.Sign) :
    toEReal (ofModel fmt (.infinity sign)) =
      if modelSignBit sign then (⊥ : EReal) else (⊤ : EReal) := by
  exact toEReal_of_toERealOption (toERealOption_ofModel_infinity fmt hfmt sign)

/-- Either IEEE signed zero denotes zero in the extended reals. -/
@[simp] theorem toEReal_signedZero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (negative : Bool) :
    toEReal (if negative then negZero fmt else posZero fmt) = 0 := by
  cases negative <;>
    simp [posZero_eq_ofModel_zero, negZero_eq_ofModel_zero, hfmt]

/-- Positive executable infinity denotes `⊤` in a conventional IEEE format. -/
@[simp] theorem toEReal_posInf (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toEReal (posInf fmt) = (⊤ : EReal) := by
  rw [posInf_eq_ofModel_infinity]
  exact toEReal_ofModel_infinity fmt hfmt .positive

/-- Negative executable infinity denotes `⊥` in a conventional IEEE format. -/
@[simp] theorem toEReal_negInf (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toEReal (negInf fmt) = (⊥ : EReal) := by
  rw [negInf_eq_ofModel_infinity]
  exact toEReal_ofModel_infinity fmt hfmt .negative

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange

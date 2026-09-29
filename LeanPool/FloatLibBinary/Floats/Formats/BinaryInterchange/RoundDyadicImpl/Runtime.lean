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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rounding

/-!
# Direct generic dyadic rounding

Generic dyadic rounding executes directly with integer arithmetic. `RoundDyadicImpl.Proof`
proves that these functions refine the logical float model and registers the compiler
substitutions. Keeping the implementation here lets runtime backends avoid importing the
substantially larger normalization proof.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/--
Direct integer implementation of nearest-even IEEE dyadic rounding.

This is the compiled counterpart of `ieeeRoundDyadic`. It handles subnormal alignment,
normalization carry, signed underflow to zero, and overflow without constructing a logical model
value.
-/
@[inline] def ieeeRoundDyadicImpl (fmt : FloatFormat) (d : Numerics.Dyadic) : Model fmt :=
  if d.significand == 0 then
    if d.negative then negZero fmt else posZero fmt
  else
    let leading := d.significand.log2
    let totalExponent := (leading : Int) + d.exponent
    if totalExponent < FloatFormat.ieeeMinNormalExponent fmt then
      let fraction :=
        match d.exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with
        | .ofNat shift => d.significand <<< shift
        | .negSucc shift => Numerics.roundShiftRightEven d.significand (shift + 1)
      if fraction == 0 then
        if d.negative then negZero fmt else posZero fmt
      else if fraction == pow2 fmt.fracWidth then
        ofFields fmt d.negative 1 0
      else
        ofFields fmt d.negative 0 fraction
    else
      let roundedMantissa :=
        if fmt.fracWidth ≤ leading then
          Numerics.roundShiftRightEven d.significand (leading - fmt.fracWidth)
        else
          d.significand <<< (fmt.fracWidth - leading)
      let carry := roundedMantissa == pow2 (fmt.fracWidth + 1)
      let normalizedExponent := if carry then totalExponent + 1 else totalExponent
      if normalizedExponent > Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) then
        if d.negative then negInf fmt else posInf fmt
      else
        let normalizedMantissa :=
          if carry then pow2 fmt.fracWidth else roundedMantissa
        ofFields fmt d.negative
          (Int.toNat (normalizedExponent + Int.ofNat fmt.bias))
          (normalizedMantissa - pow2 fmt.fracWidth)

/-- Compiled nearest-even dyadic rounding for every complete format descriptor. -/
@[inline] def roundDyadicImpl (fmt : FloatFormat) (d : Numerics.Dyadic) : Model fmt :=
  if fmt.isIEEE then
    ieeeRoundDyadicImpl fmt d
  else
    roundDyadicGeneral fmt d

end FloatLib.Floats.Formats.BinaryInterchange.Model

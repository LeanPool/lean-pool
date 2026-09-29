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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import Init.Data.Float.Model.Unpacked.Operations.Sqrt

/-!
# Executable native-backed unpacked floating-point square root

The unpacked-float square-root implementation uses the proved native-word integer-root
dispatcher when the radicand fits in `UInt64`. Wider radicands retain Lean's arbitrary-precision
implementation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeModelSqrt

/-- Native-backed implementation of Lean's unpacked square-root core. -/
@[inline] def sqrtCore (spec : Float.Model.Format) (mantissa : Nat) (exponent : Int) :
    Nat × Int × Float.Model.UnpackedFloat.Accuracy :=
  let targetExponent :=
    min (exponent.ediv 2)
      (spec.targetExponent ((Float.Model.totalExponent mantissa exponent + 1).ediv 2))
  let shiftAmount := (exponent - 2 * targetExponent).toNat
  let scaledMantissa := mantissa <<< shiftAmount
  let root := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat scaledMantissa
  let remainder := scaledMantissa - root * root
  let accuracy : Float.Model.UnpackedFloat.Accuracy :=
    if remainder = 0 then
      .exact
    else
      .inexact (if remainder ≤ root then .lt else .gt)
  (root, targetExponent, accuracy)

/-- Native-backed implementation of Lean's logical unpacked floating-point square root. -/
@[inline] def sqrt (spec : Float.Model.Format) :
    Float.Model.UnpackedFloat → Float.Model.UnpackedFloat
  | .notANumber => .notANumber
  | .infinity .positive => .infinity .positive
  | .infinity .negative => .notANumber
  | .finite .negative .. => .notANumber
  | .zero sign => .zero sign
  | .finite .positive mantissa exponent _ =>
      let (mantissa, exponent, accuracy) := sqrtCore spec mantissa exponent
      Float.Model.UnpackedFloat.roundWithAccuracy
        spec .positive mantissa exponent accuracy

end Model.NativeModelSqrt
end FloatLib.Floats.Formats.BinaryInterchange

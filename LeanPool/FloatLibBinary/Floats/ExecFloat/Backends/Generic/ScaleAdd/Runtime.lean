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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Runtime

/-!
# Executable unsigned-scale exact addition

These kernels align and combine signed magnitudes in an unsigned scale coordinate before entering
the product rounder. `ScaleAdd.Proof` proves agreement with exact dyadic addition and rounding for
conventional IEEE descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd

/--
Numerics.Dyadic exponent represented by an unsigned scale accepted by `FiniteProductRound.round`.

The rounder interprets its scale relative to twice the IEEE subnormal alignment offset. The
additional `roundOffset` lets ordinary addition use one-offset coordinates while FMA uses
two-offset product coordinates.
-/
@[inline] def exponent
    (fmt : FloatFormat) (scale roundOffset : Nat) : Int :=
  Int.ofNat (scale + roundOffset) -
    Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)

/-- Round one signed magnitude from an unsigned scale. -/
@[inline] def roundMagnitude
    (fmt : FloatFormat) (roundOffset : Nat)
    (sign : Bool) (mantissa scale : Nat) : Model fmt :=
  FiniteProductRound.round fmt sign mantissa (scale + roundOffset)

/-- Combine nonzero signed magnitudes at one shared unsigned scale and round once. -/
@[inline] def roundMagnitudes
    (fmt : FloatFormat) (roundOffset : Nat)
    (leftSign rightSign : Bool) (left right scale : Nat) : Model fmt :=
  if leftSign == rightSign then
    roundMagnitude fmt roundOffset leftSign (left + right) scale
  else if left == right then
    zero fmt (leftSign && rightSign)
  else if left < right then
    roundMagnitude fmt roundOffset rightSign (right - left) scale
  else
    roundMagnitude fmt roundOffset leftSign (left - right) scale

/--
Align two signed magnitudes in an unsigned scale coordinate and round their exact sum once.
-/
@[inline] def roundSum
    (fmt : FloatFormat) (roundOffset : Nat)
    (leftSign rightSign : Bool)
    (leftMantissa leftScale rightMantissa rightScale : Nat) :
    Model fmt :=
  if leftMantissa == 0 then
    if rightMantissa == 0 then
      zero fmt (leftSign && rightSign)
    else
      roundMagnitude fmt roundOffset rightSign rightMantissa rightScale
  else if rightMantissa == 0 then
    roundMagnitude fmt roundOffset leftSign leftMantissa leftScale
  else if leftScale ≤ rightScale then
    roundMagnitudes fmt roundOffset leftSign rightSign leftMantissa
      (rightMantissa <<< (rightScale - leftScale)) leftScale
  else
    roundMagnitudes fmt roundOffset leftSign rightSign
      (leftMantissa <<< (leftScale - rightScale)) rightMantissa rightScale

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteScaleAdd

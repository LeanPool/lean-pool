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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Product.Runtime

/-!
# Shared native signed-magnitude arithmetic

Binary interchange and posit arithmetic both decode finite values into a sign and an unsigned
significand. These one- and two-word operations combine aligned magnitudes, retaining the sign
of the larger magnitude on subtraction and choosing positive zero on exact cancellation.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
Add or subtract two unsigned magnitudes according to their independent signs.

Exact cancellation returns positive zero. Same-sign callers must establish separately that the
sum fits in `UInt64`; opposite-sign subtraction cannot overflow.
-/
@[inline] def addSignedMagnitudes
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt64) : Bool × UInt64 :=
  if leftNegative == rightNegative then
    (leftNegative, leftMagnitude + rightMagnitude)
  else if leftMagnitude == rightMagnitude then
    (false, 0)
  else if leftMagnitude < rightMagnitude then
    (rightNegative, rightMagnitude - leftMagnitude)
  else
    (leftNegative, leftMagnitude - rightMagnitude)

/--
Add or subtract two unsigned two-limb magnitudes according to their independent signs.

Exact cancellation returns positive zero. Same-sign addition discards the carry from `add128`,
so callers must establish that the sum fits in `UInt128`; opposite-sign subtraction cannot overflow.
-/
@[inline] def addSignedMagnitudes128
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt128) : Bool × UInt128 :=
  if leftNegative == rightNegative then
    (leftNegative, (add128 leftMagnitude rightMagnitude).value)
  else if leftMagnitude == rightMagnitude then
    (false, ⟨0, 0⟩)
  else if UInt128.less leftMagnitude rightMagnitude then
    (rightNegative, UInt128.sub rightMagnitude leftMagnitude)
  else
    (leftNegative, UInt128.sub leftMagnitude rightMagnitude)

end FloatLib.Numerics.FixedWord

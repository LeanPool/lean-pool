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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Runtime

/-!
# Two-word addition runtime

The two-word addition runtime combines the same-exponent kernel with a complete finite candidate
chain for every eligible layout. Correctness theorems are isolated in `Addition.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Try native same-sign addition of normal operands with the same exponent.

The two largest exponent fields are rejected so incrementing the accepted exponent always remains
finite. The sum of two `fracWidth + 1`-bit significands fits in the two-word accumulator.
-/
@[inline] def addNormalSameExponentOption {fmt : FloatFormat} (x y : Model fmt) : Option (Model
  fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let xSign := signBit fmt xWords.hi
  let ySign := signBit fmt yWords.hi
  if xSign != ySign || xExponent == 0 || expAllOnes fmt - 1 ≤ xExponent ||
      yExponent != xExponent then
    none
  else
    let xMantissa := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let yMantissa := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    let exact := FloatLib.Numerics.FixedWord.add128 xMantissa yMantissa
    let rounded := exact.value.roundShiftRightOneEven
    some <| packNormal fmt xSign (xExponent + 1) rounded

/--
Evaluate finite two-word addition.

The fixed-limb same-exponent kernel is attempted first. Every remaining finite case uses the
width-generic exact kernel; exceptional inputs are reported as `none` to the operation dispatcher.
The `@[specialize fmt]` annotation enables descriptor-dependent constants to be simplified at
closed-format call sites without requesting that callers inline this candidate chain.
-/
@[specialize fmt] def addFiniteOption {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  match addNormalSameExponentOption x y with
  | some sum => some sum
  | none => FiniteKernel.addRuntimeOption x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

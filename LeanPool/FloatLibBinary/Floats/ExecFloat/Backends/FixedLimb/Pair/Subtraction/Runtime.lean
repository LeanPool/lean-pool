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
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime

/-!
# Two-word subtraction runtime

The two-word subtraction runtime combines the equal-exponent kernel with a complete finite
candidate chain for every eligible layout. It reuses the pair-kernel storage layer; correctness
proofs are isolated in `Subtraction.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Try exact native subtraction of same-sign normal operands with the same exponent.

An accepted nonzero result remains normal. Exact cancellation returns positive zero; a nonzero
subnormal difference is left to the generic implementation.
-/
@[inline] def subNormalSameExponentOption {fmt : FloatFormat} (x y : Model fmt) : Option (Model
  fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let xSign := signBit fmt xWords.hi
  let ySign := signBit fmt yWords.hi
  if xSign != ySign || xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent != xExponent then
    none
  else
    let xMantissa := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let yMantissa := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    if xMantissa == yMantissa then
      some (Model.posZero fmt)
    else
      let xLess := FloatLib.Numerics.FixedWord.UInt128.less xMantissa yMantissa
      let difference :=
        if xLess then
          FloatLib.Numerics.FixedWord.UInt128.sub yMantissa xMantissa
        else
          FloatLib.Numerics.FixedWord.UInt128.sub xMantissa yMantissa
      let leading := FloatLib.Numerics.FixedWord.UInt128.log2 difference
      if xExponent.toNat + leading ≤ fmt.fracWidth then
        none
      else
        let normalized :=
          FloatLib.Numerics.FixedWord.UInt128.shiftLeft difference (fmt.fracWidth - leading)
        let resultExponent :=
          UInt64.ofNat (xExponent.toNat + leading - fmt.fracWidth)
        some <| packNormal fmt (if xLess then !xSign else xSign)
          resultExponent normalized

/--
Evaluate finite two-word subtraction.

The fixed-limb equal-exponent kernel is attempted first. Every remaining finite case uses generic
exact addition with a negated right operand; exceptional inputs remain visible to the dispatcher.
Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def subFiniteOption {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  match subNormalSameExponentOption x y with
  | some difference => some difference
  | none => FiniteKernel.addRuntimeOption x (neg y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

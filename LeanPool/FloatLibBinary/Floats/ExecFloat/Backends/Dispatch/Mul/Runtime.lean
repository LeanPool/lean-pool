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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Mul.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.TwoWordMul.Runtime

/-!
# Executable multiplication backends

The generic path computes exact finite products and owns the complete exceptional-value policy.
The dispatcher opportunistically uses native binary32 or binary64, fixed-pair limbs, and
parameterized one- or two-word kernels when their structural capabilities apply.

Every specialized routine is partial by design: a declined case is handled by the one exact
generic implementation. `Mul.Proof` establishes that successful fast paths and the baseline all
implement the same public specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace MulBackend

/--
Width-generic compiled multiplication.

Finite operands use the compact scale kernel; exceptional operands retain the public NaN and
infinity policy.
-/
def generic {fmt : FloatFormat}
    (x y : Model fmt) : Model fmt :=
  match FiniteKernel.mulRuntimeOption x y with
  | some product => product
  | none =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isZero y then
              invalidResult fmt
            else
              nativeOverflow fmt (signBit x != signBit y)
          else if isInf y then
            if isZero x then
              invalidResult fmt
            else
              nativeOverflow fmt (signBit x != signBit y)
          else
            invalidResult fmt

/--
Word-specialized compiled implementation of `mul`.

Each specialized kernel is selected by a structural capability and returns only a partial fast
result. Binary32 uses the checked narrow backend. Binary64 first tries the parameterized two-word
normal-product kernel, whose `64 x 64 -> 128` product and machine-word finishing stage suit its
53-bit significands, and falls back to its fixed multiword kernel. Eligible pair layouts use the
four-limb product kernel. Other conventional IEEE formats use
parameterized one- and two-word normal-product kernels. After the binary64 candidate chain is
exhausted, and on every other declined route,
`generic` supplies the result. The dispatcher is specialized on the descriptor, as described in
`Dispatch.Add.Runtime`.
-/
@[specialize fmt] def word {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    let y32 : NativeBinary32.Value := Eq.mp hcarrier y
    match NativeBinary32.mulFiniteImplOption x32 y32 with
    | some product => Eq.mpr hcarrier product
    | none => generic x y
  else if h64 : FloatFormat.IsBinary64 fmt then
    match NativeTwoWordMul.mulNormalOption x y with
    | some product => product
    | none =>
        let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
        let hcarrier := congrArg Model hfmt
        let x64 : NativeBinary64.Value := Eq.mp hcarrier x
        let y64 : NativeBinary64.Value := Eq.mp hcarrier y
        match NativeBinary64.mulNormalLimbOption x64 y64 with
        | some product => Eq.mpr hcarrier product
        | none => generic x y
  else if _hpair : NativePair.Eligible fmt then
    match NativePair.mulNormalLimbOption x y with
    | some product => product
    | none => generic x y
  else if _heligible : NativeSmallWordMul.Eligible fmt then
    let product := NativeSmallWordMul.mulNormalWord x y
    if product == NativeSmallWordMul.declineWord then
      generic x y
    else
      NativeSmallWord.ofWord product
  else if _htwoWord : NativeTwoWordMul.Eligible fmt then
    match NativeTwoWordMul.mulNormalOption x y with
    | some product => product
    | none => generic x y
  else
    generic x y

end MulBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

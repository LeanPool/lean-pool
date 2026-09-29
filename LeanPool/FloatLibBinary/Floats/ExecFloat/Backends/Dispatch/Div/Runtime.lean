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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Spec.Division
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Division.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Division.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Division.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Div.Runtime

/-!
# Executable division backends

The width-generic divider and fixed-width dispatcher live here. Their correctness theorems are
kept in `Div.Proof`.

The dispatcher selects native kernels by format capability. A selected kernel may decline when
its operand or intermediate bounds fail; the generic implementation then supplies the result,
including the descriptor's exceptional-value policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace DivBackend

/--
Width-generic compiled division.

Finite operands use the compact scale kernel; exceptional operands retain `Spec.divSpecial`.
-/
def generic {fmt : FloatFormat}
    (x y : Model fmt) : Model fmt :=
  match FiniteKernel.divRuntimeOption x y with
  | some quotient => quotient
  | none => Spec.divSpecial x y

/--
Compiled implementation of `div`.

Binary32 and binary64 finite operands use native-word decoding. Structurally eligible pair layouts
use the certified radix-`2^32` normal quotient kernel. Every other one-word IEEE layout uses
restoring division. Every declined or ineligible case enters the single exact width-generic
baseline here. The dispatcher is specialized on the descriptor, as described in
`Dispatch.Add.Runtime`.
-/
@[specialize fmt] def word {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    let y32 : NativeBinary32.Value := Eq.mp hcarrier y
    match NativeBinary32.divFiniteImplOption x32 y32 with
    | some quotient => Eq.mpr hcarrier quotient
    | none => generic x y
  else if h64 : FloatFormat.IsBinary64 fmt then
    let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    let hcarrier := congrArg Model hfmt
    let x64 : NativeBinary64.Value := Eq.mp hcarrier x
    let y64 : NativeBinary64.Value := Eq.mp hcarrier y
    match NativeBinary64.divFiniteFastImplOption x64 y64 with
    | some quotient => Eq.mpr hcarrier quotient
    | none => generic x y
  else if _hpair : NativePair.Eligible fmt then
    match NativePair.divNormalOption x y with
    | some quotient => quotient
    | none => generic x y
  else if _heligible : NativeSmallWord.StorageEligible fmt then
    match NativeSmallWordDiv.divNormalOption x y with
    | some quotient => quotient
    | none => generic x y
  else
    generic x y

end DivBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

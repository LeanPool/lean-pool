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
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Fma.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Fma.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Finite.Runtime

/-!
# Executable word-specialized fused multiply-add dispatch

Generic and word-specialized dispatchers compute fused multiply-add. Their refinement theorems
live in `FmaWord.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/--
Width-generic compiled FMA.

The exceptional-value dispatcher stays explicit, while the all-finite path decodes each operand
once and uses the compact finite kernel.
-/
def generic {fmt : FloatFormat}
    (x y z : Model fmt) : Model fmt :=
  match FiniteKernel.fmaRuntimeFlatOption x y z with
  | some result => result
  | none =>
      match chooseNaN3 x y z with
      | some nan => nan
      | none =>
          if isInf x || isInf y then
            if isZero x || isZero y then
              invalidResult fmt
            else
              let productSign := Bool.xor (signBit x) (signBit y)
              let productInfinity := nativeOverflow fmt productSign
              if isInf z then
                if signBit z != productSign then
                  invalidResult fmt
                else
                  productInfinity
              else
                productInfinity
          else if isInf z then
            z
          else
            invalidResult fmt

/--
Compiled implementation of `fma`.

Binary32 and binary64 finite operands use native-word decoding and still round only once. Other
eligible one-word IEEE formats use the reusable native-storage decoder. Declined and unsupported
cases follow the format-generic implementation. The dispatcher is specialized on the descriptor,
as described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def word {fmt : FloatFormat}
    (x y z : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    let y32 : NativeBinary32.Value := Eq.mp hcarrier y
    let z32 : NativeBinary32.Value := Eq.mp hcarrier z
    match NativeBinary32.fmaFiniteImplOption x32 y32 z32 with
    | some result => Eq.mpr hcarrier result
    | none => generic x y z
  else if h64 : FloatFormat.IsBinary64 fmt then
    let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    let hcarrier := congrArg Model hfmt
    let x64 : NativeBinary64.Value := Eq.mp hcarrier x
    let y64 : NativeBinary64.Value := Eq.mp hcarrier y
    let z64 : NativeBinary64.Value := Eq.mp hcarrier z
    match NativeBinary64.fmaFiniteFastImplOption x64 y64 z64 with
    | some result => Eq.mpr hcarrier result
    | none => generic x y z
  else if _heligible : NativeSmallWord.StorageEligible fmt then
    match NativeSmallWordFinite.fmaFiniteOption x y z with
    | some result => result
    | none => generic x y z
  else
    generic x y z

end FmaBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

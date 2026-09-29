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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Finite.Runtime

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Executable word-specialized square-root dispatch

Only executable square-root kernels and their format dispatcher live here. Correctness theorems
remain in `SqrtWord.Proof`, so runtime-only clients do not load the native refinement developments.

Selection is based on proved format and capacity conditions: binary32 and binary64 use their native
paths, suitable smaller formats use the shared word kernel, and the general implementation remains
available outside those envelopes. These are implementations of one operation contract, not
format-specific definitions of square root.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace SqrtBackend

/--
Width-generic compiled square root.

The outer dispatcher retains NaN payload, infinity, signed-zero, and negative-input policy.
Positive finite nonzero values use the compact decoder and checked model square root. Their
classification proof makes the finite decoder total, so this path has no exceptional fallback.
-/
def generic {fmt : FloatFormat}
    (x : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN1 x) fun hnan =>
    let hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
    if hxInf : isInf x then
      if signBit x then invalidResult fmt else nativeOverflow fmt false
    else if hxZero : isZero x then
      x
    else if hxSign : signBit x then
      invalidResult fmt
    else
      let hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN
          (Bool.eq_false_of_not_eq_true hxInf)
      FiniteSqrt.sqrtPositiveRuntime x hfinite
        (Bool.eq_false_of_not_eq_true hxZero)
        (Bool.eq_false_of_not_eq_true hxSign)

/--
One-word square root with native finite-field decoding.

The outer cases intentionally match `SqrtBackend.generic`; only the positive finite decoder is
replaced. Eligibility and classification evidence are erased, leaving the native field kernel in
compiled code without an impossible fallback.
-/
@[inline] def smallWord {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN1 x) fun hnan =>
    let hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
    if hxInf : isInf x then
      if signBit x then invalidResult fmt else nativeOverflow fmt false
    else if hxZero : isZero x then
      x
    else if hxSign : signBit x then
      invalidResult fmt
    else
      let hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN
          (Bool.eq_false_of_not_eq_true hxInf)
      NativeSmallWordFinite.sqrtPositive heligible x hfinite
        (Bool.eq_false_of_not_eq_true hxZero)
        (Bool.eq_false_of_not_eq_true hxSign)

/--
Word-specialized compiled implementation of `sqrt`.

Binary32 uses the checked direct `UInt32`/`UInt64` backend. Binary64 uses the two-limb restoring
kernel. Other eligible one-word IEEE formats use native storage decoding before entering the
shared square-root kernel. Remaining formats use `SqrtBackend.generic`. The dispatcher is
specialized on the descriptor, as described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def word {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    let hcarrier := congrArg Model hfmt
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    Eq.mpr hcarrier (NativeBinary32.sqrt x32)
  else if h64 : FloatFormat.IsBinary64 fmt then
    let hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
    let hcarrier := congrArg Model hfmt
    let x64 : NativeBinary64.Value := Eq.mp hcarrier x
    Eq.mpr hcarrier (NativeBinary64.sqrt x64)
  else if heligible : NativeSmallWord.StorageEligible fmt then
    smallWord heligible x
  else
    generic x

end SqrtBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

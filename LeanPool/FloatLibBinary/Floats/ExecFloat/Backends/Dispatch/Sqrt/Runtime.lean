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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.SqrtWord.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Sqrt.Runtime

/-!
# Executable square-root dispatch

The dispatcher adds the certified pair-layout route to the smaller word-specialized kernels
without importing their refinement proofs. It alone selects the exact word baseline when the
partial pair kernel declines.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace SqrtBackend

/--
Use the fixed-pair square-root kernel when eligible, otherwise use the word dispatcher.

The partial pair result has one fallback call to `word`. The fixed-format guard lets
specialization discard the pair probe for binary32 and binary64; neither is pair-eligible.
-/
@[inline] def dispatch {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  let fast : Option (Model fmt) :=
    if FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt then none
    else if _hpair : NativePair.Eligible fmt then NativePair.sqrtNormalOption x
    else none
  match fast with
  | some result => result
  | none => word x

end SqrtBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

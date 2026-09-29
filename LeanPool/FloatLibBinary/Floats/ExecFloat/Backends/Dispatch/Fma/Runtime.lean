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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.FmaWord.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Runtime

/-!
# Executable fused multiply-add dispatch

The dispatcher adds the fixed-limb pair-layout route to the smaller word-specialized kernels
without importing their refinement proofs. The pair route contains a complete finite candidate
chain; the dispatcher handles only exceptional inputs after that chain returns `none`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/-- Use the fixed-limb FMA when eligible, otherwise use the word dispatcher. -/
@[inline] def dispatch {fmt : FloatFormat}
    (x y z : Model fmt) : Model fmt :=
  -- Keep one fallback call to `word`. The fixed-format guard lets specialization discard
  -- the pair probe for binary32 and binary64, neither of which is pair-eligible.
  let fast : Option (Model fmt) :=
    if FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt then none
    else if _hpair : NativePair.Eligible fmt then NativePair.fmaFiniteOption x y z
    else none
  match fast with
  | some result => result
  | none => word x y z

end FmaBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

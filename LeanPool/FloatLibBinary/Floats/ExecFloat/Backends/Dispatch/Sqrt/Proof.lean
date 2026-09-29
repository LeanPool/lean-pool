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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.SqrtWord.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Sqrt.Proof

/-!
# Correctness of square-root dispatch

`dispatch_eq_spec` combines the word and fixed-pair refinements to identify the complete
dispatcher with `Spec.sqrt`, including exceptional inputs. Runtime clients can import
`Sqrt.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace SqrtBackend

/-- Final structurally selected dispatch preserves square root. -/
theorem dispatch_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    dispatch x = Spec.sqrt x := by
  by_cases hfixed : FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt
  · simp [dispatch, hfixed, word_eq_spec]
  by_cases hpair : NativePair.Eligible fmt
  · cases hfast : NativePair.sqrtNormalOption x with
    | none =>
        simp [dispatch, hfixed, hpair, hfast, word_eq_spec]
    | some result =>
        have hrefines := NativePair.sqrtNormal_refines hpair x result hfast
        simp [dispatch, hfixed, hpair, hfast, hrefines]
  · simp [dispatch, hfixed, hpair, word_eq_spec]

end SqrtBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

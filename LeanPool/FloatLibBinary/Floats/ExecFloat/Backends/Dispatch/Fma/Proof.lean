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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Fma.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.FmaWord.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Fma.Proof

/-!
# Correctness of fused multiply-add dispatch

`dispatch_eq_spec` combines the word and fixed-limb refinements to identify the complete
dispatcher with `Spec.fma`. For finite inputs, this contract rounds the exact product-plus-addend
once. Runtime clients can import `Fma.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/-- Final structurally selected dispatch preserves fused multiply-add. -/
theorem dispatch_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    dispatch x y z = Spec.fma x y z := by
  by_cases hfixed : FloatFormat.IsBinary32 fmt ∨ FloatFormat.IsBinary64 fmt
  · simp [dispatch, hfixed, word_eq_spec]
  by_cases hpair : NativePair.Eligible fmt
  · cases hfinite : FiniteKernel.fmaOption x y z with
    | none =>
        simp [dispatch, hfixed, hpair, NativePair.fmaFinite_eq hpair, hfinite, word_eq_spec]
    | some result =>
        have hresult : result = Spec.fma x y z := by
          calc
            result = generic x y z := by
              simp [generic, FiniteKernel.fmaRuntimeFlat_eq,
                FiniteKernel.fmaRuntime_eq, hfinite]
            _ = Spec.fma x y z := generic_eq_spec x y z
        simp [dispatch, hfixed, hpair, NativePair.fmaFinite_eq hpair, hfinite, hresult]
  · simp [dispatch, hfixed, hpair, word_eq_spec]

end FmaBackend
end Model
end FloatLib.Floats.Formats.BinaryInterchange

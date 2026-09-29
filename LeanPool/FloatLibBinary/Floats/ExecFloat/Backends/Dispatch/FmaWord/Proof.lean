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
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Spec.Dyadic
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Agreement
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Fma.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Classification
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Fma.Proof
/-!
# Correctness of word-specialized fused multiply-add dispatch

Fused multiply-add forms the exact product-plus-addend before one rounding step. The refinements
here establish that contract for the binary32, binary64, and reusable small-word kernels.

Accepted kernel results and the generic fallback all agree with `Spec.fma`, including its
exceptional-value policy. Runtime clients can import `FmaWord.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace FmaBackend

/-- Compact generic FMA preserves the public exact-dyadic operation. -/
theorem generic_eq_spec {fmt : FloatFormat}
    (x y z : Model fmt) :
    generic x y z = Spec.fma x y z := by
  unfold generic Spec.fma
  rw [FiniteKernel.fmaRuntimeFlat_eq, FiniteKernel.fmaRuntime_eq]
  rw [FiniteKernel.fma_eq_spec]
  cases hx : toDyadicOption x with
  | none =>
      simp
      rfl
  | some dx =>
    cases hy : toDyadicOption y with
    | none =>
        simp
        rfl
    | some dy =>
      cases hz : toDyadicOption z with
      | none =>
          simp
          rfl
      | some dz =>
        have hxNaN := isNaN_eq_false_of_toDyadicOption_some hx
        have hyNaN := isNaN_eq_false_of_toDyadicOption_some hy
        have hzNaN := isNaN_eq_false_of_toDyadicOption_some hz
        have hxSNaN := isSNaN_eq_false_of_toDyadicOption_some hx
        have hySNaN := isSNaN_eq_false_of_toDyadicOption_some hy
        have hzSNaN := isSNaN_eq_false_of_toDyadicOption_some hz
        have hxInf := isInf_eq_false_of_toDyadicOption_some hx
        have hyInf := isInf_eq_false_of_toDyadicOption_some hy
        have hzInf := isInf_eq_false_of_toDyadicOption_some hz
        simp [chooseNaN3, hxNaN, hyNaN, hzNaN, hxSNaN, hySNaN,
          hzSNaN, hxInf, hyInf, hzInf]

private theorem generic_eq_of_finite_some {fmt : FloatFormat}
    (x y z result : Model fmt)
    (hfinite : FiniteKernel.fmaOption x y z = some result) :
    generic x y z = result := by
  simp [generic, FiniteKernel.fmaRuntimeFlat_eq,
    FiniteKernel.fmaRuntime_eq, hfinite]

/--
The binary32 kernel and the generic finite kernel expose the same exact-dyadic contract.

Keeping this agreement as a named lemma avoids repeating the exceptional-value case split in the
dispatcher proof. It also keeps the binary32 and binary64 dispatch arguments structurally alike.
-/
private theorem binary32_fmaFiniteImpl_eq_kernel
    (x y z : Model FloatFormat.binary32) :
    NativeBinary32.fmaFiniteImplOption x y z = FiniteKernel.fmaOption x y z := by
  rw [NativeBinary32.fmaFiniteImpl_eq, NativeBinary32.fmaFinite_eq,
    FiniteKernel.fma_eq_spec]
  rfl

/-- Native fixed-format and reusable one-word dispatch preserves fused multiply-add. -/
private theorem spec_fma_eq_word :
    @Spec.fma = @word := by
  funext fmt x y z
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    cases hnative : NativeBinary32.fmaFiniteImplOption x y z with
    | none =>
        simp [word, hnative, generic_eq_spec]
    | some result =>
        have hfinite :
            FiniteKernel.fmaOption x y z = some result := by
          rw [← binary32_fmaFiniteImpl_eq_kernel]
          exact hnative
        have hresult : result = Spec.fma x y z := by
          calc
            result = generic x y z :=
              (generic_eq_of_finite_some
                x y z result hfinite).symm
            _ = Spec.fma x y z := generic_eq_spec x y z
        simp [word, hnative, hresult]
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      cases hnative : NativeBinary64.fmaFiniteFastImplOption x y z with
      | none =>
          simp [word, h32, hnative, generic_eq_spec]
      | some result =>
          have hfinite :
              FiniteKernel.fmaOption x y z = some result := by
            rw [← NativeBinary64.fmaFiniteFastImpl_eq]
            exact hnative
          have hresult : result = Spec.fma x y z := by
            calc
              result = generic x y z :=
                (generic_eq_of_finite_some
                  x y z result hfinite).symm
              _ = Spec.fma x y z := generic_eq_spec x y z
          simp [word, h32, hnative, hresult]
    · by_cases heligible : NativeSmallWord.StorageEligible fmt
      · cases hnative : NativeSmallWordFinite.fmaFiniteOption x y z with
        | none =>
            simp [word, h32, h64, heligible, hnative,
              generic_eq_spec]
        | some result =>
            have hfinite :
                FiniteKernel.fmaOption x y z = some result := by
              rw [← NativeSmallWordFinite.fmaFinite_eq heligible]
              exact hnative
            have hresult : result = Spec.fma x y z := by
              calc
                result = generic x y z :=
                  (generic_eq_of_finite_some
                    x y z result hfinite).symm
                _ = Spec.fma x y z := generic_eq_spec x y z
            simp [word, h32, h64, heligible, hnative, hresult]
      · simp [word, generic_eq_spec, h32, h64, heligible]

/-- Native-word or generic fused multiply-add preserves the logical operation. -/
theorem word_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    word x y z = Spec.fma x y z :=
  (congrFun (congrFun (congrFun (congrFun spec_fma_eq_word fmt) x) y) z).symm

end FmaBackend

end Model

end FloatLib.Floats.Formats.BinaryInterchange

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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Storage

/-!
# Standard and low-precision binary formats

Named `FloatFormat` descriptors cover IEEE interchange formats, common machine-learning formats,
and a 256-bit IEEE-style layout. They are all values of the same `FloatFormat` structure used by
custom formats; no operation or theorem is duplicated for a named encoding.

## References

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 3.6,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* D. Kalamkar et al., *A Study of BFLOAT16 for Deep Learning Training*, 2019,
  <https://arxiv.org/abs/1905.12322>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

/--
Structural equality of two binary-interchange layouts.

Backend capabilities should depend on these computational fields rather than descriptor names.
The proof fields in `FloatFormat` are propositions, so matching the stored layout recovers full
descriptor equality.
-/
abbrev SameLayout (left right : FloatFormat) : Prop :=
  left.expWidth = right.expWidth ∧
    left.fracWidth = right.fracWidth ∧
      left.exponentBias = right.exponentBias ∧
        left.encoding = right.encoding

/-- Two descriptors with the same stored layout are equal. -/
theorem eq_of_sameLayout {left right : FloatFormat} (h : SameLayout left right) :
    left = right := by
  rcases h with ⟨hexponent, hfraction, hbias, hencoding⟩
  cases left with
  | mk leftExp leftExpGeTwo leftFrac leftFracPos leftBias leftEncoding _ _ =>
      cases right with
      | mk rightExp rightExpGeTwo rightFrac rightFracPos rightBias rightEncoding _ _ =>
          dsimp only at hexponent hfraction hbias hencoding
          subst rightExp
          subst rightFrac
          subst rightBias
          subst rightEncoding
          rfl

/-- IEEE binary16, commonly called half precision. -/
@[inline] def binary16 : FloatFormat where
  expWidth := 5
  fracWidth := 10
  exponentBias := 15
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/-- Bfloat16, with the normal exponent range of binary32 and eight significand bits. -/
@[inline] def bfloat16 : FloatFormat where
  expWidth := 8
  fracWidth := 7
  exponentBias := 127
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/-- IEEE binary32, commonly called single precision. -/
@[inline] def binary32 : FloatFormat where
  expWidth := 8
  fracWidth := 23
  exponentBias := 127
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/-- IEEE binary64, commonly called double precision. -/
@[inline] def binary64 : FloatFormat where
  expWidth := 11
  fracWidth := 52
  exponentBias := 1023
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/-- Binary16 uses the IEEE exceptional-value encoding. -/
@[simp] theorem isIEEE_binary16 : binary16.isIEEE = true := by decide

/-- Bfloat16 uses the IEEE exceptional-value encoding. -/
@[simp] theorem isIEEE_bfloat16 : bfloat16.isIEEE = true := by decide

/-- Binary32 uses the IEEE exceptional-value encoding. -/
@[simp] theorem isIEEE_binary32 : binary32.isIEEE = true := by decide

/-- Binary64 uses the IEEE exceptional-value encoding. -/
@[simp] theorem isIEEE_binary64 : binary64.isIEEE = true := by decide

/--
Structural capability for the binary32 native backend.

The theorem below recovers full descriptor equality before any carrier cast.
-/
abbrev IsBinary32 (fmt : FloatFormat) : Prop :=
  SameLayout fmt binary32

/-- A format with the binary32 storage layout is binary32. -/
theorem eq_binary32_of_isBinary32 {fmt : FloatFormat} (h : IsBinary32 fmt) :
    fmt = binary32 :=
  eq_of_sameLayout h

/-- Structural capability for the binary64 native-storage backend. -/
abbrev IsBinary64 (fmt : FloatFormat) : Prop :=
  SameLayout fmt binary64

/-- A format with the binary64 storage layout is binary64. -/
theorem eq_binary64_of_isBinary64 {fmt : FloatFormat} (h : IsBinary64 fmt) :
    fmt = binary64 :=
  eq_of_sameLayout h

/-- The named binary32 descriptor satisfies its data-only backend predicate. -/
@[simp] theorem isBinary32_binary32 : IsBinary32 binary32 := by
  decide

/-- Binary32 does not satisfy the binary64 backend predicate. -/
@[simp] theorem not_isBinary64_binary32 : ¬IsBinary64 binary32 := by
  decide

/-- Binary64 does not satisfy the binary32 backend predicate. -/
@[simp] theorem not_isBinary32_binary64 : ¬IsBinary32 binary64 := by
  decide

/-- The named binary64 descriptor satisfies its data-only backend predicate. -/
@[simp] theorem isBinary64_binary64 : IsBinary64 binary64 := by
  decide

/-- IEEE binary128, commonly called quadruple precision. -/
@[inline] def binary128 : FloatFormat where
  expWidth := 15
  fracWidth := 112
  exponentBias := 16383
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/--
A named 256-bit IEEE-style layout with a 237-bit significand.

It uses 19 exponent bits and 236 stored fraction bits. Arbitrary wider layouts remain available
by constructing `FloatFormat` directly.
-/
@[inline] def binary256 : FloatFormat where
  expWidth := 19
  fracWidth := 236
  exponentBias := 262143
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/-- Binary128 uses the IEEE exceptional-value encoding. -/
@[simp] theorem isIEEE_binary128 : binary128.isIEEE = true := by decide

/-- The binary256 profile uses the IEEE-style exceptional-value encoding. -/
@[simp] theorem isIEEE_binary256 : binary256.isIEEE = true := by decide

/-! ### Low-precision and finite-only formats -/

/-- OCP/ONNX E5M2: bias 15 with IEEE-style infinities and NaNs. -/
@[inline] def e5m2 : FloatFormat := .ieee 5 2

/-- Compact semantic TensorFloat-32 layout with eight exponent and ten fraction bits. -/
@[inline] def tf32 : FloatFormat := .ieee 8 10

/-- OCP/ONNX E4M3FN: bias 7, no infinity, maximum fraction at maximum exponent is NaN. -/
@[inline] def e4m3fn : FloatFormat := .finiteMaxNaN 4 3

/-- ONNX E4M3FNUZ: bias 8, one zero, and the negative-zero word as the sole NaN. -/
@[inline] def e4m3fnuz : FloatFormat := .finiteUnsignedZero 4 3

/-- ONNX E5M2FNUZ: bias 16, one zero, and the negative-zero word as the sole NaN. -/
@[inline] def e5m2fnuz : FloatFormat := .finiteUnsignedZero 5 2

/-- OCP MX FP4 E2M1: bias 1 with every stored word finite. -/
@[inline] def e2m1 : FloatFormat := .finite 2 1

/-- OCP MX FP6 E2M3 element format with every stored word finite. -/
@[inline] def e2m3 : FloatFormat := .finite 2 3

/-- OCP MX FP6 E3M2 element format with every stored word finite. -/
@[inline] def e3m2 : FloatFormat := .finite 3 2

end FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

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

public import Init.Data.Float.Model.Format

/-!
# Binary interchange format definitions

`FloatFormat` completely describes a binary storage format: its sign/exponent/fraction layout,
exponent bias, and exceptional-value encoding. There is no global precision ceiling. IEEE,
finite-only, and FNUZ formats are values of the same structure, and so is a custom format, which
pairs one of the four exceptional-value encodings with a validated exponent bias.

Lean's generic `Float.Model.Format` represents the IEEE interpretation of a layout. The
`toModel` conversion below therefore exposes that logical view only for the layout fields; the
policy-aware executable semantics use `exponentBias` and `encoding` directly.

References:

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

namespace FloatFormat

/-- Assignment of exceptional values within a sign/exponent/fraction binary format. -/
inductive Encoding where
  /-- All-ones exponent: zero fraction is infinity, nonzero fraction is NaN. -/
  | ieee
  /-- No infinity; the all-ones exponent and all-ones fraction pattern is NaN. -/
  | finiteMaxNaN
  /-- No infinity or negative zero; the negative-zero bit pattern is the sole NaN. -/
  | finiteUnsignedZero
  /-- Every nonzero bit pattern is finite; both signs of zero remain representable. -/
  | finite
  deriving Repr

namespace Encoding

/--
Executable equality of encodings by case split.

The explicit inlined test lets the compiler reduce comparisons of known constructors. The
`DecidableEq` instance uses this test so descriptor eligibility checks can specialize with it.
-/
@[inline] protected def beq : Encoding → Encoding → Bool
  | .ieee, .ieee => true
  | .finiteMaxNaN, .finiteMaxNaN => true
  | .finiteUnsignedZero, .finiteUnsignedZero => true
  | .finite, .finite => true
  | _, _ => false

/-- `Encoding.beq` decides propositional equality of encodings. -/
theorem beq_eq_true_iff (left right : Encoding) :
    Encoding.beq left right = true ↔ left = right := by
  cases left <;> cases right <;> simp [Encoding.beq]

end Encoding

/-- Equality of encodings is decidable; the instance is inlined so literal comparisons fold. -/
@[inline] instance instDecidableEqEncoding : DecidableEq Encoding := fun left right =>
  decidable_of_iff (Encoding.beq left right = true) (Encoding.beq_eq_true_iff left right)

/-- Largest encoded exponent that is finite at fraction zero. -/
@[inline] def Encoding.maxFiniteExponent (encoding : Encoding) (expWidth : Nat) : Nat :=
  match encoding with
  | .ieee => 2 ^ expWidth - 2
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => 2 ^ expWidth - 1

end FloatFormat

/-- Complete binary storage, exponent-bias, and exceptional-value format descriptor. -/
structure FloatFormat where
  /-- Width of the biased exponent field. -/
  expWidth : Nat
  /--
  At least two exponent bits are needed to separate zero/subnormal encodings, finite normal
  exponents, and the all-ones infinity/NaN class.
  -/
  expWidth_ge_two : 2 ≤ expWidth := by decide
  /-- Width of the fraction (significand without the implicit integer bit). -/
  fracWidth : Nat
  /-- An interchange format has at least one explicit fraction bit. -/
  fracWidth_pos : 0 < fracWidth := by decide
  /-- Bias subtracted from every nonzero encoded exponent. -/
  exponentBias : Nat
  /-- Interpretation of infinity, NaN, and zero bit patterns. -/
  encoding : FloatFormat.Encoding
  /-- A positive bias makes `exponentBias` the normal encoding of one. -/
  exponentBias_pos : 0 < exponentBias
  /-- The normal encoding of one is finite and fits in the exponent field. -/
  exponentBias_le_maxFinite :
    exponentBias ≤ encoding.maxFiniteExponent expWidth
  deriving DecidableEq, Repr

namespace FloatFormat

/-! ## Format construction -/

/-- The conventional IEEE exponent bias determined by the exponent width. -/
@[inline] def ieeeBias (expWidth : Nat) : Nat :=
  (2 ^ (expWidth - 1)) - 1

/--
Default exponent bias for a configured encoding.

IEEE, finite-max-NaN, and signed-zero finite formats use the conventional IEEE bias. The
finite-unsigned-zero encoding shifts the bias by one, matching its reuse of negative zero as NaN.
Callers can still supply any other validated bias through `FloatFormat.custom`.
-/
@[inline] def Encoding.defaultBias (encoding : Encoding) (expWidth : Nat) : Nat :=
  match encoding with
  | .finiteUnsignedZero => ieeeBias expWidth + 1
  | .ieee | .finiteMaxNaN | .finite => ieeeBias expWidth

/-- The conventional IEEE bias is positive when the exponent field has at least two bits. -/
theorem ieeeBias_pos (expWidth : Nat) (h : 2 ≤ expWidth) :
    0 < ieeeBias expWidth := by
  have hindex : 1 ≤ expWidth - 1 := Nat.le_sub_of_add_le h
  have hpow : 2 ≤ 2 ^ (expWidth - 1) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hindex
  unfold ieeeBias
  omega

/-- The conventional IEEE bias fits below the largest finite IEEE exponent encoding. -/
theorem ieeeBias_le_maxFiniteExponent (expWidth : Nat) (h : 2 ≤ expWidth) :
    ieeeBias expWidth ≤ Encoding.maxFiniteExponent .ieee expWidth := by
  have hwidthPos : 0 < expWidth := by omega
  have hindex : expWidth - 1 < expWidth := Nat.sub_lt hwidthPos (by decide)
  have hpow : 2 ^ (expWidth - 1) < 2 ^ expWidth :=
    Nat.pow_lt_pow_right (by decide) hindex
  change 2 ^ (expWidth - 1) - 1 ≤ 2 ^ expWidth - 2
  omega

/-- The conventional IEEE bias fits below the largest finite-only exponent encoding. -/
theorem ieeeBias_le_finiteMaxExponent (expWidth : Nat) (h : 2 ≤ expWidth) :
    ieeeBias expWidth ≤ Encoding.maxFiniteExponent .finite expWidth := by
  have hwidthPos : 0 < expWidth := by omega
  have hindex : expWidth - 1 < expWidth := Nat.sub_lt hwidthPos (by decide)
  have hpow : 2 ^ (expWidth - 1) < 2 ^ expWidth :=
    Nat.pow_lt_pow_right (by decide) hindex
  change 2 ^ (expWidth - 1) - 1 ≤ 2 ^ expWidth - 1
  omega

/-- The shifted FNUZ bias fits below the largest finite exponent encoding. -/
theorem finiteUnsignedBias_le_maxFiniteExponent
    (expWidth : Nat) (h : 2 ≤ expWidth) :
    ieeeBias expWidth + 1 ≤
      Encoding.maxFiniteExponent .finiteUnsignedZero expWidth := by
  have hwidthPos : 0 < expWidth := by omega
  have hindex : expWidth - 1 < expWidth := Nat.sub_lt hwidthPos (by decide)
  have hpow : 2 ^ (expWidth - 1) < 2 ^ expWidth :=
    Nat.pow_lt_pow_right (by decide) hindex
  have hbase : 0 < 2 ^ (expWidth - 1) := Nat.two_pow_pos _
  change (2 ^ (expWidth - 1) - 1) + 1 ≤ 2 ^ expWidth - 1
  omega

/--
Construct a validated custom binary format.

For literal widths and biases, Lean discharges the four side conditions with `by decide`.
-/
@[inline] def custom (expWidth fracWidth exponentBias : Nat) (encoding : Encoding)
    (expWidth_ge_two : 2 ≤ expWidth := by decide)
    (fracWidth_pos : 0 < fracWidth := by decide)
    (exponentBias_pos : 0 < exponentBias := by decide)
    (exponentBias_le_maxFinite :
      exponentBias ≤ encoding.maxFiniteExponent expWidth := by decide) : FloatFormat where
  expWidth := expWidth
  fracWidth := fracWidth
  exponentBias := exponentBias
  encoding := encoding
  expWidth_ge_two := expWidth_ge_two
  fracWidth_pos := fracWidth_pos
  exponentBias_pos := exponentBias_pos
  exponentBias_le_maxFinite := exponentBias_le_maxFinite

/-- Give an arbitrary layout its ordinary IEEE bias and exceptional-value interpretation. -/
@[inline] def ieee (expWidth fracWidth : Nat)
    (expWidth_ge_two : 2 ≤ expWidth := by decide)
    (fracWidth_pos : 0 < fracWidth := by decide) : FloatFormat where
  expWidth := expWidth
  fracWidth := fracWidth
  expWidth_ge_two := expWidth_ge_two
  fracWidth_pos := fracWidth_pos
  exponentBias := ieeeBias expWidth
  encoding := .ieee
  exponentBias_pos := ieeeBias_pos expWidth expWidth_ge_two
  exponentBias_le_maxFinite :=
    ieeeBias_le_maxFiniteExponent expWidth expWidth_ge_two

/-- OCP E4M3-style format with no infinity and one maximum-magnitude NaN per sign. -/
@[inline] def finiteMaxNaN (expWidth fracWidth : Nat)
    (expWidth_ge_two : 2 ≤ expWidth := by decide)
    (fracWidth_pos : 0 < fracWidth := by decide) : FloatFormat where
  expWidth := expWidth
  fracWidth := fracWidth
  expWidth_ge_two := expWidth_ge_two
  fracWidth_pos := fracWidth_pos
  exponentBias := ieeeBias expWidth
  encoding := .finiteMaxNaN
  exponentBias_pos := ieeeBias_pos expWidth expWidth_ge_two
  exponentBias_le_maxFinite :=
    ieeeBias_le_finiteMaxExponent expWidth expWidth_ge_two

/-- FNUZ format with bias one above the IEEE bias and negative zero reused as NaN. -/
@[inline] def finiteUnsignedZero (expWidth fracWidth : Nat)
    (expWidth_ge_two : 2 ≤ expWidth := by decide)
    (fracWidth_pos : 0 < fracWidth := by decide) : FloatFormat where
  expWidth := expWidth
  fracWidth := fracWidth
  expWidth_ge_two := expWidth_ge_two
  fracWidth_pos := fracWidth_pos
  exponentBias := ieeeBias expWidth + 1
  encoding := .finiteUnsignedZero
  exponentBias_pos := Nat.zero_lt_succ _
  exponentBias_le_maxFinite :=
    finiteUnsignedBias_le_maxFiniteExponent expWidth expWidth_ge_two

/-- Finite-only binary format in which no bit pattern denotes infinity or NaN. -/
@[inline] def finite (expWidth fracWidth : Nat)
    (expWidth_ge_two : 2 ≤ expWidth := by decide)
    (fracWidth_pos : 0 < fracWidth := by decide) : FloatFormat where
  expWidth := expWidth
  fracWidth := fracWidth
  expWidth_ge_two := expWidth_ge_two
  fracWidth_pos := fracWidth_pos
  exponentBias := ieeeBias expWidth
  encoding := .finite
  exponentBias_pos := ieeeBias_pos expWidth expWidth_ge_two
  exponentBias_le_maxFinite :=
    ieeeBias_le_finiteMaxExponent expWidth expWidth_ge_two

/-- Total storage width: sign + exponent + fraction. -/
@[inline] def bitWidth (fmt : FloatFormat) : Nat :=
  1 + fmt.expWidth + fmt.fracWidth

/-- The corresponding format used by Lean's logical floating-point model. -/
@[inline] def toModel (fmt : FloatFormat) : Float.Model.Format where
  mantissaBitsWithoutImplicit := fmt.fracWidth
  exponentBits := fmt.expWidth
  hm := fmt.fracWidth_pos
  he := fmt.expWidth_ge_two

/-- The declared exponent bias fits in the stored exponent field. -/
theorem exponentBias_lt_two_pow (fmt : FloatFormat) :
    fmt.exponentBias < 2 ^ fmt.expWidth := by
  have hbound := fmt.exponentBias_le_maxFinite
  have hpow : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
  cases hencoding : fmt.encoding <;>
    simp only [hencoding, Encoding.maxFiniteExponent] at hbound <;>
    omega

/--
Recover an executable IEEE format descriptor from Lean's logical format descriptor.

Both descriptors require at least two exponent bits; `fmt.he` supplies the explicit width proof.
The conversion assigns the conventional IEEE bias and exceptional-value interpretation.
-/
@[inline] def ofModel (fmt : Float.Model.Format) (h : 2 ≤ fmt.exponentBits) : FloatFormat where
  expWidth := fmt.exponentBits
  fracWidth := fmt.mantissaBitsWithoutImplicit
  expWidth_ge_two := h
  fracWidth_pos := fmt.hm
  exponentBias := ieeeBias fmt.exponentBits
  encoding := .ieee
  exponentBias_pos := ieeeBias_pos fmt.exponentBits h
  exponentBias_le_maxFinite :=
    ieeeBias_le_maxFiniteExponent fmt.exponentBits h

/-- Converting a Lean logical format to an executable descriptor and back is exact. -/
@[simp] theorem toModel_ofModel (fmt : Float.Model.Format) (h : 2 ≤ fmt.exponentBits) :
    toModel (ofModel fmt h) = fmt := by
  rfl

/--
Converting through Lean's logical model retains the widths and produces the corresponding
conventional IEEE descriptor.
-/
@[simp] theorem ofModel_toModel (fmt : FloatFormat) :
    ofModel (toModel fmt) fmt.expWidth_ge_two =
      ieee fmt.expWidth fmt.fracWidth fmt.expWidth_ge_two fmt.fracWidth_pos := by
  cases fmt
  rfl

/-- Lean's logical model and the executable descriptor assign the same total storage width. -/
@[simp] theorem toModel_numBits (fmt : FloatFormat) :
    (toModel fmt).numBits = fmt.bitWidth := by
  rfl

/-- Raw storage has precisely the width prescribed by the format. -/
abbrev ExecWord (fmt : FloatFormat) := BitVec fmt.bitWidth

end FloatFormat

end FloatLib.Floats.Formats.BinaryInterchange

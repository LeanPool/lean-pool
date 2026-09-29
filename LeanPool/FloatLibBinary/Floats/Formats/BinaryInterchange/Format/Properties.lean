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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Definition

/-!
# Derived binary interchange format properties

`FloatFormat` stores the choices that vary between binary interchange families:
exponent and fraction widths, bias, and exceptional-value encoding. This module derives the
capabilities, masks, and exponent bounds used everywhere else.

Keeping these formulas descriptor-driven is what makes FP8 variants, binary16/32/64/128, custom
biases, and finite-only encodings instances of one development. Format-specific kernels may
specialize the results, but they do not redefine the layout semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace FloatFormat

/--
Conventional IEEE exponent bias `2^(expWidth-1) - 1`.

This layout-derived quantity can differ from `fmt.exponentBias` for a custom or FNUZ descriptor.
The `FloatFormat` invariant guarantees `expWidth ≥ 2`.
-/
@[inline] def bias (fmt : FloatFormat) : Nat :=
  (2 ^ (fmt.expWidth - 1)) - 1

/-- The layout-derived conventional bias is positive for every binary descriptor. -/
theorem bias_pos (fmt : FloatFormat) : 0 < fmt.bias :=
  ieeeBias_pos fmt.expWidth fmt.expWidth_ge_two

/-- The exponent field range in terms of the conventional bias: `2 ^ expWidth = 2 * bias + 2`. -/
theorem two_pow_expWidth_eq_two_mul_bias_add_two (fmt : FloatFormat) :
    2 ^ fmt.expWidth = 2 * fmt.bias + 2 := by
  have hpow : 2 ^ fmt.expWidth = 2 ^ (fmt.expWidth - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    have := fmt.expWidth_ge_two
    omega
  have hpos : 0 < 2 ^ (fmt.expWidth - 1) := Nat.two_pow_pos _
  unfold bias
  omega

/-- The conventional bias always fits in the exponent field that defines it. -/
theorem bias_lt_pow_expWidth (fmt : FloatFormat) :
    fmt.bias < 2 ^ fmt.expWidth := by
  rw [two_pow_expWidth_eq_two_mul_bias_add_two]
  omega

/-- Whether this format contains signed infinities. -/
@[inline] def supportsInfinity (fmt : FloatFormat) : Bool :=
  fmt.encoding == .ieee

/-- Whether this format reserves at least one NaN pattern. -/
@[inline] def supportsNaN (fmt : FloatFormat) : Bool :=
  fmt.encoding != .finite

/-- Whether zero has distinct positive and negative encodings. -/
@[inline] def supportsSignedZero (fmt : FloatFormat) : Bool :=
  fmt.encoding != .finiteUnsignedZero

/--
Whether the descriptor has the conventional IEEE bias and exceptional-value encoding.

Custom widths can satisfy this predicate as well as the named IEEE 754 layouts.
-/
@[inline] def isIEEE (fmt : FloatFormat) : Bool :=
  fmt.encoding == .ieee && fmt.exponentBias == fmt.bias

/-- Every descriptor constructed by `ieee` is recognized as conventionally IEEE encoded. -/
@[simp] theorem isIEEE_ieee (expWidth fracWidth : Nat)
    (expWidth_ge_two : 2 ≤ expWidth := by decide)
    (fracWidth_pos : 0 < fracWidth := by decide) :
    (ieee expWidth fracWidth expWidth_ge_two fracWidth_pos).isIEEE = true := by
  simp [isIEEE, ieee, ieeeBias, bias]

/-- Characterization of descriptors represented exactly by Lean's IEEE logical model. -/
theorem isIEEE_eq_true_iff (fmt : FloatFormat) :
    fmt.isIEEE = true ↔
      fmt.encoding = .ieee ∧ fmt.exponentBias = fmt.bias := by
  simp [isIEEE]

/-- An IEEE descriptor uses the IEEE exceptional-value encoding. -/
theorem encoding_eq_ieee_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.encoding = .ieee :=
  ((isIEEE_eq_true_iff fmt).mp hfmt).1

/-- An IEEE descriptor uses the conventional layout-derived exponent bias. -/
theorem exponentBias_eq_bias_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.exponentBias = fmt.bias :=
  ((isIEEE_eq_true_iff fmt).mp hfmt).2

/-- A conventional IEEE descriptor necessarily uses the infinity-bearing encoding policy. -/
theorem supportsInfinity_eq_true_of_isIEEE (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) :
    fmt.supportsInfinity = true := by
  simp [supportsInfinity, encoding_eq_ieee_of_isIEEE fmt hfmt]

/-- Every IEEE descriptor represents positive and negative zero separately. -/
@[simp] theorem supportsSignedZero_eq_true_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.supportsSignedZero = true := by
  simp [supportsSignedZero, encoding_eq_ieee_of_isIEEE fmt hfmt]

/-- Smallest unbiased normal exponent under the format's declared bias. -/
@[inline] def minNormalExponent (fmt : FloatFormat) : Int :=
  1 - Int.ofNat fmt.exponentBias

/-- Dyadic exponent of the least positive subnormal under the format's declared bias. -/
@[inline] def minSubnormalExponent (fmt : FloatFormat) : Int :=
  fmt.minNormalExponent - Int.ofNat fmt.fracWidth

/-!
## Dyadic scale constants

Two families of exponent bounds coexist. The policy-aware family (`minNormalExponent`,
`minSubnormalExponent`, `maxNormalExponent`, `normalMantissaExpOffset`, `subnormalAlignExp`) is
derived from the declared `fmt.exponentBias` and `fmt.encoding` and is the one executable
semantics use. The `ieee`-prefixed family below is derived from the layout alone through the
conventional bias `fmt.bias` and matches Lean's logical IEEE model; it agrees with the
policy-aware family when `fmt.isIEEE`, as the `*_eq_ieee` theorems state. Custom biases and
finite-only encodings can change these bounds.
-/

/--
Dyadic exponent of the least positive subnormal in the conventional IEEE reading of the layout
(binary32: `-149`). For policy-aware semantics use `minSubnormalExponent`, which is based on
`fmt.exponentBias` rather than the layout-derived `fmt.bias`.
-/
@[inline] def ieeeMinSubnormalExponent (fmt : FloatFormat) : Int :=
  (1 : Int) - Int.ofNat fmt.bias - Int.ofNat fmt.fracWidth

/--
Offset from the biased exponent field to the dyadic exponent of an integer normal significand:
a normal word with biased exponent `e` and fraction `f` denotes
`(2^fracWidth + f) * 2^(e - normalMantissaExpOffset)` (binary32: `150`).
-/
@[inline] def normalMantissaExpOffset (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth

/--
Largest unbiased normal exponent in the conventional IEEE reading of the layout
(binary32: `127`). For policy-aware semantics use `maxNormalExponent`; the two differ for
finite-only encodings, whose all-ones exponent field is finite, and for custom biases.
-/
@[inline] def ieeeMaxNormalExponent (fmt : FloatFormat) : Nat :=
  fmt.bias

/--
Smallest unbiased normal exponent in the conventional IEEE reading of the layout
(binary32: `-126`). For policy-aware semantics use `minNormalExponent`.
-/
@[inline] def ieeeMinNormalExponent (fmt : FloatFormat) : Int :=
  (1 : Int) - Int.ofNat fmt.bias

/-- For an IEEE descriptor, the policy-aware lower normal exponent is the conventional bound. -/
theorem minNormalExponent_eq_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.minNormalExponent = fmt.ieeeMinNormalExponent := by
  simp [minNormalExponent, ieeeMinNormalExponent,
    exponentBias_eq_bias_of_isIEEE fmt hfmt]

/-- For an IEEE descriptor, the policy-aware subnormal quantum is the conventional bound. -/
theorem minSubnormalExponent_eq_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.minSubnormalExponent = fmt.ieeeMinSubnormalExponent := by
  simp [minSubnormalExponent, minNormalExponent, ieeeMinSubnormalExponent,
    exponentBias_eq_bias_of_isIEEE fmt hfmt]

/--
Shift that aligns a subnormal fraction field with its dyadic exponent under the declared bias
(binary32: `149`).
-/
@[inline] def subnormalAlignExp (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth - 1

/--
Layout-derived counterpart of `normalMantissaExpOffset`, using the conventional bias `fmt.bias`.
-/
@[inline] def ieeeNormalMantissaExpOffset (fmt : FloatFormat) : Nat :=
  fmt.bias + fmt.fracWidth

/-- Layout-derived counterpart of `subnormalAlignExp`, using the conventional bias `fmt.bias`. -/
@[inline] def ieeeSubnormalAlignExp (fmt : FloatFormat) : Nat :=
  fmt.bias + fmt.fracWidth - 1

/-!
## Layout formulas

The sign occupies the top bit, followed by the exponent and then the low fraction field.
-/

/-- Sign bit index (binary32: `31`). -/
@[inline] def signBitIndex (fmt : FloatFormat) : Nat :=
  fmt.bitWidth - 1

/-- All-ones exponent field alone (binary32: `255`). -/
@[inline] def expAllOnesNat (fmt : FloatFormat) : Nat :=
  (2 ^ fmt.expWidth) - 1

/-- The all-ones exponent field is twice the conventional layout-derived bias plus one. -/
theorem expAllOnesNat_eq_two_mul_bias_add_one (fmt : FloatFormat) :
    fmt.expAllOnesNat = 2 * fmt.bias + 1 := by
  unfold expAllOnesNat
  rw [two_pow_expWidth_eq_two_mul_bias_add_two]
  omega

/-- Every supported descriptor has exponent fields zero, one, and the all-ones pattern. -/
theorem one_lt_expAllOnesNat (fmt : FloatFormat) :
    1 < fmt.expAllOnesNat := by
  have hfour : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
        fmt.expWidth_ge_two
  unfold expAllOnesNat
  omega

/-- A valid exponent field has a nonzero all-ones pattern. -/
theorem expAllOnesNat_pos (fmt : FloatFormat) :
    0 < expAllOnesNat fmt :=
  Nat.zero_lt_of_lt (one_lt_expAllOnesNat fmt)

/-- Fraction mask in low bits (binary32: `2^23 - 1`). -/
@[inline] def fracMaskNat (fmt : FloatFormat) : Nat :=
  (2 ^ fmt.fracWidth) - 1

/-- A valid fraction field has a nonzero low-bit mask. -/
theorem fracMaskNat_pos (fmt : FloatFormat) :
    0 < fmt.fracMaskNat := by
  have hpow : 2 ≤ 2 ^ fmt.fracWidth := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.fracWidth_pos
  unfold fracMaskNat
  omega

/-- Largest encoded exponent that belongs to a finite value. -/
@[inline] def maxFiniteExpField (fmt : FloatFormat) : Nat :=
  fmt.encoding.maxFiniteExponent fmt.expWidth

/-- Largest fraction at `maxFiniteExpField` that remains finite. -/
@[inline] def maxFiniteFracField (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .finiteMaxNaN => fmt.fracMaskNat - 1
  | .ieee | .finiteUnsignedZero | .finite => fmt.fracMaskNat

/-- The largest finite exponent field is nonzero. -/
theorem maxFiniteExpField_pos (fmt : FloatFormat) :
    0 < fmt.maxFiniteExpField := by
  have hfour : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
  cases hencoding : fmt.encoding <;>
    simp [maxFiniteExpField, Encoding.maxFiniteExponent, hencoding] <;>
    omega

/-- The largest finite exponent field fits in the stored exponent width. -/
theorem maxFiniteExpField_lt_two_pow (fmt : FloatFormat) :
    fmt.maxFiniteExpField < 2 ^ fmt.expWidth := by
  have hpow : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
  cases hencoding : fmt.encoding <;>
    simp [maxFiniteExpField, Encoding.maxFiniteExponent, hencoding] <;>
    omega

/-- The largest finite fraction field fits in the stored fraction width. -/
theorem maxFiniteFracField_lt_two_pow (fmt : FloatFormat) :
    fmt.maxFiniteFracField < 2 ^ fmt.fracWidth := by
  have hpow : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  cases hencoding : fmt.encoding <;>
    simp [maxFiniteFracField, fracMaskNat, hencoding] <;>
    omega

/-- Largest unbiased exponent occurring among finite normal values. -/
@[inline] def maxNormalExponent (fmt : FloatFormat) : Int :=
  Int.ofNat fmt.maxFiniteExpField - Int.ofNat fmt.exponentBias

/-- For an IEEE descriptor, the policy-aware upper exponent is the conventional IEEE bound. -/
theorem maxNormalExponent_eq_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.maxNormalExponent = Int.ofNat fmt.ieeeMaxNormalExponent := by
  obtain ⟨hencoding, hbias⟩ :=
    (isIEEE_eq_true_iff fmt).mp hfmt
  have hge := fmt.expWidth_ge_two
  have hwidth : fmt.expWidth = (fmt.expWidth - 1) + 1 := by
    omega
  have hpow :
      2 ^ fmt.expWidth = 2 * 2 ^ (fmt.expWidth - 1) := by
    rw [hwidth, Nat.pow_succ]
    exact Nat.mul_comm _ _
  have hhalf : 0 < 2 ^ (fmt.expWidth - 1) := Nat.two_pow_pos _
  simp only [maxNormalExponent, maxFiniteExpField,
    Encoding.maxFiniteExponent, ieeeMaxNormalExponent, bias, hencoding, hbias]
  have hnat :
      (2 ^ fmt.expWidth - 2) - (2 ^ (fmt.expWidth - 1) - 1) =
        2 ^ (fmt.expWidth - 1) - 1 := by
    omega
  have hle :
      2 ^ (fmt.expWidth - 1) - 1 ≤ 2 ^ fmt.expWidth - 2 := by
    omega
  calc
    Int.ofNat (2 ^ fmt.expWidth - 2) -
          Int.ofNat (2 ^ (fmt.expWidth - 1) - 1) =
        Int.ofNat
          ((2 ^ fmt.expWidth - 2) -
            (2 ^ (fmt.expWidth - 1) - 1)) :=
      (Int.ofNat_sub hle).symm
    _ = Int.ofNat (2 ^ (fmt.expWidth - 1) - 1) := by rw [hnat]

/-- Exponent mask shifted into place (binary32: `0x7F800000`). -/
@[inline] def expMaskNat (fmt : FloatFormat) : Nat :=
  expAllOnesNat fmt * (2 ^ fmt.fracWidth)

/-- Sign-bit mask (binary32: `2^31`). -/
@[inline] def signMaskNat (fmt : FloatFormat) : Nat :=
  2 ^ (signBitIndex fmt)

/-- Quiet-NaN bit (binary32: `2^22`). -/
@[inline] def quietBitNat (fmt : FloatFormat) : Nat :=
  2 ^ (fmt.fracWidth - 1)

end FloatFormat
end FloatLib.Floats.Formats.BinaryInterchange

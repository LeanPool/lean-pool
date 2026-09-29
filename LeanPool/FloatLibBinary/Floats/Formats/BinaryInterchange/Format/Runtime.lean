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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Properties

/-!
# Compiled binary format constants

Layout proofs are easiest to read with powers such as `2 ^ fmt.expWidth`; compiled code is better
served by left shifts. Frequently used format values therefore have shift-based implementations,
with proved equalities registered for compiler substitution.

Source-level theorems use the mathematical definitions; compiler substitutions replace them
with the proved shift formulas.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace FloatFormat

/-- Shift-based compiled implementation of `bias`. -/
@[inline] def biasImpl (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (fmt.expWidth - 1) - 1

/-- Shift-based compiled implementation of `ieeeMinSubnormalExponent`. -/
@[inline] def ieeeMinSubnormalExponentImpl (fmt : FloatFormat) : Int :=
  (1 : Int) - Int.ofNat (biasImpl fmt) - Int.ofNat fmt.fracWidth

/-- Compiled implementation of `normalMantissaExpOffset`. -/
@[inline] def normalMantissaExpOffsetImpl (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth

/-- Shift-based compiled implementation of `ieeeMaxNormalExponent`. -/
@[inline] def ieeeMaxNormalExponentImpl (fmt : FloatFormat) : Nat :=
  biasImpl fmt

/-- Shift-based compiled implementation of `ieeeMinNormalExponent`. -/
@[inline] def ieeeMinNormalExponentImpl (fmt : FloatFormat) : Int :=
  (1 : Int) - Int.ofNat (biasImpl fmt)

/-- Compiled implementation of `subnormalAlignExp`. -/
@[inline] def subnormalAlignExpImpl (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth - 1

/-- Shift-based compiled implementation of `expAllOnesNat`. -/
@[inline] def expAllOnesNatImpl (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 fmt.expWidth - 1

/-- Shift-based compiled implementation of `fracMaskNat`. -/
@[inline] def fracMaskNatImpl (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 fmt.fracWidth - 1

/-- Shift-based compiled implementation of `expMaskNat`. -/
@[inline] def expMaskNatImpl (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft (expAllOnesNat fmt) fmt.fracWidth

/-- Shift-based compiled implementation of `signMaskNat`. -/
@[inline] def signMaskNatImpl (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (signBitIndex fmt)

/-- Shift-based compiled implementation of `quietBitNat`. -/
@[inline] def quietBitNatImpl (fmt : FloatFormat) : Nat :=
  Nat.shiftLeft 1 (fmt.fracWidth - 1)

/-- Compiler substitution of exponent-bias exponentiation by the equivalent shift kernel. -/
@[csimp] theorem bias_eq_biasImpl :
    bias = biasImpl := by
  funext fmt
  simp [bias, biasImpl, Nat.shiftLeft_eq]

/-- Compiler substitution for the least-subnormal dyadic exponent. -/
@[csimp] theorem ieeeMinSubnormalExponent_eq_ieeeMinSubnormalExponentImpl :
    ieeeMinSubnormalExponent = ieeeMinSubnormalExponentImpl := by
  funext fmt
  simp [ieeeMinSubnormalExponent, ieeeMinSubnormalExponentImpl, bias, biasImpl, Nat.shiftLeft_eq]

/-- Compiler substitution for the normal-significand exponent offset. -/
@[csimp] theorem normalMantissaExpOffset_eq_normalMantissaExpOffsetImpl :
    normalMantissaExpOffset = normalMantissaExpOffsetImpl := by
  funext fmt
  rfl

/-- Compiler substitution for the greatest normal unbiased exponent. -/
@[csimp] theorem ieeeMaxNormalExponent_eq_ieeeMaxNormalExponentImpl :
    ieeeMaxNormalExponent = ieeeMaxNormalExponentImpl := by
  funext fmt
  simp [ieeeMaxNormalExponent, ieeeMaxNormalExponentImpl, bias, biasImpl,
    Nat.shiftLeft_eq]

/-- Compiler substitution for the least normal unbiased exponent. -/
@[csimp] theorem ieeeMinNormalExponent_eq_ieeeMinNormalExponentImpl :
    ieeeMinNormalExponent = ieeeMinNormalExponentImpl := by
  funext fmt
  simp [ieeeMinNormalExponent, ieeeMinNormalExponentImpl, bias, biasImpl,
    Nat.shiftLeft_eq]

/-- Compiler substitution for the subnormal alignment exponent. -/
@[csimp] theorem subnormalAlignExp_eq_subnormalAlignExpImpl :
    subnormalAlignExp = subnormalAlignExpImpl := by
  funext fmt
  rfl

/-- Compiler substitution of the all-ones exponent mask by the equivalent shift kernel. -/
@[csimp] theorem expAllOnesNat_eq_expAllOnesNatImpl :
    expAllOnesNat = expAllOnesNatImpl := by
  funext fmt
  simp [expAllOnesNat, expAllOnesNatImpl, Nat.shiftLeft_eq]

/-- Compiler substitution of the fraction mask by the equivalent shift kernel. -/
@[csimp] theorem fracMaskNat_eq_fracMaskNatImpl :
    fracMaskNat = fracMaskNatImpl := by
  funext fmt
  simp [fracMaskNat, fracMaskNatImpl, Nat.shiftLeft_eq]

/-- Compiler substitution of the shifted exponent mask by the equivalent shift kernel. -/
@[csimp] theorem expMaskNat_eq_expMaskNatImpl :
    expMaskNat = expMaskNatImpl := by
  funext fmt
  simp [expMaskNat, expMaskNatImpl, Nat.shiftLeft_eq]

/-- Compiler substitution of the sign mask by the equivalent shift kernel. -/
@[csimp] theorem signMaskNat_eq_signMaskNatImpl :
    signMaskNat = signMaskNatImpl := by
  funext fmt
  simp [signMaskNat, signMaskNatImpl, Nat.shiftLeft_eq]

/-- Compiler substitution of the quiet-NaN bit by the equivalent shift kernel. -/
@[csimp] theorem quietBitNat_eq_quietBitNatImpl :
    quietBitNat = quietBitNatImpl := by
  funext fmt
  simp [quietBitNat, quietBitNatImpl, Nat.shiftLeft_eq]

end FloatFormat
end FloatLib.Floats.Formats.BinaryInterchange

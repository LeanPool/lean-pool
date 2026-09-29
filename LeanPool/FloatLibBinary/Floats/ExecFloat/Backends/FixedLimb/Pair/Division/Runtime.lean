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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.CertifiedDivision.Runtime

/-!
# Two-word division runtime

The first path checks a radix-`2^32` quotient candidate with an independent Euclidean
certificate. A rejected candidate is replaced by the fixed-word restoring result whose
equality to the logical divider is proved in `CertifiedDivision.Proof`. The selected pair is then
rounded and packed. This module exposes only the partial specialized kernel for every eligible
two-word layout; the dispatcher owns the exact baseline for cases outside its normal finite range.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Try certified fixed-word division for two normal operands.

Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def divNormalOption {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt then
    none
  else
    let num := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let den := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    let less := FloatLib.Numerics.FixedWord.UInt128.less num den
    let rationalExponent : Int := if less then -1 else 0
    let totalExponent :=
      rationalExponent +
        (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat)
    if totalExponent < fmt.ieeeMinNormalExponent then
      none
    else
      let candidateShift :
          FloatLib.Numerics.FixedWord.CertifiedDivision.CandidateShift :=
        if less then .extra else .exact
      let shift := candidateShift.toNat fmt.fracWidth
      let candidate :=
        FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate
          fmt.fracWidth num den candidateShift
      let rounded :=
        FloatLib.Numerics.FixedWord.CertifiedDivision.roundQuotient
          den candidate.quotient candidate.remainder
      let carry := isCarry fmt rounded
      let resultExponent : Int :=
        Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat +
          Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0
      if resultExponent ≤ 0 || Int.ofNat fmt.expAllOnesNat ≤ resultExponent then
        none
      else
        some <| packNormal fmt
          (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
          (UInt64.ofNat resultExponent.toNat) (normalizeCarry fmt carry rounded)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

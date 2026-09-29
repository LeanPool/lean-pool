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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.RealSemantics

/-!
# Order theory for exact dyadics

The executable `cmpDyadic` comparison agrees with real order. The proof aligns both integer
significands at the smaller exponent and then cancels their common positive power-of-two scale.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

namespace Dyadic

/--
Real semantics after moving a dyadic significand to any smaller exponent.

The aligned integer is the exact signed significand at scale `2^exponent`.
-/
theorem toReal_eq_signedSignificand_shiftLeft (d : Numerics.Dyadic) (exponent : Int)
    (hexponent : exponent ≤ d.exponent) :
    d.toReal =
      ((Numerics.Dyadic.mk d.negative
          (Nat.shiftLeft d.significand (Int.toNat (d.exponent - exponent))) 0).signedSignificand
            : ℝ) *
        bpow Numerics.binaryRadix exponent := by
  have hnonneg : 0 ≤ d.exponent - exponent := sub_nonneg.mpr hexponent
  have htoNat : (Int.ofNat (Int.toNat (d.exponent - exponent))) = d.exponent - exponent := by
    simpa using Int.toNat_of_nonneg hnonneg
  have hpow :
      bpow Numerics.binaryRadix d.exponent =
        bpow Numerics.binaryRadix exponent *
          bpow Numerics.binaryRadix (d.exponent - exponent) := by
    have hadd : exponent + (d.exponent - exponent) = d.exponent := by omega
    simpa [hadd] using
      bpow.add_exp Numerics.binaryRadix exponent (d.exponent - exponent)
  let shift := Int.toNat (d.exponent - exponent)
  have hpowShift :
      bpow Numerics.binaryRadix (d.exponent - exponent) =
        bpow Numerics.binaryRadix (Int.ofNat shift) := by
    simpa [shift] using
      congrArg (fun value : Int => bpow Numerics.binaryRadix value) htoNat.symm
  have hshift :
      ((Numerics.Dyadic.mk d.negative (Nat.shiftLeft d.significand shift) 0).signedSignificand :
        ℝ) =
        (d.signedSignificand : ℝ) *
          bpow Numerics.binaryRadix (d.exponent - exponent) := by
    have hshiftNat := signedSignificand_shiftLeft d shift
    simpa [hpowShift] using hshiftNat
  rw [toReal_eq_signedSignificand, hpow]
  rw [show
    (d.signedSignificand : ℝ) *
        (bpow Numerics.binaryRadix exponent *
          bpow Numerics.binaryRadix (d.exponent - exponent)) =
      ((d.signedSignificand : ℝ) *
          bpow Numerics.binaryRadix (d.exponent - exponent)) *
        bpow Numerics.binaryRadix exponent by ring]
  simpa [shift, mul_assoc] using
    congrArg (fun value : ℝ => value * bpow Numerics.binaryRadix exponent) hshift.symm

end Dyadic

private def alignedSignedMantissa (d : Numerics.Dyadic) (exponent : Int) : Int :=
  (Numerics.Dyadic.mk d.negative (Nat.shiftLeft d.significand (Int.toNat (d.exponent -
    exponent))) 0).signedSignificand

private theorem cmpDyadic_eq_compare_aligned (a b : Numerics.Dyadic)
    (hzero : (a.significand == 0 && b.significand == 0) = false) :
    let exponent := if a.exponent ≤ b.exponent then a.exponent else b.exponent
    cmpDyadic a b =
      compare (alignedSignedMantissa a exponent) (alignedSignedMantissa b exponent) := by
  simp (config := { zeta := true })
    [cmpDyadic, hzero, alignedSignedMantissa, Numerics.Dyadic.signedSignificand]

private theorem aligned_scale (d : Numerics.Dyadic) (exponent : Int) (hexponent : exponent ≤
  d.exponent) :
    d.toReal =
      (alignedSignedMantissa d exponent : ℝ) *
        bpow Numerics.binaryRadix exponent := by
  simpa [alignedSignedMantissa] using
    Dyadic.toReal_eq_signedSignificand_shiftLeft d exponent hexponent

/-- Executable dyadic comparison returns `.lt` exactly when the real values are ordered. -/
theorem cmpDyadic_lt_iff (a b : Numerics.Dyadic) :
    cmpDyadic a b = .lt ↔ a.toReal < b.toReal := by
  classical
  cases hzero : (a.significand == 0 && b.significand == 0) with
  | true =>
      have hparts : (a.significand == 0) = true ∧ (b.significand == 0) = true := by
        simpa [Bool.and_eq_true] using hzero
      have ha : a.significand = 0 := beq_iff_eq.mp hparts.1
      have hb : b.significand = 0 := beq_iff_eq.mp hparts.2
      simp [cmpDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, ha, hb]
  | false =>
      let exponent := if a.exponent ≤ b.exponent then a.exponent else b.exponent
      have haExponent : exponent ≤ a.exponent := by
        by_cases hab : a.exponent ≤ b.exponent
        · simp [exponent, hab]
        · have hba : b.exponent ≤ a.exponent := le_of_not_ge hab
          simp [exponent, hab, hba]
      have hbExponent : exponent ≤ b.exponent := by
        by_cases hab : a.exponent ≤ b.exponent
        · simp [exponent, hab]
        · simp [exponent, hab]
      let aInt := alignedSignedMantissa a exponent
      let bInt := alignedSignedMantissa b exponent
      have hcmp : cmpDyadic a b = compare aInt bInt := by
        simpa [exponent, aInt, bInt] using
          cmpDyadic_eq_compare_aligned a b hzero
      have ha :
          a.toReal = (aInt : ℝ) * bpow Numerics.binaryRadix exponent := by
        simpa [aInt] using aligned_scale a exponent haExponent
      have hb :
          b.toReal = (bInt : ℝ) * bpow Numerics.binaryRadix exponent := by
        simpa [bInt] using aligned_scale b exponent hbExponent
      have hscale : 0 < bpow Numerics.binaryRadix exponent :=
        bpow.pos Numerics.binaryRadix exponent
      have hlt : aInt < bInt ↔ a.toReal < b.toReal := by
        constructor
        · intro hab
          have habReal : (aInt : ℝ) < (bInt : ℝ) := by exact_mod_cast hab
          simpa [ha, hb] using mul_lt_mul_of_pos_right habReal hscale
        · intro hab
          have habScaled :
              (aInt : ℝ) * bpow Numerics.binaryRadix exponent <
                (bInt : ℝ) * bpow Numerics.binaryRadix exponent := by
            simpa [ha, hb] using hab
          have habReal : (aInt : ℝ) < (bInt : ℝ) :=
            lt_of_mul_lt_mul_right habScaled (le_of_lt hscale)
          exact_mod_cast habReal
      simp [hcmp, compare_lt_iff_lt, hlt]

/-- Executable dyadic comparison returns `.eq` exactly when the real values are equal. -/
theorem cmpDyadic_eq_iff (a b : Numerics.Dyadic) :
    cmpDyadic a b = .eq ↔ a.toReal = b.toReal := by
  classical
  cases hzero : (a.significand == 0 && b.significand == 0) with
  | true =>
      have hparts : (a.significand == 0) = true ∧ (b.significand == 0) = true := by
        simpa [Bool.and_eq_true] using hzero
      have ha : a.significand = 0 := beq_iff_eq.mp hparts.1
      have hb : b.significand = 0 := beq_iff_eq.mp hparts.2
      simp [cmpDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, ha, hb]
  | false =>
      let exponent := if a.exponent ≤ b.exponent then a.exponent else b.exponent
      have haExponent : exponent ≤ a.exponent := by
        by_cases hab : a.exponent ≤ b.exponent
        · simp [exponent, hab]
        · have hba : b.exponent ≤ a.exponent := le_of_not_ge hab
          simp [exponent, hab, hba]
      have hbExponent : exponent ≤ b.exponent := by
        by_cases hab : a.exponent ≤ b.exponent
        · simp [exponent, hab]
        · simp [exponent, hab]
      let aInt := alignedSignedMantissa a exponent
      let bInt := alignedSignedMantissa b exponent
      have hcmp : cmpDyadic a b = compare aInt bInt := by
        simpa [exponent, aInt, bInt] using
          cmpDyadic_eq_compare_aligned a b hzero
      have ha :
          a.toReal = (aInt : ℝ) * bpow Numerics.binaryRadix exponent := by
        simpa [aInt] using aligned_scale a exponent haExponent
      have hb :
          b.toReal = (bInt : ℝ) * bpow Numerics.binaryRadix exponent := by
        simpa [bInt] using aligned_scale b exponent hbExponent
      have hscale : bpow Numerics.binaryRadix exponent ≠ 0 :=
        ne_of_gt (bpow.pos Numerics.binaryRadix exponent)
      have heq : aInt = bInt ↔ a.toReal = b.toReal := by
        rw [ha, hb]
        constructor
        · intro h
          simp [h]
        · intro h
          have hcast : (aInt : ℝ) = (bInt : ℝ) :=
            mul_right_cancel₀ hscale h
          exact_mod_cast hcast
      simp [hcmp, heq]

/-- Executable dyadic comparison returns `.gt` exactly when the real values are reversed. -/
theorem cmpDyadic_gt_iff (a b : Numerics.Dyadic) :
    cmpDyadic a b = .gt ↔ b.toReal < a.toReal := by
  classical
  cases hzero : (a.significand == 0 && b.significand == 0) with
  | true =>
      have hparts : (a.significand == 0) = true ∧ (b.significand == 0) = true := by
        simpa [Bool.and_eq_true] using hzero
      have ha : a.significand = 0 := beq_iff_eq.mp hparts.1
      have hb : b.significand = 0 := beq_iff_eq.mp hparts.2
      simp [cmpDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, ha, hb]
  | false =>
      let exponent := if a.exponent ≤ b.exponent then a.exponent else b.exponent
      have haExponent : exponent ≤ a.exponent := by
        by_cases hab : a.exponent ≤ b.exponent
        · simp [exponent, hab]
        · have hba : b.exponent ≤ a.exponent := le_of_not_ge hab
          simp [exponent, hab, hba]
      have hbExponent : exponent ≤ b.exponent := by
        by_cases hab : a.exponent ≤ b.exponent
        · simp [exponent, hab]
        · simp [exponent, hab]
      let aInt := alignedSignedMantissa a exponent
      let bInt := alignedSignedMantissa b exponent
      have hcmp : cmpDyadic a b = compare aInt bInt := by
        simpa [exponent, aInt, bInt] using
          cmpDyadic_eq_compare_aligned a b hzero
      have ha :
          a.toReal = (aInt : ℝ) * bpow Numerics.binaryRadix exponent := by
        simpa [aInt] using aligned_scale a exponent haExponent
      have hb :
          b.toReal = (bInt : ℝ) * bpow Numerics.binaryRadix exponent := by
        simpa [bInt] using aligned_scale b exponent hbExponent
      have hscale : 0 < bpow Numerics.binaryRadix exponent :=
        bpow.pos Numerics.binaryRadix exponent
      have hgt : bInt < aInt ↔ b.toReal < a.toReal := by
        constructor
        · intro hab
          have habReal : (bInt : ℝ) < (aInt : ℝ) := by exact_mod_cast hab
          simpa [ha, hb] using mul_lt_mul_of_pos_right habReal hscale
        · intro hab
          have habScaled :
              (bInt : ℝ) * bpow Numerics.binaryRadix exponent <
                (aInt : ℝ) * bpow Numerics.binaryRadix exponent := by
            simpa [ha, hb] using hab
          have habReal : (bInt : ℝ) < (aInt : ℝ) :=
            lt_of_mul_lt_mul_right habScaled (le_of_lt hscale)
          exact_mod_cast habReal
      simp [hcmp, compare_gt_iff_gt, hgt]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange

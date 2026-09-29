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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.SignedMagnitude.Runtime
public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Proof

/-!
# Exactness of shared native signed-magnitude arithmetic

The format-independent `UInt64` signed-magnitude primitive implements exact dyadic addition
under its capacity hypotheses. Equal signs require a no-overflow hypothesis; opposite signs
reduce to an exact difference. The two-limb refinement is in `SignedMagnitude.UInt128.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
Interpret a native signed magnitude as the canonical exact dyadic used after addition.

Exact cancellation is normalized to positive zero with exponent zero. Nonzero results retain the
common exponent at which their magnitudes were added.
-/
def signedMagnitudeDyadic
    (negative : Bool) (magnitude : UInt64) (exponent : Int) : Dyadic :=
  if magnitude == 0 then
    { negative := false, significand := 0, exponent := 0 }
  else
    { negative, significand := magnitude.toNat, exponent }

/--
A zero magnitude returned by native signed-magnitude addition always has a positive sign.

The no-overflow premise rules out a wrapped same-sign sum. With nonzero inputs, the remaining
zero case is exact cancellation of opposite, equal magnitudes.
-/
theorem addSignedMagnitudes_sign_eq_false_of_magnitude_eq_zero
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt64)
    (hleft : leftMagnitude ≠ 0) (hright : rightMagnitude ≠ 0)
    (hsum :
      leftNegative = rightNegative →
        leftMagnitude.toNat + rightMagnitude.toNat < 2 ^ 64)
    (hzero :
      (addSignedMagnitudes
        leftNegative rightNegative leftMagnitude rightMagnitude).2 = 0) :
    (addSignedMagnitudes
      leftNegative rightNegative leftMagnitude rightMagnitude).1 = false := by
  have hleftNat : leftMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hleft
  have hrightNat : rightMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hright
  cases leftNegative <;> cases rightNegative
  · simp [addSignedMagnitudes]
  · by_cases heq : leftMagnitude = rightMagnitude
    · simp [addSignedMagnitudes, heq]
    · by_cases hlt : leftMagnitude < rightMagnitude
      · exfalso
        have hsubZero : rightMagnitude - leftMagnitude = 0 := by
          simpa [addSignedMagnitudes, heq, hlt] using hzero
        have hsubNat := congrArg UInt64.toNat hsubZero
        rw [UInt64.toNat_sub_of_le] at hsubNat
        · simp only [UInt64.toNat_zero] at hsubNat
          have hnatLt := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        · exact UInt64.le_of_lt hlt
      · simp [addSignedMagnitudes, heq, hlt]
  · by_cases heq : leftMagnitude = rightMagnitude
    · simp [addSignedMagnitudes, heq]
    · by_cases hlt : leftMagnitude < rightMagnitude
      · simp [addSignedMagnitudes, heq, hlt]
      · exfalso
        have hnotLt : ¬leftMagnitude.toNat < rightMagnitude.toNat := by
          intro h
          exact hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have hne : leftMagnitude.toNat ≠ rightMagnitude.toNat := by
          intro h
          exact heq (UInt64.toNat_inj.mp h)
        have hrightLt : rightMagnitude < leftMagnitude :=
          UInt64.lt_iff_toNat_lt.mpr (by omega)
        have hsubZero : leftMagnitude - rightMagnitude = 0 := by
          simpa [addSignedMagnitudes, heq, hlt] using hzero
        have hsubNat := congrArg UInt64.toNat hsubZero
        rw [UInt64.toNat_sub_of_le] at hsubNat
        · simp only [UInt64.toNat_zero] at hsubNat
          have hnatLt := UInt64.lt_iff_toNat_lt.mp hrightLt
          omega
        · exact UInt64.le_of_lt hrightLt
  · exfalso
    have hsum' := hsum rfl
    have haddZero : leftMagnitude + rightMagnitude = 0 := by
      simpa [addSignedMagnitudes] using hzero
    have haddNat := congrArg UInt64.toNat haddZero
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum'] at haddNat
    simp only [UInt64.toNat_zero] at haddNat
    omega

/--
Native signed-magnitude addition denotes exact dyadic addition at a common exponent.

The only capacity hypothesis is required by same-sign addition. Opposite-sign subtraction cannot
overflow, while the nonzero hypotheses exclude the input-zero branches handled directly by
format-specific kernels.
-/
theorem signedMagnitudeDyadic_addSignedMagnitudes_eq_addFields
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt64) (exponent : Int)
    (hleft : leftMagnitude ≠ 0) (hright : rightMagnitude ≠ 0)
    (hsum :
      leftNegative = rightNegative →
        leftMagnitude.toNat + rightMagnitude.toNat < 2 ^ 64) :
    signedMagnitudeDyadic
        (addSignedMagnitudes
          leftNegative rightNegative leftMagnitude rightMagnitude).1
        (addSignedMagnitudes
          leftNegative rightNegative leftMagnitude rightMagnitude).2
        exponent =
      Dyadic.addFields
        leftNegative leftMagnitude.toNat exponent
        rightNegative rightMagnitude.toNat exponent := by
  have hleftNat : leftMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hleft
  have hrightNat : rightMagnitude.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hright
  cases leftNegative <;> cases rightNegative
  all_goals
    unfold addSignedMagnitudes signedMagnitudeDyadic Dyadic.addFields
    simp only [hleftNat, hrightNat, beq_iff_eq, ite_false, le_refl, ite_true,
      Bool.false_eq_true, Bool.true_eq_false, sub_self, Int.toNat_zero]
  · have hsum' := hsum rfl
    have hadd :
        (leftMagnitude + rightMagnitude).toNat =
          leftMagnitude.toNat + rightMagnitude.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum']
    have hpositiveNat :
        0 < leftMagnitude.toNat + rightMagnitude.toNat := by
      omega
    have hpositive :
        0 < (leftMagnitude.toNat : Int) + rightMagnitude.toNat := by
      exact_mod_cast hpositiveNat
    have hnatAbs :
        ((leftMagnitude.toNat : Int) + rightMagnitude.toNat).natAbs =
          leftMagnitude.toNat + rightMagnitude.toNat := by
      rw [Int.natAbs_add_of_nonneg] <;> simp
    have hwordNe : leftMagnitude + rightMagnitude ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt64.toNat hzero
      rw [hadd] at hzeroNat
      simp only [UInt64.toNat_zero] at hzeroNat
      omega
    have hintNe :
        (leftMagnitude.toNat : Int) + rightMagnitude.toNat ≠ 0 :=
      ne_of_gt hpositive
    simp [hadd, hwordNe, hintNe, Int.not_lt.mpr hpositive.le, hnatAbs]
  · by_cases heq : leftMagnitude = rightMagnitude
    · subst rightMagnitude
      simp
    · by_cases hlt : leftMagnitude < rightMagnitude
      · have hnatLt : leftMagnitude.toNat < rightMagnitude.toNat :=
          UInt64.lt_iff_toNat_lt.mp hlt
        have hsub :
            (rightMagnitude - leftMagnitude).toNat =
              rightMagnitude.toNat - leftMagnitude.toNat := by
          rw [UInt64.toNat_sub_of_le]
          exact UInt64.le_iff_toNat_le.mpr hnatLt.le
        have hnegative :
            (leftMagnitude.toNat : Int) + -rightMagnitude.toNat < 0 := by
          omega
        have hnatAbs :
            ((leftMagnitude.toNat : Int) + -rightMagnitude.toNat).natAbs =
              rightMagnitude.toNat - leftMagnitude.toNat := by
          have hcast :=
            Int.ofNat_natAbs_of_nonpos (le_of_lt hnegative)
          norm_num at hcast ⊢
          omega
        have hwordNe : rightMagnitude - leftMagnitude ≠ 0 := by
          intro hzero
          have hzeroNat := congrArg UInt64.toNat hzero
          rw [hsub] at hzeroNat
          simp only [UInt64.toNat_zero] at hzeroNat
          omega
        have hintNe :
            (leftMagnitude.toNat : Int) + -rightMagnitude.toNat ≠ 0 :=
          ne_of_lt hnegative
        simp [heq, hlt, hsub, hwordNe, hintNe, hnegative, hnatAbs]
      · have hnatNotLt : ¬leftMagnitude.toNat < rightMagnitude.toNat := by
          intro h
          exact hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have hnatNe : leftMagnitude.toNat ≠ rightMagnitude.toNat := by
          intro h
          apply heq
          exact UInt64.toNat_inj.mp h
        have hnatGt : rightMagnitude.toNat < leftMagnitude.toNat := by
          omega
        have hsub :
            (leftMagnitude - rightMagnitude).toNat =
              leftMagnitude.toNat - rightMagnitude.toNat := by
          rw [UInt64.toNat_sub_of_le]
          exact UInt64.le_iff_toNat_le.mpr hnatGt.le
        have hpositive :
            0 < (leftMagnitude.toNat : Int) + -rightMagnitude.toNat := by
          omega
        have hnatAbs :
            ((leftMagnitude.toNat : Int) + -rightMagnitude.toNat).natAbs =
              leftMagnitude.toNat - rightMagnitude.toNat := by
          have hcast := Int.natAbs_of_nonneg (le_of_lt hpositive)
          norm_num at hcast ⊢
          omega
        have hwordNe : leftMagnitude - rightMagnitude ≠ 0 := by
          intro hzero
          have hzeroNat := congrArg UInt64.toNat hzero
          rw [hsub] at hzeroNat
          simp only [UInt64.toNat_zero] at hzeroNat
          omega
        have hintNe :
            (leftMagnitude.toNat : Int) + -rightMagnitude.toNat ≠ 0 :=
          ne_of_gt hpositive
        simp [heq, hlt, hsub, hwordNe, hintNe, hnatNotLt, hnatAbs]
  · by_cases heq : leftMagnitude = rightMagnitude
    · subst rightMagnitude
      simp
    · by_cases hlt : leftMagnitude < rightMagnitude
      · have hnatLt : leftMagnitude.toNat < rightMagnitude.toNat :=
          UInt64.lt_iff_toNat_lt.mp hlt
        have hsub :
            (rightMagnitude - leftMagnitude).toNat =
              rightMagnitude.toNat - leftMagnitude.toNat := by
          rw [UInt64.toNat_sub_of_le]
          exact UInt64.le_iff_toNat_le.mpr hnatLt.le
        have hpositive :
            0 < -(leftMagnitude.toNat : Int) + rightMagnitude.toNat := by
          omega
        have hnatAbs :
            (-(leftMagnitude.toNat : Int) + rightMagnitude.toNat).natAbs =
              rightMagnitude.toNat - leftMagnitude.toNat := by
          have hcast := Int.natAbs_of_nonneg (le_of_lt hpositive)
          norm_num at hcast ⊢
          omega
        have hnotReverse : ¬rightMagnitude.toNat < leftMagnitude.toNat := by
          omega
        have hwordNe : rightMagnitude - leftMagnitude ≠ 0 := by
          intro hzero
          have hzeroNat := congrArg UInt64.toNat hzero
          rw [hsub] at hzeroNat
          simp only [UInt64.toNat_zero] at hzeroNat
          omega
        have hintNe :
            -(leftMagnitude.toNat : Int) + rightMagnitude.toNat ≠ 0 :=
          ne_of_gt hpositive
        simp [heq, hlt, hsub, hwordNe, hintNe, hnotReverse, hnatAbs]
      · have hnatNotLt : ¬leftMagnitude.toNat < rightMagnitude.toNat := by
          intro h
          exact hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have hnatNe : leftMagnitude.toNat ≠ rightMagnitude.toNat := by
          intro h
          apply heq
          exact UInt64.toNat_inj.mp h
        have hnatGt : rightMagnitude.toNat < leftMagnitude.toNat := by
          omega
        have hsub :
            (leftMagnitude - rightMagnitude).toNat =
              leftMagnitude.toNat - rightMagnitude.toNat := by
          rw [UInt64.toNat_sub_of_le]
          exact UInt64.le_iff_toNat_le.mpr hnatGt.le
        have hnegative :
            -(leftMagnitude.toNat : Int) + rightMagnitude.toNat < 0 := by
          omega
        have hnatAbs :
            (-(leftMagnitude.toNat : Int) + rightMagnitude.toNat).natAbs =
              leftMagnitude.toNat - rightMagnitude.toNat := by
          have hcast :=
            Int.ofNat_natAbs_of_nonpos (le_of_lt hnegative)
          norm_num at hcast ⊢
          omega
        have hwordNe : leftMagnitude - rightMagnitude ≠ 0 := by
          intro hzero
          have hzeroNat := congrArg UInt64.toNat hzero
          rw [hsub] at hzeroNat
          simp only [UInt64.toNat_zero] at hzeroNat
          omega
        have hintNe :
            -(leftMagnitude.toNat : Int) + rightMagnitude.toNat ≠ 0 :=
          ne_of_lt hnegative
        simp [heq, hlt, hsub, hwordNe, hintNe, hnegative, hnatAbs]
  · have hsum' := hsum rfl
    have hadd :
        (leftMagnitude + rightMagnitude).toNat =
          leftMagnitude.toNat + rightMagnitude.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum']
    have hnegative :
        -(leftMagnitude.toNat : Int) + -rightMagnitude.toNat < 0 := by
      omega
    have hnatAbs :
        (-(leftMagnitude.toNat : Int) + -rightMagnitude.toNat).natAbs =
          leftMagnitude.toNat + rightMagnitude.toNat := by
      have hcast :=
        Int.ofNat_natAbs_of_nonpos (le_of_lt hnegative)
      norm_num at hcast ⊢
      omega
    have hwordNe : leftMagnitude + rightMagnitude ≠ 0 := by
      intro hzero
      have hzeroNat := congrArg UInt64.toNat hzero
      rw [hadd] at hzeroNat
      simp only [UInt64.toNat_zero] at hzeroNat
      omega
    have hintNe :
        -(leftMagnitude.toNat : Int) + -rightMagnitude.toNat ≠ 0 :=
      ne_of_lt hnegative
    simp [hadd, hwordNe, hintNe, hnegative, hnatAbs]

end FloatLib.Numerics.FixedWord

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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Core
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Magnitude

/-!
# Real meaning of Lean accuracy certificates

Lean's logical floating-point model carries an `Accuracy` value alongside a truncated natural
mantissa. This module states its intended real-number meaning, proves that right shifts preserve
that meaning, and connects its nearest-even choice to the independent Flocq-style integer rounder.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/--
`accuracyRepresents mantissa accuracy value` states that `mantissa` is the integer truncation of
the nonnegative real `value` and that `accuracy` locates the discarded part relative to one half.
-/
def accuracyRepresents (mantissa : Nat) (accuracy : Accuracy) (value : Real) : Prop :=
  match accuracy with
  | .exact => value = mantissa
  | .inexact .lt =>
      (mantissa : Real) < value ∧ value < mantissa + 1 / 2
  | .inexact .eq =>
      value = mantissa + 1 / 2
  | .inexact .gt =>
      (mantissa : Real) + 1 / 2 < value ∧ value < mantissa + 1

/-- Every represented value lies in the unit interval beginning at its truncated mantissa. -/
theorem accuracyRepresents_bounds
    {mantissa : Nat} {accuracy : Accuracy} {value : Real}
    (h : accuracyRepresents mantissa accuracy value) :
    (mantissa : Real) ≤ value ∧ value < mantissa + 1 := by
  cases accuracy with
  | exact =>
      simp only [accuracyRepresents] at h
      constructor
      · rw [h]
      · rw [h]
        norm_num
  | inexact ordering =>
      cases ordering <;>
        simp only [accuracyRepresents] at h
      · exact ⟨h.1.le, h.2.trans (by norm_num)⟩
      · constructor
        · rw [h]
          norm_num
        · rw [h]
          norm_num
      · constructor <;> nlinarith [h.1, h.2]

/--
A nonzero truncated mantissa determines the binary magnitude of every real value represented by
its accuracy certificate.
-/
theorem magnitude_of_accuracyRepresents
    {mantissa : Nat} {accuracy : Accuracy} {value : Real}
    (hmantissa : mantissa ≠ 0)
    (h : accuracyRepresents mantissa accuracy value) :
    magnitude Numerics.binaryRadix value = Int.ofNat mantissa.log2 + 1 := by
  have hbounds := accuracyRepresents_bounds h
  have hmantissaPos : (0 : Real) < mantissa := by
    exact_mod_cast Nat.pos_of_ne_zero hmantissa
  have hvaluePos : 0 < value := hmantissaPos.trans_le hbounds.1
  apply magnitude_eq_of_bpow_bounds
    Numerics.binaryRadix value (Int.ofNat mantissa.log2 + 1) hvaluePos.ne'
  · rw [abs_of_pos hvaluePos]
    have hlower : 2 ^ mantissa.log2 ≤ mantissa := Nat.log2_self_le hmantissa
    have hlowerReal : (2 ^ mantissa.log2 : Nat) ≤ (mantissa : Real) := by
      exact_mod_cast hlower
    simpa [bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
      hlowerReal.trans hbounds.1
  · rw [abs_of_pos hvaluePos]
    have hupper : mantissa + 1 ≤ 2 ^ (mantissa.log2 + 1) := by
      exact Nat.succ_le_of_lt (Nat.lt_log2_self (n := mantissa))
    have hupperReal : (mantissa : Real) + 1 ≤ (2 ^ (mantissa.log2 + 1) : Nat) := by
      exact_mod_cast hupper
    have hpower :
        bpow Numerics.binaryRadix (Int.ofNat mantissa.log2 + 1) =
          (2 ^ (mantissa.log2 + 1) : Nat) := by
      change (2 : Real) ^ (Int.ofNat mantissa.log2 + 1) =
        ((2 ^ (mantissa.log2 + 1) : Nat) : Real)
      rw [show Int.ofNat mantissa.log2 + 1 =
          Int.ofNat (mantissa.log2 + 1) by
            exact (Int.natCast_add_one mantissa.log2).symm]
      rw [Int.ofNat_eq_natCast, zpow_natCast, Nat.cast_pow]
      norm_num
    rw [hpower]
    exact hbounds.2.trans_le hupperReal

private theorem nat_eq_twice_div_add_mod_two (mantissa : Nat) :
    mantissa = 2 * (mantissa / 2) + mantissa % 2 := by
  omega

/--
One model right shift preserves the accuracy certificate after dividing the represented real by
two.
-/
theorem accuracyRepresents_shiftRightOne
    (em : ExtendedMantissa) (value : Real)
    (h : accuracyRepresents em.mantissa em.accuracy value) :
    accuracyRepresents (ExtendedMantissa.shiftRightOne em).mantissa
      (ExtendedMantissa.shiftRightOne em).accuracy (value / 2) := by
  rcases em with ⟨mantissa, roundBit, stickyBit⟩
  have hdecomp := nat_eq_twice_div_add_mod_two mantissa
  rcases Nat.mod_two_eq_zero_or_one mantissa with hmod | hmod
  · have hmantissa : (mantissa : Real) = 2 * (mantissa / 2 : Nat) := by
      exact_mod_cast (by omega : mantissa = 2 * (mantissa / 2))
    have hshift :
        ExtendedMantissa.shiftRightOne ⟨mantissa, roundBit, stickyBit⟩ =
          ⟨mantissa / 2, false, roundBit || stickyBit⟩ := by
      simp [ExtendedMantissa.shiftRightOne, hmod]
    rw [hshift]
    cases roundBit <;> cases stickyBit
    · change accuracyRepresents (mantissa / 2) .exact (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      nlinarith [hmantissa]
    · change accuracyRepresents (mantissa / 2) (.inexact .lt) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      constructor <;> nlinarith [hmantissa]
    · change accuracyRepresents (mantissa / 2) (.inexact .lt) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      constructor <;> nlinarith [hmantissa]
    · change accuracyRepresents (mantissa / 2) (.inexact .lt) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      constructor <;> nlinarith [hmantissa]
  · have hmantissa : (mantissa : Real) = 2 * (mantissa / 2 : Nat) + 1 := by
      exact_mod_cast (by omega : mantissa = 2 * (mantissa / 2) + 1)
    have hshift :
        ExtendedMantissa.shiftRightOne ⟨mantissa, roundBit, stickyBit⟩ =
          ⟨mantissa / 2, true, roundBit || stickyBit⟩ := by
      simp [ExtendedMantissa.shiftRightOne, hmod]
    rw [hshift]
    cases roundBit <;> cases stickyBit
    · change accuracyRepresents (mantissa / 2) (.inexact .eq) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      nlinarith [hmantissa]
    · change accuracyRepresents (mantissa / 2) (.inexact .gt) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      constructor <;> nlinarith [hmantissa]
    · change accuracyRepresents (mantissa / 2) (.inexact .gt) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      constructor <;> nlinarith [hmantissa]
    · change accuracyRepresents (mantissa / 2) (.inexact .gt) (value / 2)
      simp only [ExtendedMantissa.accuracy, accuracyRepresents] at h ⊢
      constructor <;> nlinarith [hmantissa]

/-- Repeated model right shifts preserve the certificate at the correspondingly divided scale. -/
theorem accuracyRepresents_shift
    (em : ExtendedMantissa) (value : Real) (shift : Nat)
    (h : accuracyRepresents em.mantissa em.accuracy value) :
    accuracyRepresents (em >>> shift).mantissa (em >>> shift).accuracy
      (value / (2 : Real) ^ shift) := by
  induction shift generalizing em value with
  | zero =>
      simpa [HShiftRight.hShiftRight, Nat.repeat] using h
  | succ shift ih =>
      rw [pow_succ]
      have hshift := ih em value h
      have hone := accuracyRepresents_shiftRightOne (em >>> shift)
        (value / (2 : Real) ^ shift) hshift
      simpa [HShiftRight.hShiftRight, Nat.repeat, div_eq_mul_inv, mul_assoc,
        mul_comm, mul_left_comm] using hone

private theorem floor_eq_nat_of_accuracyRepresents
    {mantissa : Nat} {accuracy : Accuracy} {value : Real}
    (h : accuracyRepresents mantissa accuracy value) :
    ⌊value⌋ = Int.ofNat mantissa := by
  apply Int.floor_eq_iff.mpr
  have hb := accuracyRepresents_bounds h
  constructor
  · exact_mod_cast hb.1
  · simpa using hb.2

/-- A valid accuracy certificate makes Lean's and the real model's nearest-even choices equal. -/
theorem roundToNearestEven_eq_nearestEven
    (mantissa : Nat) (accuracy : Accuracy) (value : Real)
    (h : accuracyRepresents mantissa accuracy value) :
    Int.ofNat (accuracy.roundToNearestEven mantissa) =
      nearestEven value := by
  have hfloor := floor_eq_nat_of_accuracyRepresents h
  cases accuracy with
  | exact =>
      simp only [accuracyRepresents] at h
      rw [Accuracy.roundToNearestEven, h]
      simpa using (ValidRnd.id
        (rnd := nearestEven) (Int.ofNat mantissa)).symm
  | inexact ordering =>
      cases ordering with
      | lt =>
          simp only [accuracyRepresents] at h
          have hcast : ((Int.ofNat mantissa : Int) : Real) = mantissa := by
            norm_num
          have hfrac : value - (⌊value⌋ : Int) < 1 / 2 := by
            rw [hfloor, hcast]
            linarith
          rw [nearestEven_eq_floor_of_frac_lt_half value hfrac, hfloor]
          rfl
      | eq =>
          simp only [accuracyRepresents] at h
          have hcast : ((Int.ofNat mantissa : Int) : Real) = mantissa := by
            norm_num
          have hfrac : value - (⌊value⌋ : Int) = 1 / 2 := by
            rw [hfloor, hcast, h]
            ring
          by_cases heven : Even (Int.ofNat mantissa)
          · rw [nearestEven_eq_floor_of_frac_half_even value
              (by simpa using hfrac) (by simpa [hfloor] using heven)]
            rw [hfloor]
            have hmod : mantissa % 2 = 0 := by
              exact Nat.even_iff.mp (Int.even_coe_nat mantissa |>.mp heven)
            simp [Accuracy.roundToNearestEven, hmod]
          · rw [nearestEven_eq_ceil_of_frac_half_odd value
              (by simpa using hfrac) (by simpa [hfloor] using heven)]
            rw [hfloor]
            have hmod : mantissa % 2 = 1 := by
              apply Nat.not_even_iff.mp
              intro hevenNat
              exact heven (Int.even_coe_nat mantissa |>.mpr hevenNat)
            simp [Accuracy.roundToNearestEven, hmod]
      | gt =>
          simp only [accuracyRepresents] at h
          have hcast : ((Int.ofNat mantissa : Int) : Real) = mantissa := by
            norm_num
          have hfrac : value - (⌊value⌋ : Int) > 1 / 2 := by
            rw [hfloor, hcast]
            linarith
          rw [nearestEven_eq_ceil_of_frac_gt_half value hfrac, hfloor]
          simp [Accuracy.roundToNearestEven]

/--
After any model right shift, rounding the resulting extended mantissa agrees with independent
nearest-even rounding of the represented real at the shifted scale.
-/
theorem roundedMantissa_eq_nearestEven
    (mantissa : Nat) (accuracy : Accuracy) (value : Real) (shift : Nat)
    (h : accuracyRepresents mantissa accuracy value) :
    Int.ofNat
        (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>>
          shift).roundedMantissa =
      nearestEven (value / (2 : Real) ^ shift) := by
  let em := ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy
  have hinitial :
      accuracyRepresents em.mantissa em.accuracy value := by
    cases accuracy with
    | exact =>
        simpa [em, ExtendedMantissa.ofMantissaAndAccuracy,
          ExtendedMantissa.accuracy] using h
    | inexact ordering =>
        cases ordering <;>
          simpa [em, ExtendedMantissa.ofMantissaAndAccuracy,
            ExtendedMantissa.accuracy] using h
  have hshifted := accuracyRepresents_shift em value shift hinitial
  exact roundToNearestEven_eq_nearestEven
    (em >>> shift).mantissa (em >>> shift).accuracy
      (value / (2 : Real) ^ shift) hshifted

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange

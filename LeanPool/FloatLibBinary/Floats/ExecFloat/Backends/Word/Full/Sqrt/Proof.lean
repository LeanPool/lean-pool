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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtArithmetic
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.SqrtNormalRounding
public import Mathlib.Data.Nat.Sqrt

/-!
# Correctness of the native binary64 square-root kernel

The restoring two-limb kernel reconstructs its scaled radicand one base-four digit at a time. Its
state invariant proves that the final native root is `Nat.sqrt` with the exact remainder. The
format-level theorem then refines the native field packing to Lean's unpacked binary64 model.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.BaseFour

/-! ## Restoring-root invariant -/

local notation "RootRep64" =>
  RestoringRootState.Represents UInt64.toNat

private theorem digit_lt_four (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat) :
    (digitAt radicand index).toNat < 4 := by
  unfold digitAt
  split <;> exact maskedBaseFourDigit_lt _

private theorem rootStep_spec
    (state : RestoringRootState UInt64) (digit : UInt64) (value : Nat)
    (hrep : RootRep64 state value)
    (hvalue : value < 2 ^ 106)
    (hdigit : digit.toNat < 4) :
    RootRep64 (rootStep digit state) (value * 4 + digit.toNat) := by
  unfold rootStep
  dsimp only
  have hroot :=
    RestoringRootState.root_lt_two_pow UInt64.toNat 53 hrep hvalue
  have hremainderLe :
      state.remainder.toNat ≤ 2 * state.root.toNat :=
    hrep.2
  have hremainder : state.remainder.toNat < 2 ^ 54 := by
    norm_num at hroot ⊢
    omega
  have hrootMulFour :
      (state.root * 4).toNat = state.root.toNat * 4 := by
    rw [UInt64.toNat_mul]
    change (state.root.toNat * 4) % 2 ^ 64 =
      state.root.toNat * 4
    rw [Nat.mod_eq_of_lt]
    norm_num at hroot ⊢
    omega
  have hrootMulTwo :
      (state.root * 2).toNat = state.root.toNat * 2 := by
    rw [UInt64.toNat_mul]
    change (state.root.toNat * 2) % 2 ^ 64 =
      state.root.toNat * 2
    rw [Nat.mod_eq_of_lt]
    norm_num at hroot ⊢
    omega
  have hremainderMulFour :
      (state.remainder * 4).toNat = state.remainder.toNat * 4 := by
    rw [UInt64.toNat_mul]
    change (state.remainder.toNat * 4) % 2 ^ 64 =
      state.remainder.toNat * 4
    rw [Nat.mod_eq_of_lt]
    norm_num at hremainder ⊢
    omega
  have hexpanded :
      (state.remainder * 4 + digit).toNat =
        state.remainder.toNat * 4 + digit.toNat := by
    rw [UInt64.toNat_add, hremainderMulFour]
    apply Nat.mod_eq_of_lt
    norm_num at hremainder ⊢
    omega
  have htrial :
      (state.root * 4 + 1).toNat = state.root.toNat * 4 + 1 := by
    rw [UInt64.toNat_add, hrootMulFour]
    change (state.root.toNat * 4 + 1) % 2 ^ 64 =
      state.root.toNat * 4 + 1
    rw [Nat.mod_eq_of_lt]
    norm_num at hroot ⊢
    omega
  have hrootOdd :
      (state.root * 2 + 1).toNat = state.root.toNat * 2 + 1 := by
    rw [UInt64.toNat_add, hrootMulTwo]
    change (state.root.toNat * 2 + 1) % 2 ^ 64 =
      state.root.toNat * 2 + 1
    rw [Nat.mod_eq_of_lt]
    norm_num at hroot ⊢
    omega
  by_cases hle : state.root * 4 + 1 ≤ state.remainder * 4 + digit
  · rw [ite_eq_left hle]
    have hleNat : state.root.toNat * 4 + 1 ≤
        state.remainder.toNat * 4 + digit.toNat := by
      simpa [UInt64.le_iff_toNat_le, htrial, hexpanded] using hle
    have hremainderSub :
        ((state.remainder * 4 + digit) -
          (state.root * 4 + 1)).toNat =
          state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ hle, hexpanded, htrial]
    have hsubAdd :
        (state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1)) +
            (state.root.toNat * 4 + 1) =
          state.remainder.toNat * 4 + digit.toNat :=
      Nat.sub_add_cancel hleNat
    have hsquare :
        (state.root.toNat * 2 + 1) * (state.root.toNat * 2 + 1) =
          4 * (state.root.toNat * state.root.toNat) + 4 * state.root.toNat + 1 := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hrootOdd, hremainderSub]
      omega
    · rw [hrootOdd, hremainderSub]
      omega
  · rw [ite_eq_right hle]
    have hltNat :
        state.remainder.toNat * 4 + digit.toNat <
          state.root.toNat * 4 + 1 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
      simpa [htrial, hexpanded] using this
    have hsquare :
        state.root.toNat * 2 * (state.root.toNat * 2) =
          4 * (state.root.toNat * state.root.toNat) := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hrootMulTwo, hexpanded]
      omega
    · rw [hrootMulTwo, hexpanded]
      omega

/-! ## Two-word radicand digits -/

private theorem shiftedRadicand_toNat
    (mantissa : UInt64) (shift : Nat)
    (hpositive : 0 < shift)
    (hshift : shift < 128)
    (hfit : mantissa.toNat <<< shift < 2 ^ 128) :
    (shiftedRadicand mantissa shift).toNat =
      mantissa.toNat <<< shift := by
  unfold shiftedRadicand FloatLib.Numerics.FixedWord.UInt128.toNat
  by_cases hsmall : shift < 64
  · rw [ite_eq_left hsmall]
    have hshiftSize : shift < 2 ^ 64 :=
      lt_trans hsmall (by norm_num)
    have hcomplement : 64 - shift < 64 := by omega
    have hcomplementSize : 64 - shift < 2 ^ 64 :=
      lt_trans hcomplement (by norm_num)
    have hlo :
        (mantissa <<< UInt64.ofNat shift).toNat =
          (mantissa.toNat <<< shift) % 2 ^ 64 := by
      rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hshiftSize, Nat.mod_eq_of_lt hsmall]
    have hhi :
        (mantissa >>> UInt64.ofNat (64 - shift)).toNat =
          mantissa.toNat / 2 ^ (64 - shift) := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hcomplementSize,
        Nat.mod_eq_of_lt hcomplement, Nat.shiftRight_eq_div_pow]
    have hpow :
        2 ^ 64 = 2 ^ (64 - shift) * 2 ^ shift := by
      calc
        2 ^ 64 = 2 ^ ((64 - shift) + shift) := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hsmall)]
        _ = 2 ^ (64 - shift) * 2 ^ shift := pow_add ..
    have hquotient :
        (mantissa.toNat <<< shift) / 2 ^ 64 =
          mantissa.toNat / 2 ^ (64 - shift) := by
      rw [Nat.shiftLeft_eq, hpow]
      exact Nat.mul_div_mul_right mantissa.toNat (2 ^ (64 - shift))
        (by positivity)
    rw [hlo, hhi, ← hquotient, Nat.shiftLeft_eq]
    exact Nat.mod_add_div' (mantissa.toNat * 2 ^ shift) (2 ^ 64)
  · rw [ite_eq_right hsmall]
    have hlarge : 64 ≤ shift := Nat.le_of_not_gt hsmall
    have hinner : shift - 64 < 64 := by omega
    have hinnerSize : shift - 64 < 2 ^ 64 :=
      lt_trans hinner (by norm_num)
    have hpow :
        2 ^ shift = 2 ^ (shift - 64) * 2 ^ 64 := by
      calc
        2 ^ shift = 2 ^ ((shift - 64) + 64) := by
          rw [Nat.sub_add_cancel hlarge]
        _ = 2 ^ (shift - 64) * 2 ^ 64 := pow_add ..
    have hhighFit :
        mantissa.toNat <<< (shift - 64) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq] at hfit ⊢
      rw [hpow] at hfit
      nlinarith [show 0 < 2 ^ 64 by positivity]
    have hhi :
        (mantissa <<< UInt64.ofNat (shift - 64)).toNat =
          mantissa.toNat <<< (shift - 64) := by
      rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hinnerSize, Nat.mod_eq_of_lt hinner,
        Nat.mod_eq_of_lt hhighFit]
    rw [hhi]
    simp only [UInt64.reduceToNat, zero_add, Nat.shiftLeft_eq]
    rw [hpow]
    ring

/-! ## Restoring-loop refinement -/

private theorem digitAt_low
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat)
    (hindex : index < 32) :
    (digitAt radicand index).toNat =
      wordDigit radicand.lo index := by
  simp [digitAt, wordDigit, hindex]

private theorem digitAt_high
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat)
    (hindex : 32 ≤ index) :
    (digitAt radicand index).toNat =
      wordDigit radicand.hi (index - 32) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr hindex]

private theorem digitsValue_low
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (steps : Nat)
    (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand steps = wordDigits radicand.lo steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [digitsValue, wordDigits, digitAt_low radicand steps (by omega),
        ih (by omega)]

private theorem digitsValue_high
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (steps : Nat)
    (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (32 + steps) =
      wordDigits radicand.hi steps * place 32 +
        wordDigits radicand.lo 32 := by
  induction steps with
  | zero =>
      change
        digitsValue digitAt radicand 32 =
          0 * place 32 + wordDigits radicand.lo 32
      rw [zero_mul, zero_add]
      exact digitsValue_low radicand 32 (by omega)
  | succ steps ih =>
      change
        (digitAt radicand (32 + steps)).toNat * place (32 + steps) +
            digitsValue digitAt radicand (32 + steps) =
          (wordDigit radicand.hi steps * place steps +
              wordDigits radicand.hi steps) * place 32 +
            wordDigits radicand.lo 32
      rw [digitAt_high radicand (32 + steps) (by omega),
        show 32 + steps - 32 = steps by omega, ih (by omega),
        place_add]
      ring

private theorem digitsValue_53_eq_toNat
    (radicand : FloatLib.Numerics.FixedWord.UInt128)
    (hfit : radicand.toNat < 2 ^ 106) :
    digitsValue digitAt radicand 53 = radicand.toNat := by
  have hhigh : radicand.hi.toNat < 2 ^ 42 := by
    unfold FloatLib.Numerics.FixedWord.UInt128.toNat at hfit
    norm_num at hfit ⊢
    nlinarith [radicand.lo.toNat.zero_le]
  rw [show 53 = 32 + 21 by omega,
    digitsValue_high radicand 21 (by omega),
    wordDigits_eq_mod radicand.hi 21 (by omega),
    wordDigits_eq_mod radicand.lo 32 (by omega)]
  have hlo : radicand.lo.toNat % place 32 = radicand.lo.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using radicand.lo.toNat_lt
  have hhi : radicand.hi.toNat % place 21 = radicand.hi.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using hhigh
  rw [hlo, hhi]
  simp [FloatLib.Numerics.FixedWord.UInt128.toNat, place, Nat.add_comm, Nat.mul_comm]

private theorem rootLoop_spec
    (radicand : FloatLib.Numerics.FixedWord.UInt128) (steps : Nat)
    (state : RestoringRootState UInt64) (value : Nat)
    (hrep : RootRep64 state value)
    (hfit :
      value * place steps + digitsValue digitAt radicand steps < 2 ^ 106) :
    RootRep64 (rootLoop radicand steps state)
      (value * place steps + digitsValue digitAt radicand steps) :=
  loop_represents UInt64.toNat digitAt rootStep rootLoop (2 ^ 106)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    digit_lt_four rootStep_spec radicand steps state value hrep hfit

private theorem rootLoop_53_spec
    (radicand : FloatLib.Numerics.FixedWord.UInt128)
    (hfit : radicand.toNat < 2 ^ 106) :
    RootRep64
      (rootLoop radicand 53 { root := 0, remainder := 0 })
      radicand.toNat := by
  have hinitial :
      RootRep64 ({ root := 0, remainder := 0 } : RestoringRootState UInt64) 0 := by
    simp [RestoringRootState.Represents]
  have hloop :=
    rootLoop_spec radicand 53 { root := 0, remainder := 0 } 0
      hinitial
  rw [zero_mul, zero_add, digitsValue_53_eq_toNat radicand hfit] at hloop
  exact hloop hfit

/-- When the shifted significand fits in 106 bits, the restoring root returns the integer square
root and its remainder. -/
theorem rootAndRemainder_spec
    (mantissa : UInt64) (shift : Nat)
    (hpositive : 0 < shift)
    (hshift : shift < 128)
    (hfit : mantissa.toNat <<< shift < 2 ^ 106) :
    let state := rootAndRemainder mantissa shift
    state.root.toNat = Nat.sqrt (mantissa.toNat <<< shift) ∧
      state.remainder.toNat =
        (mantissa.toNat <<< shift) -
          Nat.sqrt (mantissa.toNat <<< shift) *
            Nat.sqrt (mantissa.toNat <<< shift) := by
  let radicand := shiftedRadicand mantissa shift
  let state := rootLoop radicand 53 { root := 0, remainder := 0 }
  have hradicand :
      radicand.toNat = mantissa.toNat <<< shift := by
    exact shiftedRadicand_toNat mantissa shift hpositive hshift
      (lt_trans hfit (Nat.pow_lt_pow_right (by decide) (by omega)))
  have hradicandFit : radicand.toNat < 2 ^ 106 := by
    rw [hradicand]
    exact hfit
  have hrep : RootRep64 state radicand.toNat :=
    rootLoop_53_spec radicand hradicandFit
  change
    state.root.toNat = Nat.sqrt (mantissa.toNat <<< shift) ∧
      state.remainder.toNat =
        (mantissa.toNat <<< shift) -
          Nat.sqrt (mantissa.toNat <<< shift) *
            Nat.sqrt (mantissa.toNat <<< shift)
  simpa [hradicand] using
    RestoringRootState.sqrt_spec UInt64.toNat hrep

/-! ## Binary64 scaling and rounding specification -/

private theorem sqrt_target_exponent
    (leading scale : Nat) (hleading : leading < 53) :
    let inputExponent := Int.ofNat scale - 1074
    let position := leading + scale
    let rootExponent := Int.ofNat ((position + 972) / 2) - 1023
    min (inputExponent.ediv 2)
        ((FloatFormat.toModel FloatFormat.binary64).targetExponent
          ((Float.Model.totalExponent (2 ^ leading) inputExponent + 1).ediv 2)) =
      rootExponent - 52 := by
  dsimp only
  norm_num [Float.Model.Format.targetExponent, Float.Model.Format.minExponent,
    Float.Model.Format.mantissaBits, FloatFormat.toModel, FloatFormat.binary64,
    Float.Model.totalExponent, Nat.log2_two_pow]
  exact
    FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.target_exponent
      leading scale 1074 972 1023 52
      (by omega) (by decide) (by decide) (by decide) (by decide)

private theorem sqrt_shift_amount
    (leading scale : Nat) (hleading : leading < 53) :
    let inputExponent := Int.ofNat scale - 1074
    let position := leading + scale
    let rootExponent := Int.ofNat ((position + 972) / 2) - 1023
    (inputExponent - 2 * (rootExponent - 52)).toNat =
      if position % 2 = 0 then 104 - leading else 105 - leading := by
  dsimp only
  simpa using
    FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.shift_amount_of_even_offset
      leading scale 1074 972 1023 52 (by omega) (by decide) (by decide)

private def sqrtPositiveFiniteSpec (mantissa scale : Nat) : UInt64 :=
  let leading := mantissa.log2
  let position := leading + scale
  let shift := if position % 2 == 0 then 104 - leading else 105 - leading
  let scaledMantissa := mantissa <<< shift
  let root := Nat.sqrt scaledMantissa
  let remainder := scaledMantissa - root * root
  let roundedRoot := if remainder ≤ root then root else root + 1
  let carry := roundedRoot == Model.pow2 53
  let encodedExponent := (position + 972) / 2 + if carry then 1 else 0
  let roundedMantissa := if carry then Model.pow2 52 else roundedRoot
  packFieldsWord false (UInt64.ofNat encodedExponent)
    (UInt64.ofNat (roundedMantissa - Model.pow2 52))

/-! ## Native-core refinement -/

private theorem packRoundedSquareRoot (mantissa scale : UInt64) :
  let nativeLeading := mantissa.log2;
  let nativePosition := nativeLeading + scale;
  let nativeShift := if (nativePosition % 2 == 0) = true then 104 - nativeLeading.toNat else 105
    - nativeLeading.toNat;
  let nativeState := rootAndRemainder mantissa nativeShift;
  let nativeRoot := nativeState.root;
  let nativeRemainder := nativeState.remainder;
  let nativeRounded := if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1;
  let nativeCarry := nativeRounded == 9007199254740992;
  let nativeEncoded := (nativePosition + 972) / 2 + if nativeCarry = true then 1 else 0;
  let nativeRoundedMantissa := if nativeCarry = true then 4503599627370496 else nativeRounded;
  let nativeFraction := nativeRoundedMantissa - 4503599627370496;
  let genericLeading := mantissa.toNat.log2;
  let genericPosition := genericLeading + scale.toNat;
  let genericShift := if (genericPosition % 2 == 0) = true then 104 - genericLeading else 105 -
    genericLeading;
  let genericScaled := mantissa.toNat <<< genericShift;
  let genericRoot := genericScaled.sqrt;
  let genericRemainder := genericScaled - genericRoot * genericRoot;
  let genericRounded := if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1;
  let genericCarry := genericRounded == pow2 53;
  let genericEncoded := (genericPosition + 972) / 2 + if genericCarry = true then 1 else 0;
  let genericRoundedMantissa := if genericCarry = true then pow2 52 else genericRounded;
  let genericFraction := genericRoundedMantissa - pow2 52;
  mantissa.toNat ≠ 0 →
    nativeLeading.toNat = genericLeading →
      genericLeading < 53 →
        genericPosition ≤ 2097 →
          nativePosition.toNat = genericPosition →
            nativeRoot.toNat = genericRoot ∧ nativeRemainder.toNat = genericRemainder →
                (nativeRemainder ≤ nativeRoot ↔ genericRemainder ≤ genericRoot) →
                  genericRoot < 2 ^ 53 →
                    packFieldsWord false nativeEncoded nativeFraction =
                      packFieldsWord false (UInt64.ofNat genericEncoded) (UInt64.ofNat
                        genericFraction) := by
  intro nativeLeading nativePosition nativeShift nativeState nativeRoot nativeRemainder
    nativeRounded nativeCarry nativeEncoded nativeRoundedMantissa nativeFraction genericLeading
    genericPosition genericShift genericScaled genericRoot genericRemainder genericRounded
    genericCarry genericEncoded genericRoundedMantissa genericFraction hmantissaNat hleading
    hleadingLt hpositionLe hposition hstate hremainderLe hrootLt
  have hroot := hstate.1
  have hrounded : nativeRounded.toNat = genericRounded := by
    dsimp only [nativeRounded, genericRounded]
    by_cases hle : nativeRemainder ≤ nativeRoot
    · rw [ite_eq_left hle, ite_eq_left (hremainderLe.mp hle), hroot]
    · rw [ite_eq_right hle, ite_eq_right ((not_congr hremainderLe).mp hle)]
      have hrootSuccFit : genericRoot + 1 < 2 ^ 64 := by
        have hpow : 2 ^ 53 < 2 ^ 64 :=
          Nat.pow_lt_pow_right (by decide) (by omega)
        omega
      rw [UInt64.toNat_add, hroot]
      change (genericRoot + 1) % 2 ^ 64 = genericRoot + 1
      exact Nat.mod_eq_of_lt hrootSuccFit
  have hcarry : nativeCarry = genericCarry := by
    dsimp only [nativeCarry, genericCarry]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [← UInt64.toNat_inj]
    simp [hrounded, Model.pow2_eq_two_pow]
  have hpositionAdd :
      (nativePosition + 972).toNat = genericPosition + 972 := by
    rw [UInt64.toNat_add, hposition]
    change (genericPosition + 972) % 2 ^ 64 = genericPosition + 972
    apply Nat.mod_eq_of_lt
    omega
  have hpositionHalf :
      ((nativePosition + 972) / 2).toNat =
        (genericPosition + 972) / 2 := by
    rw [UInt64.toNat_div, hpositionAdd]
    rfl
  have hencoded : nativeEncoded.toNat = genericEncoded := by
    dsimp only [nativeEncoded, genericEncoded]
    rw [hcarry]
    by_cases hgenericCarry : genericCarry = true
    · simp only [hgenericCarry, ite_true]
      have hencodedFit :
          (genericPosition + 972) / 2 + 1 < 2 ^ 64 := by
        omega
      rw [UInt64.toNat_add, hpositionHalf]
      change
        ((genericPosition + 972) / 2 + 1) % 2 ^ 64 =
          (genericPosition + 972) / 2 + 1
      exact Nat.mod_eq_of_lt hencodedFit
    · simp [Bool.eq_false_of_not_eq_true hgenericCarry, hpositionHalf]
  have hpowLeading : 2 ^ genericLeading ≤ mantissa.toNat := by
    dsimp only [genericLeading]
    exact (Nat.le_log2 hmantissaNat).mp le_rfl
  have hscaledExponentLower :
      104 ≤ genericLeading + genericShift := by
    dsimp only [genericShift]
    split <;> omega
  have hscaledLower : 2 ^ 104 ≤ genericScaled := by
    dsimp only [genericScaled]
    rw [Nat.shiftLeft_eq]
    calc
      2 ^ 104 ≤ 2 ^ (genericLeading + genericShift) :=
        Nat.pow_le_pow_right (by decide) hscaledExponentLower
      _ = 2 ^ genericLeading * 2 ^ genericShift := Nat.pow_add ..
      _ ≤ mantissa.toNat * 2 ^ genericShift :=
        Nat.mul_le_mul_right (2 ^ genericShift) hpowLeading
  have hrootLower : 2 ^ 52 ≤ genericRoot := by
    dsimp only [genericRoot]
    rw [Nat.le_sqrt, ← Nat.pow_add]
    norm_num
    exact hscaledLower
  have hroundedLower : 2 ^ 52 ≤ genericRounded := by
    dsimp only [genericRounded]
    split <;> omega
  have hroundedMantissa :
      nativeRoundedMantissa.toNat = genericRoundedMantissa := by
    dsimp only [nativeRoundedMantissa, genericRoundedMantissa]
    rw [hcarry]
    by_cases hgenericCarry : genericCarry = true
    · simp [hgenericCarry, Model.pow2_eq_two_pow]
    · simp [Bool.eq_false_of_not_eq_true hgenericCarry, hrounded]
  have hroundedMantissaLower :
      2 ^ 52 ≤ genericRoundedMantissa := by
    dsimp only [genericRoundedMantissa]
    split
    · norm_num [Model.pow2_eq_two_pow]
    · exact hroundedLower
  have hroundedMantissaWordLower :
      (0x0010000000000000 : UInt64) ≤ nativeRoundedMantissa := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hroundedMantissa]
    exact hroundedMantissaLower
  have hfraction : nativeFraction.toNat = genericFraction := by
    dsimp only [nativeFraction, genericFraction]
    rw [UInt64.toNat_sub_of_le _ _ hroundedMantissaWordLower,
      hroundedMantissa]
    change
      genericRoundedMantissa - 4503599627370496 =
        genericRoundedMantissa - Model.pow2 52
    norm_num [Model.pow2_eq_two_pow]
  have hencodedWord :
      nativeEncoded = UInt64.ofNat genericEncoded := by
    have hgenericEncodedFit : genericEncoded < 2 ^ 64 := by
      dsimp only [genericEncoded]
      split <;> omega
    apply UInt64.toNat_inj.mp
    rw [hencoded]
    exact (UInt64.toNat_ofNat_of_lt hgenericEncodedFit).symm
  have hgenericRoundedUpper : genericRounded ≤ 2 ^ 53 := by
    dsimp only [genericRounded]
    split <;> omega
  have hgenericRoundedMantissaUpper :
      genericRoundedMantissa ≤ 2 ^ 53 := by
    dsimp only [genericRoundedMantissa]
    split
    · norm_num [Model.pow2_eq_two_pow]
    · exact hgenericRoundedUpper
  have hfractionWord :
      nativeFraction = UInt64.ofNat genericFraction := by
    have hgenericFractionFit : genericFraction < 2 ^ 64 := by
      exact (Nat.sub_le _ _).trans_lt
        (hgenericRoundedMantissaUpper.trans_lt (by norm_num))
    apply UInt64.toNat_inj.mp
    rw [hfraction]
    exact (UInt64.toNat_ofNat_of_lt hgenericFractionFit).symm
  rw [hencodedWord, hfractionWord]

private theorem sqrtPositiveFiniteCore_eq_spec
    (mantissa scale : UInt64)
    (hmantissa : mantissa ≠ 0)
    (hmantissaBound : mantissa.toNat < 2 ^ 53)
    (hscaleBound : scale.toNat ≤ 2045) :
    sqrtPositiveFiniteCore mantissa scale =
      sqrtPositiveFiniteSpec mantissa.toNat scale.toNat := by
  let nativeLeading := mantissa.log2
  let nativePosition := nativeLeading + scale
  let nativeShift :=
    if nativePosition % 2 == 0 then
      104 - nativeLeading.toNat
    else
      105 - nativeLeading.toNat
  let nativeState := rootAndRemainder mantissa nativeShift
  let nativeRoot := nativeState.root
  let nativeRemainder := nativeState.remainder
  let nativeRounded :=
    if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1
  let nativeCarry := nativeRounded == 0x0020000000000000
  let nativeEncoded :=
    (nativePosition + 972) / 2 + if nativeCarry then 1 else 0
  let nativeRoundedMantissa :=
    if nativeCarry then 0x0010000000000000 else nativeRounded
  let nativeFraction := nativeRoundedMantissa - 0x0010000000000000
  let genericLeading := mantissa.toNat.log2
  let genericPosition := genericLeading + scale.toNat
  let genericShift :=
    if genericPosition % 2 == 0 then
      104 - genericLeading
    else
      105 - genericLeading
  let genericScaled := mantissa.toNat <<< genericShift
  let genericRoot := Nat.sqrt genericScaled
  let genericRemainder := genericScaled - genericRoot * genericRoot
  let genericRounded :=
    if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1
  let genericCarry := genericRounded == Model.pow2 53
  let genericEncoded :=
    (genericPosition + 972) / 2 + if genericCarry then 1 else 0
  let genericRoundedMantissa :=
    if genericCarry then Model.pow2 52 else genericRounded
  let genericFraction := genericRoundedMantissa - Model.pow2 52
  change
    packFieldsWord false nativeEncoded nativeFraction =
      packFieldsWord false (UInt64.ofNat genericEncoded)
        (UInt64.ofNat genericFraction)
  have hmantissaNat : mantissa.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hmantissa
  have hleading : nativeLeading.toNat = genericLeading := by
    dsimp only [nativeLeading, genericLeading]
    exact FloatLib.Numerics.FixedWord.log2_toNat mantissa
  have hleadingLt : genericLeading < 53 := by
    dsimp only [genericLeading]
    rw [Nat.log2_lt hmantissaNat]
    exact hmantissaBound
  have hpositionBound : genericPosition < 2 ^ 64 := by
    dsimp only [genericPosition]
    omega
  have hpositionLe : genericPosition ≤ 2097 := by
    dsimp only [genericPosition]
    omega
  have hposition : nativePosition.toNat = genericPosition := by
    dsimp only [nativePosition]
    rw [UInt64.toNat_add, hleading, Nat.mod_eq_of_lt hpositionBound]
  have hpositionEven :
      nativePosition % 2 = 0 ↔ genericPosition % 2 = 0 := by
    constructor
    · intro h
      have hnat := congrArg UInt64.toNat h
      rw [UInt64.toNat_mod, hposition] at hnat
      norm_num at hnat ⊢
      exact hnat
    · intro h
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, hposition]
      norm_num
      exact h
  have hparity :
      (nativePosition % 2 == 0) = (genericPosition % 2 == 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using hpositionEven
  have hshift : nativeShift = genericShift := by
    dsimp only [nativeShift, genericShift]
    rw [hparity, hleading]
  have hshiftPositive : 0 < genericShift := by
    dsimp only [genericShift]
    split <;> omega
  have hshiftLt : genericShift < 128 := by
    dsimp only [genericShift]
    split <;> omega
  have hscaledExponentUpper :
      genericLeading + 1 + genericShift ≤ 106 := by
    dsimp only [genericShift]
    split <;> omega
  have hscaledFit : genericScaled < 2 ^ 106 := by
    dsimp only [genericScaled]
    exact lt_of_lt_of_le
      (Nat.shiftLeft_lt Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) hscaledExponentUpper)
  have hstate :
      nativeRoot.toNat = genericRoot ∧
        nativeRemainder.toNat = genericRemainder := by
    simpa only [nativeRoot, nativeRemainder, nativeState, genericRoot,
      genericRemainder, genericScaled, hshift] using
      rootAndRemainder_spec mantissa nativeShift
        (by simpa [hshift] using hshiftPositive)
        (by simpa [hshift] using hshiftLt)
        (by simpa [hshift] using hscaledFit)
  have hroot := hstate.1
  have hremainder := hstate.2
  have hremainderLe :
      nativeRemainder ≤ nativeRoot ↔ genericRemainder ≤ genericRoot := by
    rw [UInt64.le_iff_toNat_le, hremainder, hroot]
  have hrootLt : genericRoot < 2 ^ 53 := by
    dsimp only [genericRoot]
    rw [Nat.sqrt_lt, ← Nat.pow_add]
    norm_num
    exact hscaledFit
  exact packRoundedSquareRoot (mantissa := mantissa) (scale := scale) hmantissaNat hleading
    hleadingLt hpositionLe hposition hstate hremainderLe hrootLt

/-! ## Unpacked binary64 semantic refinement -/

/-- On every positive finite binary64 value, including subnormals, the native square root agrees
with the unpacked model after packing. -/
theorem sqrt_eq_generic_of_positive_finite
    (x : Value)
    (hexponent :
      Model.expField x ≠ FloatFormat.expAllOnesNat FloatFormat.binary64)
    (hnonzero : Model.isZero x = false)
    (hsign : Model.signBit x = false) :
    ofUInt64
        (sqrtPositiveFinite
          (expField (toUInt64 x))
          (fracField (toUInt64 x))) =
      Model.ofModel FloatFormat.binary64 (
        Float.Model.UnpackedFloat.sqrt
          (FloatFormat.toModel FloatFormat.binary64)
          (Model.toModel x)) := by
  let bits := toUInt64 x
  let exponent := expField bits
  let fraction := fracField bits
  let mantissa := finiteMantissa exponent fraction
  let scale := finiteScale exponent
  have hfraction : fraction.toNat < 2 ^ 52 := by
    simpa only [fraction, bits] using fracField_lt x
  have hexponentNative : exponent ≠ 0x7ff := by
    intro h
    apply hexponent
    rw [← expField_toNat x]
    simp only [bits, exponent, h]
    decide
  have hmantissa : mantissa ≠ 0 := by
    intro h
    have hmantissaNat : mantissa.toNat = 0 := congrArg UInt64.toNat h
    rw [finiteMantissa_toNat exponent fraction hfraction] at hmantissaNat
    by_cases hexponentZero : exponent = 0
    · simp only [hexponentZero, ite_true] at hmantissaNat
      have hfractionZero : fraction = 0 := by
        apply UInt64.toNat_inj.mp
        simpa using hmantissaNat
      have hzero : Model.isZero x = true := by
        change Model.IEEE.isZero x = true
        unfold Model.IEEE.isZero
        rw [Bool.and_eq_true]
        constructor
        · apply beq_iff_eq.mpr
          rw [← expField_toNat x]
          simp [bits, exponent, hexponentZero]
        · apply beq_iff_eq.mpr
          rw [← fracField_toNat x]
          simp [bits, fraction, hfractionZero]
      rw [hzero] at hnonzero
      contradiction
    · simp only [hexponentZero, ite_false] at hmantissaNat
      simp [Model.pow2_eq_two_pow] at hmantissaNat
  have hsignNative : signBit bits = false := by
    simpa only [bits, signBit_eq] using hsign
  have hmantissaNat : mantissa.toNat ≠ 0 := by
    intro h
    apply hmantissa
    apply UInt64.toNat_inj.mp
    simpa using h
  have hscale :
      FiniteKernel.scale exponent.toNat = scale.toNat := by
    rw [finiteScale_toNat]
    unfold FiniteKernel.scale
    simp only [beq_iff_eq]
    by_cases h : exponent = 0
    · simp [h]
    · have hnat : exponent.toNat ≠ 0 := by
        intro hz
        apply h
        apply UInt64.toNat_inj.mp
        simpa using hz
      simp [h, hnat]
  have hdecode :
      Model.toDyadicOption x =
        some
          ({ negative := false
             significand := mantissa.toNat
             exponent := Int.ofNat scale.toNat - 1074 } : Numerics.Dyadic) := by
    rw [FiniteKernel.toDyadic_eq_decode, ← decode_eq]
    unfold decodeOption
    simp only [bits, exponent, hexponentNative, beq_iff_eq,
      ite_false, hsignNative]
    change
      (some ({
        sign := false
        exponent := exponent.toNat
        mantissa := mantissa.toNat } : FiniteKernel.Components)).map
          (FiniteKernel.Components.toDyadic FloatFormat.binary64) =
        some
          ({ negative := false
             significand := mantissa.toNat
             exponent := Int.ofNat scale.toNat - 1074 } : Numerics.Dyadic)
    simp only [Option.map_some, FiniteKernel.Components.toDyadic,
      hmantissaNat, beq_iff_eq, ite_false]
    rw [FiniteKernel.exponent_eq_scale, hscale]
    rw [show FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 by
      decide]
    norm_num
  have htoModel :
      Model.toModel x =
        .finite .positive mantissa.toNat (Int.ofNat scale.toNat - 1074)
          (Nat.pos_of_ne_zero hmantissaNat) := by
    have hieeeDecode :
        Model.ieeeToDyadicOption x =
          some
            ({ negative := false
               significand := mantissa.toNat
               exponent := Int.ofNat scale.toNat - 1074 } : Numerics.Dyadic) := by
      simpa [Model.toDyadicOption, show FloatFormat.binary64.isIEEE = true by decide]
        using hdecode
    simpa [Model.modelSign] using
      Model.toModel_eq_finite_of_ieeeToDyadicOption_eq_some
        x false mantissa.toNat (Int.ofNat scale.toNat - 1074)
        hmantissaNat hieeeDecode
  rw [htoModel]
  have hmantissaBound : mantissa.toNat < 2 ^ 53 :=
    finiteMantissa_lt exponent fraction hfraction
  have hexponentLt : exponent.toNat < 2 ^ 11 := by
    change Model.expField x < 2 ^ 11
    simpa only [show FloatFormat.binary64.expWidth = 11 by decide] using
      Model.expField_lt_pow2 x
  have hscaleBound : scale.toNat ≤ 2045 :=
    finiteScale_le exponent hexponentLt hexponentNative
  have hleading : mantissa.toNat.log2 < 53 := by
    rw [Nat.log2_lt hmantissaNat]
    exact hmantissaBound
  have hfracWidth : FloatFormat.binary64.fracWidth = 52 := by decide
  have hbias : FloatFormat.binary64.bias = 1023 := by decide
  rw [Model.ofModel_sqrt_finite_positive_eq_ofFields FloatFormat.binary64 mantissa.toNat
    (if (mantissa.toNat.log2 + scale.toNat) % 2 = 0 then 104 - mantissa.toNat.log2
      else 105 - mantissa.toNat.log2)
    ((mantissa.toNat.log2 + scale.toNat + 972) / 2) (Int.ofNat scale.toNat - 1074)
    (Nat.pos_of_ne_zero hmantissaNat)
    (by rw [hfracWidth]; split <;> omega) (by rw [hfracWidth]; split <;> omega)
    (by omega) (by rw [hbias]; omega)
    (by simpa only [hfracWidth, hbias, Float.Model.totalExponent, Nat.log2_two_pow,
      Int.ofNat_eq_natCast, Nat.cast_ofNat] using
        sqrt_target_exponent mantissa.toNat.log2 scale.toNat hleading)
    (by simpa only [hfracWidth, hbias, Int.ofNat_eq_natCast, Nat.cast_ofNat] using
      sqrt_shift_amount mantissa.toNat.log2 scale.toNat hleading)]
  change ofUInt64 (sqrtPositiveFiniteCore mantissa scale) = _
  rw [sqrtPositiveFiniteCore_eq_spec mantissa scale hmantissa hmantissaBound hscaleBound]
  simp only [sqrtPositiveFiniteSpec, beq_iff_eq, packFieldsWord_eq_ofNat, hfracWidth]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Product.Runtime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Verified fixed-limb significand products

`mul128_toNat` proves exact `128 × 128 → 256` multiplication using the `mul64_toNat` theorem
from `Core.Proof.UInt128`. The addition theorems reconstruct the exact sum from its low limbs
and outgoing carry. The `UInt256` lemmas describe widening, projection, and leading-bit selection.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-- Embedding a two-limb value in four limbs preserves its mathematical value. -/
@[simp, grind =] theorem UInt256.toNat_ofUInt128 (value : UInt128) :
    (UInt256.ofUInt128 value).toNat = value.toNat := by
  simp [UInt256.ofUInt128, UInt256.toNat, UInt128.toNat]

/-- The generic widening shuffle has the expected unbounded value for in-range shifts. -/
theorem UInt256.toNat_ofUInt128ShiftedLeft (value : UInt128) (shift : Nat)
    (hlower : 64 < shift) (hupper : shift < 128) :
    (UInt256.ofUInt128ShiftedLeft value shift).toNat = value.toNat <<< shift := by
  have hinnerPos : 0 < shift - 64 := by omega
  have hinnerLt : shift - 64 < 64 := by omega
  have hcomplementPos : 0 < 64 - (shift - 64) := by omega
  have hcomplementLt : 64 - (shift - 64) < 64 := by omega
  have hcomplement : 64 - (64 - (shift - 64)) = shift - 64 := by omega
  have hlow :=
    shiftLeftLowBits_toNat value.lo (64 - (shift - 64)) hcomplementPos hcomplementLt
  have hmiddle :=
    shiftedPair_toNat value.lo value.hi (64 - (shift - 64)) hcomplementPos hcomplementLt
  have hhigh :=
    shiftRight_toNat value.hi (64 - (shift - 64)) hcomplementLt
  rw [hcomplement] at hlow hmiddle
  rw [Nat.shiftRight_eq_div_pow] at hhigh
  unfold UInt256.ofUInt128ShiftedLeft UInt256.toNat
  dsimp only
  rw [hlow, UInt64.or_comm, hmiddle, hhigh]
  unfold UInt128.toNat
  have hlo := (Nat.mod_add_div value.lo.toNat (2 ^ (64 - (shift - 64)))).symm
  have hhi := (Nat.mod_add_div value.hi.toNat (2 ^ (64 - (shift - 64)))).symm
  have hpow : 2 ^ (64 - (shift - 64)) * 2 ^ (shift - 64) = 2 ^ 64 := by
    rw [← pow_add]
    congr 1
    omega
  have hshift : 2 ^ shift = 2 ^ (shift - 64) * 2 ^ 64 := by
    rw [← pow_add]
    congr 1
    omega
  rw [Nat.shiftLeft_eq, hshift]
  set inner := 2 ^ (shift - 64) with hinner
  set complement := 2 ^ (64 - (shift - 64)) with hcomplementDef
  set rlo := value.lo.toNat % complement
  set qlo := value.lo.toNat / complement
  set rhi := value.hi.toNat % complement
  set qhi := value.hi.toNat / complement
  rw [hlo, hhi]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num,
    show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 by norm_num, ← hpow]
  simp only [UInt64.toNat_zero, zero_add]
  ring

/-- The low-half projection is exact whenever the four-limb value fits in two limbs. -/
theorem UInt256.low128_toNat_of_lt (value : UInt256)
    (hvalue : value.toNat < 2 ^ 128) :
    value.low128.toNat = value.toNat := by
  have hlimb2Nat : value.limb2.toNat = 0 := by
    unfold UInt256.toNat at hvalue
    omega
  have hlimb3Nat : value.limb3.toNat = 0 := by
    unfold UInt256.toNat at hvalue
    omega
  have hlimb2 : value.limb2 = 0 := by
    apply UInt64.toNat_inj.mp
    simpa using hlimb2Nat
  have hlimb3 : value.limb3 = 0 := by
    apply UInt64.toNat_inj.mp
    simpa using hlimb3Nat
  simp [UInt256.low128, UInt256.toNat, UInt128.toNat, hlimb2, hlimb3]

/-- A four-limb value has mathematical value zero exactly when every limb is zero. -/
@[simp, grind =] theorem UInt256.toNat_eq_zero_iff (value : UInt256) :
    value.toNat = 0 ↔ value = ⟨0, 0, 0, 0⟩ := by
  cases value
  simp [UInt256.toNat, uint64_toNat_eq_zero]
  tauto

/-- The natural-number interpretation determines every limb of a four-word value. -/
theorem UInt256.toNat_injective : Function.Injective UInt256.toNat := by
  intro x y hvalue
  cases x with
  | mk x3 x2 x1 x0 =>
    cases y with
    | mk y3 y2 y1 y0 =>
      have hx0 := x0.toNat_lt
      have hx1 := x1.toNat_lt
      have hx2 := x2.toNat_lt
      have hx3 := x3.toNat_lt
      have hy0 := y0.toNat_lt
      have hy1 := y1.toNat_lt
      have hy2 := y2.toNat_lt
      have hy3 := y3.toNat_lt
      simp only [UInt256.toNat] at hvalue
      have h0 : x0.toNat = y0.toNat := by omega
      have h1 : x1.toNat = y1.toNat := by omega
      have h2 : x2.toNat = y2.toNat := by omega
      have h3 : x3.toNat = y3.toNat := by omega
      simp only [UInt256.mk.injEq]
      exact ⟨UInt64.toNat_inj.mp h3, UInt64.toNat_inj.mp h2,
        UInt64.toNat_inj.mp h1, UInt64.toNat_inj.mp h0⟩

/-- Native addition with carry represents the corresponding exact natural-number sum. -/
theorem add64_toNat (x y : UInt64) :
    let result := add64 x y
    result.value.toNat + result.carry.toNat * 2 ^ 64 =
      x.toNat + y.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  dsimp only [add64]
  split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h <;>
    simp only [UInt64.toNat_add, UInt64.reduceToNat] <;> omega

/-- The carry returned by `add64` is always either zero or one. -/
theorem add64_carry_le_one (x y : UInt64) :
    (add64 x y).carry.toNat ≤ 1 := by
  simp [add64]
  split <;> simp

/-- `addCarry64` represents exact addition. -/
theorem addCarry64_toNat (x y carry : UInt64) :
    let result := addCarry64 x y carry
    result.value.toNat + result.carry.toNat * 2 ^ 64 =
      x.toNat + y.toNat + carry.toNat := by
  have hfirst := add64_toNat x y
  have hsecond := add64_toNat (add64 x y).value carry
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hcarry := carry.toNat_lt
  have hvalue := (add64 x y).value.toNat_lt
  dsimp only at hfirst hsecond
  have hsum : ((add64 x y).carry + (add64 (add64 x y).value carry).carry).toNat =
      (add64 x y).carry.toNat + (add64 (add64 x y).value carry).carry.toNat := by
    rw [UInt64.toNat_add]
    omega
  simp only [addCarry64, hsum]
  linarith

/-- The outgoing carry from `addCarry64` is a bit when the incoming carry is a bit. -/
theorem addCarry64_carry_le_one (x y carry : UInt64)
    (hcarry : carry.toNat ≤ 1) :
    (addCarry64 x y carry).carry.toNat ≤ 1 := by
  have hexact := addCarry64_toNat x y carry
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  dsimp only at hexact
  omega

/-- `add128` represents exact addition, including its carry above bit 127. -/
theorem add128_toNat (x y : UInt128) :
    let result := add128 x y
    result.value.toNat + result.carry.toNat * 2 ^ 128 =
      x.toNat + y.toNat := by
  have hlow := addCarry64_toNat x.lo y.lo 0
  have hhigh := addCarry64_toNat x.hi y.hi (addCarry64 x.lo y.lo 0).carry
  have := x.lo.toNat_lt
  have := y.lo.toNat_lt
  simp only [add128, UInt128.toNat, UInt64.toNat_zero] at *
  omega

/-- The carry returned by `add128` is zero or one. -/
theorem add128_carry_le_one (x y : UInt128) :
    (add128 x y).carry.toNat ≤ 1 := by
  let low := addCarry64 x.lo y.lo 0
  have hlowCarry : low.carry.toNat ≤ 1 := by
    simpa [low] using addCarry64_carry_le_one x.lo y.lo 0 (by simp)
  simpa [add128, low] using
    addCarry64_carry_le_one x.hi y.hi low.carry hlowCarry

/-- A 128-bit addition has no carry when its mathematical sum fits in 128 bits. -/
theorem add128_carry_eq_zero_of_lt (x y : UInt128)
    (hfit : x.toNat + y.toNat < 2 ^ 128) :
    (add128 x y).carry = 0 := by
  have hexact := add128_toNat x y
  have hcarry := add128_carry_le_one x y
  dsimp only at hexact hcarry
  apply UInt64.toNat_inj.mp
  simp only [UInt64.reduceToNat]
  omega

/-- The value limbs of `add128` contain the exact sum when its carry is zero. -/
theorem add128_value_toNat_of_carry_zero (x y : UInt128)
    (hcarry : (add128 x y).carry = 0) :
    (add128 x y).value.toNat = x.toNat + y.toNat := by
  have hexact := add128_toNat x y
  dsimp only at hexact ⊢
  simp only [hcarry, UInt64.toNat_zero, Nat.reducePow, zero_mul, add_zero] at hexact
  exact hexact

/--
The low two limbs of `add128` contain the ordinary sum whenever that sum fits in 128 bits.

This is the common refinement fact needed by fixed-limb midpoint, significand, and remainder
kernels. Keeping it next to `add128` avoids backend-local copies of the same carry argument.
-/
theorem add128_value_toNat_of_lt (x y : UInt128)
    (hfit : x.toNat + y.toNat < 2 ^ 128) :
    (add128 x y).value.toNat = x.toNat + y.toNat :=
  add128_value_toNat_of_carry_zero x y
    (add128_carry_eq_zero_of_lt x y hfit)

/-- `add256` represents exact addition, including its carry above bit 255. -/
theorem add256_toNat (x y : UInt256) :
    let result := add256 x y
    result.value.toNat + result.carry.toNat * 2 ^ 256 =
      x.toNat + y.toNat := by
  have h0 := addCarry64_toNat x.limb0 y.limb0 0
  have h1 := addCarry64_toNat x.limb1 y.limb1 (addCarry64 x.limb0 y.limb0 0).carry
  have h2 := addCarry64_toNat x.limb2 y.limb2
    (addCarry64 x.limb1 y.limb1 (addCarry64 x.limb0 y.limb0 0).carry).carry
  have h3 := addCarry64_toNat x.limb3 y.limb3
    (addCarry64 x.limb2 y.limb2
      (addCarry64 x.limb1 y.limb1 (addCarry64 x.limb0 y.limb0 0).carry).carry).carry
  have := x.limb0.toNat_lt
  have := y.limb0.toNat_lt
  have := x.limb1.toNat_lt
  have := y.limb1.toNat_lt
  have := x.limb2.toNat_lt
  have := y.limb2.toNat_lt
  simp only [add256, UInt256.toNat, UInt64.toNat_zero] at *
  omega

/-- The value limbs of `add256` contain the exact sum when its carry is zero. -/
theorem add256_value_toNat_of_carry_zero (x y : UInt256)
    (hcarry : (add256 x y).carry = 0) :
    (add256 x y).value.toNat = x.toNat + y.toNat := by
  have hexact := add256_toNat x y
  dsimp only at hexact ⊢
  simp only [hcarry, UInt64.toNat_zero, Nat.reducePow, zero_mul, add_zero] at hexact
  exact hexact

/-- Native four-limb leading-bit selection agrees with `Nat.log2`. -/
@[simp, grind =] theorem UInt256.log2_toNat (value : UInt256) :
    value.log2 = value.toNat.log2 := by
  unfold UInt256.log2
  by_cases h3 : value.limb3 = 0
  · have h3test : ¬value.limb3 != 0 := by
      simp [h3]
    rw [ite_eq_right h3test]
    by_cases h2 : value.limb2 = 0
    · have h2test : ¬value.limb2 != 0 := by
        simp [h2]
      rw [ite_eq_right h2test]
      by_cases h1 : value.limb1 = 0
      · have h1test : ¬value.limb1 != 0 := by
          simp [h1]
        rw [ite_eq_right h1test,
          FloatLib.Numerics.FixedWord.log2_toNat]
        simp [UInt256.toNat, h3, h2, h1]
      · have h1test : value.limb1 != 0 := by
          simp [h1]
        rw [ite_eq_left h1test,
          FloatLib.Numerics.FixedWord.log2_toNat]
        let low := value.limb0.toNat
        have hlow : low < 2 ^ 64 := by
          dsimp [low]
          exact value.limb0.toNat_lt
        have hhigh : value.limb1.toNat ≠ 0 := by
          intro hzero
          exact h1 (UInt64.toNat_inj.mp (by simpa using hzero))
        have hlog :=
          log2_low_add_high_mul_pow
            low value.limb1.toNat 64 hlow hhigh
        simpa [UInt256.toNat, h3, h2, low] using hlog.symm
    · have h2test : value.limb2 != 0 := by
        simp [h2]
      rw [ite_eq_left h2test,
        FloatLib.Numerics.FixedWord.log2_toNat]
      let low :=
        value.limb0.toNat + value.limb1.toNat * 2 ^ 64
      have hlow : low < 2 ^ 128 := by
        dsimp [low]
        have h0 := value.limb0.toNat_lt
        have h1 := value.limb1.toNat_lt
        omega
      have hhigh : value.limb2.toNat ≠ 0 := by
        intro hzero
        exact h2 (UInt64.toNat_inj.mp (by simpa using hzero))
      have hlog :=
        log2_low_add_high_mul_pow
          low value.limb2.toNat 128 hlow hhigh
      simpa [UInt256.toNat, h3, low] using hlog.symm
  · have h3test : value.limb3 != 0 := by
      simp [h3]
    rw [ite_eq_left h3test,
      FloatLib.Numerics.FixedWord.log2_toNat]
    let low :=
      value.limb0.toNat +
        value.limb1.toNat * 2 ^ 64 +
        value.limb2.toNat * 2 ^ 128
    have hlow : low < 2 ^ 192 := by
      dsimp [low]
      have h0 := value.limb0.toNat_lt
      have h1 := value.limb1.toNat_lt
      have h2 := value.limb2.toNat_lt
      omega
    have hhigh : value.limb3.toNat ≠ 0 := by
      intro hzero
      exact h3 (UInt64.toNat_inj.mp (by simpa using hzero))
    have hlog :=
      log2_low_add_high_mul_pow
        low value.limb3.toNat 192 hlow hhigh
    simpa [UInt256.toNat, low] using hlog.symm

/-- Every four-word unsigned value lies below the first unrepresentable 256-bit integer. -/
theorem UInt256.toNat_lt (value : UInt256) :
    value.toNat < 2 ^ 256 := by
  unfold UInt256.toNat
  have h0 := value.limb0.toNat_lt
  have h1 := value.limb1.toNat_lt
  have h2 := value.limb2.toNat_lt
  have h3 := value.limb3.toNat_lt
  omega

/-- `mul128` represents the exact mathematical product of its operands. -/
@[simp, grind =] theorem mul128_toNat (x y : UInt128) :
    (mul128 x y).toNat = x.toNat * y.toNat := by
  let p00 := mul64 x.lo y.lo
  let p01 := mul64 x.lo y.hi
  let p10 := mul64 x.hi y.lo
  let p11 := mul64 x.hi y.hi
  let first1 := add64 p00.hi p01.lo
  let second1 := add64 first1.value p10.lo
  let carry1 := first1.carry + second1.carry
  let first2 := add64 p01.hi p10.hi
  let second2 := add64 first2.value p11.lo
  let third2 := add64 second2.value carry1
  let carry2 := first2.carry + second2.carry + third2.carry
  have hp00 : p00.lo.toNat + p00.hi.toNat * 2 ^ 64 = x.lo.toNat * y.lo.toNat :=
    mul64_toNat x.lo y.lo
  have hp01 : p01.lo.toNat + p01.hi.toNat * 2 ^ 64 = x.lo.toNat * y.hi.toNat :=
    mul64_toNat x.lo y.hi
  have hp10 : p10.lo.toNat + p10.hi.toNat * 2 ^ 64 = x.hi.toNat * y.lo.toNat :=
    mul64_toNat x.hi y.lo
  have hp11 : p11.lo.toNat + p11.hi.toNat * 2 ^ 64 = x.hi.toNat * y.hi.toNat :=
    mul64_toNat x.hi y.hi
  have hfirst1 : first1.value.toNat + first1.carry.toNat * 2 ^ 64 =
      p00.hi.toNat + p01.lo.toNat := add64_toNat p00.hi p01.lo
  have hsecond1 : second1.value.toNat + second1.carry.toNat * 2 ^ 64 =
      first1.value.toNat + p10.lo.toNat := add64_toNat first1.value p10.lo
  have hfirst2 : first2.value.toNat + first2.carry.toNat * 2 ^ 64 =
      p01.hi.toNat + p10.hi.toNat := add64_toNat p01.hi p10.hi
  have hsecond2 : second2.value.toNat + second2.carry.toNat * 2 ^ 64 =
      first2.value.toNat + p11.lo.toNat := add64_toNat first2.value p11.lo
  have hthird2 : third2.value.toNat + third2.carry.toNat * 2 ^ 64 =
      second2.value.toNat + carry1.toNat := add64_toNat second2.value carry1
  have := p00.hi.toNat_lt
  have := p01.lo.toNat_lt
  have := p10.lo.toNat_lt
  have := p01.hi.toNat_lt
  have := p10.hi.toNat_lt
  have := p11.lo.toNat_lt
  have := first1.value.toNat_lt
  have := first2.value.toNat_lt
  have := second2.value.toNat_lt
  have hcarry1 : carry1.toNat = first1.carry.toNat + second1.carry.toNat := by
    rw [UInt64.toNat_add]
    omega
  have hcarry2 : carry2.toNat =
      first2.carry.toNat + second2.carry.toNat + third2.carry.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add]
    omega
  have hexpand : x.toNat * y.toNat =
      x.lo.toNat * y.lo.toNat + (x.lo.toNat * y.hi.toNat + x.hi.toNat * y.lo.toNat) * 2 ^ 64 +
        x.hi.toNat * y.hi.toNat * 2 ^ 128 := by
    unfold UInt128.toNat
    ring
  have hcolumns : x.toNat * y.toNat =
      p00.lo.toNat + second1.value.toNat * 2 ^ 64 + third2.value.toNat * 2 ^ 128 +
        (p11.hi.toNat + carry2.toNat) * 2 ^ 192 := by
    rw [hexpand, hcarry2]
    omega
  have hbound : x.toNat * y.toNat < 2 ^ 256 :=
    calc x.toNat * y.toNat < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' x.toNat_lt y.toNat_lt
      _ = 2 ^ 256 := by norm_num
  have htopFit : p11.hi.toNat + carry2.toNat < 2 ^ 64 := by
    have hle : (p11.hi.toNat + carry2.toNat) * 2 ^ 192 ≤ x.toNat * y.toNat := by
      rw [hcolumns]
      exact Nat.le_add_left _ _
    have hlt : (p11.hi.toNat + carry2.toNat) * 2 ^ 192 < 2 ^ 64 * 2 ^ 192 :=
      calc (p11.hi.toNat + carry2.toNat) * 2 ^ 192 ≤ x.toNat * y.toNat := hle
        _ < 2 ^ 256 := hbound
        _ = 2 ^ 64 * 2 ^ 192 := by norm_num
    exact Nat.lt_of_mul_lt_mul_right hlt
  have htop : (p11.hi + carry2).toNat = p11.hi.toNat + carry2.toNat :=
    uint64_add_toNat_of_lt _ _ htopFit
  change p00.lo.toNat + second1.value.toNat * 2 ^ 64 + third2.value.toNat * 2 ^ 128 +
    (p11.hi + carry2).toNat * 2 ^ 192 = x.toNat * y.toNat
  rw [htop, hcolumns]

end FloatLib.Numerics.FixedWord

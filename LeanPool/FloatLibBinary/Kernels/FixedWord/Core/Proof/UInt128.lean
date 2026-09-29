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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof.Word
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Verified two-word values and exact wide multiplication

The natural-number meaning of `UInt128` is injective, and the native `64 × 64 → 128`
multiplication kernel computes the exact product through two 64-bit output limbs. These facts
are independent of any floating-point family, so multiplication, division, and square-root
backends can share the same native/arbitrary-precision boundary.

Later proofs reason about the mathematical value of the pair instead of reopening carry code at
every use site.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

namespace UInt128

/-- Every two-word unsigned value lies below the first unrepresentable 128-bit integer. -/
theorem toNat_lt (value : UInt128) :
    value.toNat < 2 ^ 128 := by
  unfold UInt128.toNat
  rw [show 2 ^ 128 = 2 ^ 64 * 2 ^ 64 by
    rw [← pow_add]]
  have hlow := value.lo.toNat_lt
  have hhigh := value.hi.toNat_lt
  omega

/-- Below the one-word boundary, a two-limb value is represented entirely by its low limb. -/
theorem lo_toNat_eq_toNat_of_lt_two_pow
    (value : UInt128) (hvalue : value.toNat < 2 ^ 64) :
    value.lo.toNat = value.toNat := by
  have hhigh : value.hi.toNat = 0 := by
    unfold UInt128.toNat at hvalue
    have hpower : 0 < 2 ^ 64 := Nat.two_pow_pos 64
    omega
  unfold UInt128.toNat
  rw [hhigh]
  simp

/-- Two-limb splitting is exact for values below `2^128`. -/
theorem toNat_ofNat (value : Nat) (hvalue : value < 2 ^ 128) :
    (ofNat value).toNat = value := by
  have hhigh : value >>> 64 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [show 128 = 64 + 64 by omega, pow_add, Nat.mul_comm] using hvalue
  unfold ofNat UInt128.toNat
  rw [UInt64.toNat_ofNat_of_lt' hhigh, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  calc
    value % 2 ^ 64 + value / 2 ^ 64 * 2 ^ 64 =
        value % 2 ^ 64 + 2 ^ 64 * (value / 2 ^ 64) := by
      rw [Nat.mul_comm]
    _ = value := Nat.mod_add_div value (2 ^ 64)

/-- The two native limbs are uniquely determined by their mathematical value. -/
theorem toNat_injective : Function.Injective UInt128.toNat := by
  intro x y hvalue
  have hlow : x.lo.toNat = y.lo.toNat := by
    have hmod := congrArg (fun value : Nat => value % 2 ^ 64) hvalue
    unfold UInt128.toNat at hmod
    simpa only [Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt x.lo.toNat_lt,
      Nat.mod_eq_of_lt y.lo.toNat_lt] using hmod
  have hhigh : x.hi.toNat = y.hi.toNat := by
    unfold UInt128.toNat at hvalue
    rw [hlow] at hvalue
    exact Nat.mul_right_cancel (by positivity) (Nat.add_left_cancel hvalue)
  cases x
  cases y
  simp only [UInt128.mk.injEq] at hlow hhigh ⊢
  exact ⟨UInt64.toNat_inj.mp hhigh, UInt64.toNat_inj.mp hlow⟩

end UInt128

/-- The low 32-bit half of a word represents its residue modulo `2^32`. -/
@[simp, grind =] theorem low32_toNat (value : UInt64) :
    (low32 value).toNat = value.toNat % 2 ^ 32 := by
  have hmask : (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 := by
    decide
  rw [low32, UInt64.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]

/-- The high 32-bit half of a word represents its quotient by `2^32`. -/
@[simp, grind =] theorem high32_toNat (value : UInt64) :
    (high32 value).toNat = value.toNat / 2 ^ 32 := by
  simp [high32, Nat.shiftRight_eq_div_pow]

/-- Recombining the low and high 32-bit halves recovers the original word value. -/
theorem split32_toNat (value : UInt64) :
    value.toNat = (low32 value).toNat + 2 ^ 32 * (high32 value).toNat := by
  rw [low32_toNat, high32_toNat]
  exact (Nat.mod_add_div value.toNat (2 ^ 32)).symm

/-- A native word is zero exactly when its natural-number view is zero. -/
theorem uint64_toNat_eq_zero (value : UInt64) :
    value.toNat = 0 ↔ value = 0 := by
  simpa using (UInt64.toNat_inj (a := value) (b := 0))

/-- A two-limb value is nonzero exactly when at least one native limb is nonzero. -/
theorem UInt128.toNat_ne_zero_iff (value : UInt128) :
    value.toNat ≠ 0 ↔ value.lo ≠ 0 ∨ value.hi ≠ 0 := by
  unfold UInt128.toNat
  rw [ne_eq, Nat.add_eq_zero_iff, Nat.mul_eq_zero]
  norm_num
  rw [uint64_toNat_eq_zero, uint64_toNat_eq_zero]
  tauto

private theorem low32_lt (value : UInt64) :
    (low32 value).toNat < 2 ^ 32 := by
  rw [low32_toNat]
  exact Nat.mod_lt _ (by decide)

private theorem high32_lt (value : UInt64) :
    (high32 value).toNat < 2 ^ 32 := by
  rw [high32_toNat, Nat.div_lt_iff_lt_mul (by decide)]
  simpa [pow_add] using value.toNat_lt

private theorem mul_toNat_of_lt32 (x y : UInt64)
    (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  apply uint64_mul_toNat_of_lt
  nlinarith

private theorem shiftLeft32_toNat (value : UInt64)
    (hvalue : value.toNat < 2 ^ 32) :
    (value <<< 32).toNat = value.toNat * 2 ^ 32 := by
  rw [UInt64.toNat_shiftLeft]
  change (value.toNat <<< (32 % 64)) % 2 ^ 64 =
    value.toNat * 2 ^ 32
  norm_num
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  nlinarith

/-- `mul64` represents the exact mathematical product of its operands. -/
@[simp, grind =] theorem mul64_toNat (x y : UInt64) :
    (mul64 x y).toNat = x.toNat * y.toNat := by
  let x0 := low32 x
  let x1 := high32 x
  let y0 := low32 y
  let y1 := high32 y
  let w0 := x0 * y0
  let t := x1 * y0 + high32 w0
  let w1 := x0 * y1 + low32 t
  let hi := x1 * y1 + high32 t + high32 w1
  let lo := (low32 w1 <<< 32) + low32 w0
  have hx0 : x0.toNat < 2 ^ 32 := low32_lt x
  have hx1 : x1.toNat < 2 ^ 32 := high32_lt x
  have hy0 : y0.toNat < 2 ^ 32 := low32_lt y
  have hy1 : y1.toNat < 2 ^ 32 := high32_lt y
  have hw0 : w0.toNat = x0.toNat * y0.toNat := mul_toNat_of_lt32 x0 y0 hx0 hy0
  have hp10 : (x1 * y0).toNat = x1.toNat * y0.toNat := mul_toNat_of_lt32 x1 y0 hx1 hy0
  have hp01 : (x0 * y1).toNat = x0.toNat * y1.toNat := mul_toNat_of_lt32 x0 y1 hx0 hy1
  have hp11 : (x1 * y1).toNat = x1.toNat * y1.toNat := mul_toNat_of_lt32 x1 y1 hx1 hy1
  have hb00 : x0.toNat * y0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb10 : x1.toNat * y0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb01 : x0.toNat * y1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb11 : x1.toNat * y1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have htBound := t.toNat_lt
  have hw1Bound := w1.toNat_lt
  have ht : t.toNat = x1.toNat * y0.toNat + w0.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_add, hp10, high32_toNat w0, Nat.mod_eq_of_lt (by omega)]
  have hw1 : w1.toNat = x0.toNat * y1.toNat + t.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_add, hp01, low32_toNat t, Nat.mod_eq_of_lt (by omega)]
  have hhi : hi.toNat = x1.toNat * y1.toNat + t.toNat / 2 ^ 32 + w1.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hp11, high32_toNat t, high32_toNat w1,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hlo : lo.toNat = w1.toNat % 2 ^ 32 * 2 ^ 32 + w0.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_add, shiftLeft32_toNat _ (low32_lt w1), low32_toNat w1, low32_toNat w0,
      Nat.mod_eq_of_lt (by omega)]
  have hsplit : x.toNat * y.toNat =
      x0.toNat * y0.toNat + (x1.toNat * y0.toNat + x0.toNat * y1.toNat) * 2 ^ 32 +
        x1.toNat * y1.toNat * 2 ^ 64 := by
    rw [split32_toNat x, split32_toNat y]
    ring
  change lo.toNat + hi.toNat * 2 ^ 64 = x.toNat * y.toNat
  rw [hlo, hhi, hsplit]
  omega

/-- A zero high product limb certifies that the low limb is the complete exact product. -/
theorem mul64_lo_toNat_of_hi_eq_zero
    (left right : UInt64) (hhigh : (mul64 left right).hi = 0) :
    (mul64 left right).lo.toNat = left.toNat * right.toNat := by
  have hproduct := mul64_toNat left right
  unfold UInt128.toNat at hproduct
  simpa only [hhigh, UInt64.toNat_zero, zero_mul, add_zero] using hproduct

end FloatLib.Numerics.FixedWord

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
public import LeanPool.FloatLibBinary.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum

/-!
# Verified native-word integer square root

`sqrtIter_toNat` identifies the native Newton iteration with `Nat.sqrt.iter`, and `sqrt_toNat`
proves that its initialization computes the floor square root. The native average cannot overflow.
The runtime module proves termination by a strictly decreasing guess.

`natSqrt_eq_sqrtNat` installs a compiler substitution for `Nat.sqrt`, using this implementation
below `2^64` and the arbitrary-precision definition otherwise.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.IntegerSquareRoot

/-- The overflow-free native average has its ordinary natural-number value. -/
@[simp, grind =] theorem average_toNat (left right : UInt64) :
    (average left right).toNat = (left.toNat + right.toNat) / 2 := by
  have hleftHalf :
      (left >>> 1).toNat = left.toNat / 2 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hrightHalf :
      (right >>> 1).toNat = right.toNat / 2 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hcarry :
      (left &&& right &&& 1).toNat =
        if 2 ≤ left.toNat % 2 + right.toNat % 2 then 1 else 0 := by
    simp only [UInt64.toNat_and, UInt64.reduceToNat, Nat.and_one_is_mod]
    rw [show (2 : Nat) = 2 ^ 1 by decide, Nat.and_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one left.toNat with hleft | hleft <;>
      rcases Nat.mod_two_eq_zero_or_one right.toNat with hright | hright <;>
      simp_all
  have hleft := left.toNat_lt
  have hright := right.toNat_lt
  have hfirstFit :
      left.toNat / 2 + right.toNat / 2 < 2 ^ 64 := by
    omega
  have hfullFit :
      left.toNat / 2 + right.toNat / 2 +
        (if 2 ≤ left.toNat % 2 + right.toNat % 2 then 1 else 0) < 2 ^ 64 := by
    split <;> omega
  unfold average
  rw [UInt64.toNat_add, UInt64.toNat_add, hleftHalf, hrightHalf, hcarry,
    Nat.mod_eq_of_lt hfirstFit, Nat.mod_eq_of_lt hfullFit, Nat.add_div (by decide)]

/-- The native Newton iteration is exactly Lean's natural-number iteration. -/
@[simp, grind =] theorem sqrtIter_toNat (value guess : UInt64) :
    (sqrtIter value guess).toNat =
      Nat.sqrt.iter value.toNat guess.toNat := by
  rw [sqrtIter.eq_1, Nat.sqrt.iter.eq_1]
  let next := average guess (value / guess)
  have hnext :
      next.toNat =
        (guess.toNat + value.toNat / guess.toNat) / 2 := by
    simp only [next, average_toNat, UInt64.toNat_div]
  by_cases hdecrease : next < guess
  · have hdecreaseNat :
        (guess.toNat + value.toNat / guess.toNat) / 2 < guess.toNat := by
      rw [← hnext]
      exact UInt64.lt_iff_toNat_lt.mp hdecrease
    rw [dite_eq_left hdecrease, dite_eq_left hdecreaseNat]
    simpa only [next, hnext] using sqrtIter_toNat value next
  · have hnotDecreaseNat :
        ¬(guess.toNat + value.toNat / guess.toNat) / 2 < guess.toNat := by
      rw [← hnext]
      exact fun h ↦ hdecrease (UInt64.lt_iff_toNat_lt.mpr h)
    rw [dite_eq_right hdecrease, dite_eq_right hnotDecreaseNat]
termination_by guess.toNat
decreasing_by
  exact UInt64.lt_iff_toNat_lt.mp hdecrease

/-- Native-word integer square root agrees exactly with `Nat.sqrt`. -/
@[simp, grind =] theorem sqrt_toNat (value : UInt64) :
    (sqrt value).toNat = Nat.sqrt value.toNat := by
  rw [Nat.sqrt.eq_1]
  by_cases hsmall : value ≤ 1
  · have hsmallNat : value.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hsmall
    simp [sqrt, hsmall, hsmallNat]
  · have hlargeNat : ¬value.toNat ≤ 1 := by
      simpa [UInt64.le_iff_toNat_le] using hsmall
    simp only [sqrt, hsmall, hlargeNat, ite_false]
    rw [sqrtIter_toNat]
    apply congrArg (Nat.sqrt.iter value.toNat)
    let shift := value.log2.toNat / 2 + 1
    have hnonzero : value.toNat ≠ 0 := by
      omega
    have hlog :
        value.log2.toNat = value.toNat.log2 :=
      FloatLib.Numerics.FixedWord.log2_toNat value
    have hlogLt : value.toNat.log2 < 64 := by
      rw [Nat.log2_lt hnonzero]
      simpa [UInt64.size] using value.toNat_lt
    have hshift : shift < 64 := by
      simp only [shift, hlog]
      omega
    have hfit : (1 : UInt64).toNat <<< shift < 2 ^ 64 := by
      simp only [UInt64.reduceToNat, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by decide) hshift
    simpa only [shift, hlog, UInt64.reduceToNat] using
      FloatLib.Numerics.FixedWord.shiftLeft_toNat (1 : UInt64) shift hshift hfit

/-- The bounded native implementation preserves natural-number square root. -/
theorem sqrtNat_eq_sqrt (value : Nat) :
    sqrtNat value = Nat.sqrt value := by
  unfold sqrtNat
  dsimp only
  split
  next hfit =>
    rw [sqrt_toNat, UInt64.toNat_ofNat_of_lt' hfit]
  next _ =>
    exact (Nat.sqrt.eq_1 value).symm

/--
The compiler uses native-word square root whenever the input fits in one word.

This `@[csimp]` theorem is global: every module that imports it, in particular everything that
imports `FloatLib.Kernels`, compiles `Nat.sqrt` to `sqrtNat`, including uses unrelated to
FloatLib. The substitution is sound by `sqrtNat_eq_sqrt`, and the fallback branch of `sqrtNat` is
the unchanged logical definition, so only inputs below `2^64` take a different code path.
-/
-- grind: no rule; this is a compiler implementation substitution, not a search rewrite.
@[csimp] theorem natSqrt_eq_sqrtNat :
    Nat.sqrt = sqrtNat := by
  funext value
  exact (sqrtNat_eq_sqrt value).symm

end FloatLib.Numerics.FixedWord.IntegerSquareRoot

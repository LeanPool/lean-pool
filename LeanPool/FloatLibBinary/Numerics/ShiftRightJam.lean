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

import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Right shift with sticky-bit jamming

`shiftRightJam` is the representation-independent contract used by fixed words, dynamic limbs,
and format-specific rounding kernels. It returns the exact quotient when no discarded bit is set;
otherwise it records the discarded nonzero suffix in the quotient's low bit.

Keeping the operation in `Numerics` prevents a generic rounding argument from depending on one
particular fixed-word backend.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Shift right and preserve whether any discarded bit was nonzero in the result's low bit.

Exact shifts are unchanged. Inexact shifts return an odd result. This is the proof-facing
definition: it materializes `2^shift` to form the quotient and remainder, so fixed-word backends
execute the limb kernels in `FloatLib.Kernels` (such as `UInt256.shiftRightJam128`) and use this
definition only as their specification.
-/
@[inline] def shiftRightJam (value shift : Nat) : Nat :=
  let divisor := 2 ^ shift
  let quotient := value / divisor
  if value % divisor == 0 then
    quotient
  else
    quotient ||| 1

private theorem mod_two_pow_ne_zero_of_mod_two_ne_zero
    (value extra : Nat) (hextra : 0 < extra)
    (hodd : value % 2 ≠ 0) :
    value % 2 ^ extra ≠ 0 := by
  intro hzero
  have htwoDvd : 2 ∣ 2 ^ extra :=
    Nat.pow_dvd_pow 2 hextra
  have hmod := Nat.mod_mod_of_dvd value htwoDvd
  rw [hzero, Nat.zero_mod] at hmod
  exact hodd hmod.symm

/-- Exact right shifts are unchanged by jamming. -/
theorem shiftRightJam_eq_of_mod_eq_zero
    (value shift : Nat) (hexact : value % 2 ^ shift = 0) :
    shiftRightJam value shift = value / 2 ^ shift := by
  simp [shiftRightJam, hexact]

/-- An inexact right shift with jamming always returns an odd result. -/
theorem shiftRightJam_mod_two_eq_one
    (value shift : Nat) (hinexact : value % 2 ^ shift ≠ 0) :
    shiftRightJam value shift % 2 = 1 := by
  unfold shiftRightJam
  rw [ite_eq_right (by simpa only [beq_iff_eq] using hinexact)]
  rw [Nat.or_mod_two_eq_one]
  simp

/--
Every bit above the jammed low bit is the corresponding bit of the exact shifted value.

Truncating by at least one more bit therefore gives the same result as a single unjammed shift
by the sum of the two shift counts.
-/
theorem shiftRightJam_div_pow
    (value shift extra : Nat) (hextra : 0 < extra) :
    shiftRightJam value shift / 2 ^ extra =
      value / 2 ^ (shift + extra) := by
  unfold shiftRightJam
  by_cases hexact : value % 2 ^ shift = 0
  · rw [ite_eq_left (by simpa only [beq_iff_eq] using hexact)]
    rw [pow_add, ← Nat.div_div_eq_div_mul]
  · rw [ite_eq_right (by simpa only [beq_iff_eq] using hexact)]
    rw [Nat.or_div_two_pow]
    have honeSmall : 1 < 2 ^ extra :=
      Nat.one_lt_two_pow (Nat.ne_of_gt hextra)
    rw [Nat.div_eq_of_lt honeSmall, Nat.or_zero]
    rw [pow_add, ← Nat.div_div_eq_div_mul]

/-- Every positive-index bit of a jammed quotient is the corresponding original bit. -/
theorem shiftRightJam_testBit
    (value shift index : Nat) (hindex : 0 < index) :
    (shiftRightJam value shift).testBit index =
      value.testBit (shift + index) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [shiftRightJam_div_pow value shift index hindex]

/--
A positive-width suffix is nonzero after jamming exactly when the corresponding original suffix
was nonzero. This preserves sticky-bit information when shifts are composed.
-/
theorem shiftRightJam_mod_pow_ne_zero_iff
    (value shift extra : Nat) (hextra : 0 < extra) :
    shiftRightJam value shift % 2 ^ extra ≠ 0 ↔
      value % 2 ^ (shift + extra) ≠ 0 := by
  by_cases hexact : value % 2 ^ shift = 0
  · rw [shiftRightJam_eq_of_mod_eq_zero value shift hexact]
    let quotient := value / 2 ^ shift
    have hdecompose := Nat.mod_add_div value (2 ^ shift)
    have hvalue :
        value = 2 ^ shift * quotient := by
      dsimp [quotient]
      omega
    have horiginal :
        value % 2 ^ (shift + extra) =
          2 ^ shift * (quotient % 2 ^ extra) := by
      rw [pow_add, hvalue, Nat.mul_mod_mul_left]
    change quotient % 2 ^ extra ≠ 0 ↔
      value % 2 ^ (shift + extra) ≠ 0
    rw [horiginal]
    constructor
    · intro hnonzero
      exact Nat.mul_ne_zero (by positivity) hnonzero
    · intro hnonzero hzero
      apply hnonzero
      simp [hzero]
  · have hjammedOdd :
        shiftRightJam value shift % 2 ≠ 0 := by
      rw [shiftRightJam_mod_two_eq_one value shift hexact]
      decide
    have hleft :=
      mod_two_pow_ne_zero_of_mod_two_ne_zero
        (shiftRightJam value shift) extra hextra hjammedOdd
    have hpowerDvd : 2 ^ shift ∣ 2 ^ (shift + extra) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hright : value % 2 ^ (shift + extra) ≠ 0 := by
      intro hzero
      have hmod := Nat.mod_mod_of_dvd value hpowerDvd
      rw [hzero, Nat.zero_mod] at hmod
      exact hexact hmod.symm
    exact ⟨fun _ => hright, fun _ => hleft⟩

end FloatLib.Numerics

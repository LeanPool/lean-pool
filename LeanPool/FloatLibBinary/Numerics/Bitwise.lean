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

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Log

/-!
# Natural-number bit lemmas

Small format-independent facts about viewing natural numbers as bit strings. Floating-point and
posit proofs share these results without depending on one another's representation layers.
-/

@[expose] public section

namespace Nat

/--
A value that fits in a given bit width also fits in every larger bit width.
-/
theorem lt_two_pow_of_lt_two_pow_of_le {value smallWidth largeWidth : Nat}
    (hvalue : value < 2 ^ smallWidth) (hwidth : smallWidth ≤ largeWidth) :
    value < 2 ^ largeWidth :=
  lt_of_lt_of_le hvalue (Nat.pow_le_pow_right (by decide) hwidth)

/--
For a value that fits in `width + 1` bits, bit `width` is set exactly when the value reaches
`2 ^ width`.
-/
theorem testBit_eq_true_iff_two_pow_le_of_lt {value width : Nat}
    (hvalue : value < 2 ^ (width + 1)) :
    value.testBit width = true ↔ 2 ^ width ≤ value := by
  constructor
  · exact Nat.ge_two_pow_of_testBit
  · intro hlower
    have hpow : 0 < 2 ^ width := Nat.two_pow_pos width
    have hquotientPos : 0 < value / 2 ^ width :=
      Nat.div_pos hlower hpow
    have hquotientLt : value / 2 ^ width < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpow]
      simpa [Nat.pow_succ, Nat.mul_comm] using hvalue
    have hquotient : value / 2 ^ width = 1 := by
      omega
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hquotient]

/-- Left shifting a nonzero natural increases its binary logarithm by the shift distance. -/
theorem log2_shiftLeft_of_ne_zero (value shift : Nat) (hvalue : value ≠ 0) :
    (value <<< shift).log2 = value.log2 + shift := by
  simp only [Nat.shiftLeft_eq]
  induction shift with
  | zero => simp
  | succ shift ih =>
      rw [pow_succ, ← Nat.mul_assoc, Nat.mul_comm (value * 2 ^ shift) 2]
      rw [Nat.log2_two_mul]
      · rw [ih]
        omega
      · exact Nat.mul_ne_zero hvalue (pow_ne_zero _ (by decide))

end Nat

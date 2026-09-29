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

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Data.Nat.ModEq

/-!
# Bounded modular exponentiation

Exponentiation by squaring for exact modular arithmetic without constructing the usually enormous
unreduced power.

This helper is representation-independent and is used when quantizers need a power only modulo a
known denominator or code range. Reducing after every multiplication keeps intermediate naturals
bounded while the accompanying equations preserve the exact mathematical residue.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Compute `base ^ exponent` modulo `modulus` by exponentiation by squaring.

Only residues smaller than `modulus` are multiplied, so a large exponent does not construct the
usually enormous natural number `base ^ exponent`. Modulus zero has the explicit total result zero;
callers that need ordinary modular arithmetic should establish that the modulus is nonzero.
-/
def modularPow (base exponent modulus : Nat) : Nat :=
  if modulus == 0 then
    0
  else
    Nat.binaryRec
      (1 % modulus)
      (fun lowBit _ halfPower =>
        let squared := halfPower * halfPower % modulus
        if lowBit then squared * (base % modulus) % modulus else squared)
      exponent

/-- The library's total modular-power convention returns zero at modulus zero. -/
@[simp, grind =] theorem modularPow_zero (base exponent : Nat) :
    modularPow base exponent 0 = 0 := by
  simp [modularPow]

/-- Exponentiation by squaring computes the ordinary modular power for a nonzero modulus. -/
theorem modularPow_eq_pow_mod (base exponent modulus : Nat)
    (hmodulus : modulus ≠ 0) :
    modularPow base exponent modulus = base ^ exponent % modulus := by
  unfold modularPow
  rw [ite_eq_right (by simp [hmodulus])]
  induction exponent using Nat.binaryRec' with
  | zero =>
      rfl
  | bit lowBit exponent hvalid ih =>
      rw [Nat.binaryRec_eq _ _ (by exact Or.inr hvalid)]
      cases lowBit
      · simp only [Nat.bit_false_apply, Bool.false_eq_true, ↓reduceIte]
        rw [ih, Nat.two_mul, pow_add]
        exact (Nat.mul_mod _ _ _).symm
      · simp only [Nat.bit_true_apply, ↓reduceIte]
        rw [ih, Nat.two_mul, pow_add, pow_succ]
        simp only [pow_zero, one_mul]
        have hsquare :
            (base ^ exponent % modulus * (base ^ exponent % modulus)) % modulus =
              (base ^ exponent * base ^ exponent) % modulus :=
          (Nat.mod_modEq (base ^ exponent) modulus).mul
            (Nat.mod_modEq (base ^ exponent) modulus)
        rw [hsquare, pow_add]
        exact
          (Nat.mod_modEq (base ^ exponent * base ^ exponent) modulus).mul
            (Nat.mod_modEq base modulus)

end FloatLib.Numerics

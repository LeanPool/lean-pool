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

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positional-radix capability

A radix is the base used by a positional numerical system.  Binary floating point uses radix two,
decimal floating point uses radix ten, and the abstract rounded-real development can work with any
natural radix at least two.

This definition belongs to the general numerical layer: fixed point, floating point, and other
positional systems can all use the same radix without depending on a binary storage format.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- A positional radix whose natural base is at least two. -/
structure Radix where
  /-- Natural base of the positional system. -/
  base : Nat
  /-- Positional systems require a base of at least two. -/
  base_valid : 2 ≤ base

/-- Binary radix. -/
def binaryRadix : Radix := ⟨2, by norm_num⟩

/-- Decimal radix. -/
def decimalRadix : Radix := ⟨10, by norm_num⟩

namespace Radix

/-- View the radix as a real scaling factor. -/
def toReal (radix : Radix) : ℝ := radix.base

/-- Every radix is positive when interpreted as a real scaling factor. -/
theorem pos (radix : Radix) : 0 < radix.toReal := by
  have hbase : 0 < radix.base := lt_of_lt_of_le (by norm_num) radix.base_valid
  have hbaseReal : (0 : ℝ) < (radix.base : ℝ) := by exact_mod_cast hbase
  simpa [toReal] using hbaseReal

/-- A radix is nonzero when interpreted as a real scaling factor. -/
theorem ne_zero (radix : Radix) : radix.toReal ≠ 0 :=
  ne_of_gt radix.pos

/-- Every positional radix is strictly greater than one. -/
theorem gt_one (radix : Radix) : 1 < radix.toReal := by
  simp only [toReal, Nat.one_lt_cast]
  exact Nat.one_lt_cast.mpr (Nat.succ_le_iff.mp radix.base_valid)

end Radix
end FloatLib.Numerics

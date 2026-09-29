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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ModelSqrt.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.IntegerSquareRoot.Proof
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Correctness of native-backed unpacked floating-point square root

The executable implementation lives in `ModelSqrt.Runtime`. This module proves exact agreement
with Lean's logical unpacked-float operation and registers the verified compiler substitution.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeModelSqrt

/-- The native-backed core is exactly Lean's logical unpacked square-root core. -/
theorem sqrtCore_eq (spec : Float.Model.Format) (mantissa : Nat) (exponent : Int) :
    sqrtCore spec mantissa exponent =
      Float.Model.UnpackedFloat.sqrtCore spec mantissa exponent := by
  simp [sqrtCore, Float.Model.UnpackedFloat.sqrtCore,
    FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt]

/-- The native-backed operation is exactly Lean's logical unpacked floating-point square root. -/
theorem sqrt_eq (spec : Float.Model.Format) (value : Float.Model.UnpackedFloat) :
    sqrt spec value = Float.Model.UnpackedFloat.sqrt spec value := by
  cases value with
  | notANumber => rfl
  | infinity sign =>
      cases sign <;> rfl
  | zero sign => rfl
  | finite sign mantissa exponent mantissa_pos =>
      cases sign
      · rfl
      · simp [sqrt, Float.Model.UnpackedFloat.sqrt, sqrtCore_eq]

/-- Compile Lean's logical unpacked square root through the proved native-backed implementation. -/
@[csimp] theorem unpackedSqrt_eq_sqrt :
    Float.Model.UnpackedFloat.sqrt = sqrt := by
  funext spec value
  exact (sqrt_eq spec value).symm

end Model.NativeModelSqrt
end FloatLib.Floats.Formats.BinaryInterchange

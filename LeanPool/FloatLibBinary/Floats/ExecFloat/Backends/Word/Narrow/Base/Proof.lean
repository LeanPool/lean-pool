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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Correctness of native binary32 storage operations

The `UInt32` storage conversions are mutual inverses, and native sign-bit negation agrees with
the generic binary32 model. Runtime clients can import `Base.Runtime` without these proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Word negation is the model sign flip. -/
@[simp] theorem negate_eq (x : Value) :
    negate x = Model.neg x := by
  cases x
  rfl

/-- Repacking the stored word returns the value. -/
@[simp] theorem ofUInt32_toUInt32 (x : Value) :
    ofUInt32 (toUInt32 x) = x := by
  cases x
  rfl

/-- Unpacking a freshly packed word returns the word. -/
@[simp] theorem toUInt32_ofUInt32 (bits : UInt32) :
    toUInt32 (ofUInt32 bits) = bits :=
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

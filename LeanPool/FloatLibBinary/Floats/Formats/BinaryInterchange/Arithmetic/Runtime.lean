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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Add.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Div.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Fma.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Mul.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Sqrt.Runtime

/-!
# Format-parameterized binary arithmetic runtime

The six model operations use the structural dispatchers selected for a validated format
descriptor. This module contains only executable definitions; their refinement theorems live in
`Arithmetic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Automatically dispatched addition for any validated format descriptor. -/
def add {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  AddBackend.word x y

/-- Automatically dispatched subtraction for any validated format descriptor. -/
def sub {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  AddBackend.subWord x y

/-- Automatically dispatched multiplication for any validated format descriptor. -/
def mul {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  MulBackend.word x y

/-- Automatically dispatched division for any validated format descriptor. -/
def div {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  DivBackend.word x y

/-- Automatically dispatched square root for any validated format descriptor. -/
def sqrt {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  SqrtBackend.dispatch x

/-- Automatically dispatched fused multiply-add for any validated format descriptor. -/
def fma {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  FmaBackend.dispatch x y z

end Model
end FloatLib.Floats.Formats.BinaryInterchange

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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Add.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Div.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Fma.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Mul.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.Sqrt.Proof

/-!
# Refinement of format-parameterized binary arithmetic

The executable model operations agree with the independent descriptor-aware specifications for
every validated `FloatFormat`.

These theorems connect the arithmetic dispatchers to the format's specifications before a result
is transported to configured storage. Each dispatcher proof covers its optimized backends and
generic fallback.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Proof

/-- Public addition agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem add_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    add x y = Spec.add x y :=
  AddBackend.word_eq_spec x y

/-- Public subtraction agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem sub_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    sub x y = Spec.sub x y :=
  AddBackend.subWord_eq_spec x y

/-- Public multiplication agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem mul_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    mul x y = Spec.mul x y :=
  MulBackend.word_eq_spec x y

/-- Public division agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem div_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    div x y = Spec.div x y :=
  DivBackend.word_eq_spec x y

/-- Public square root agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem sqrt_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    sqrt x = Spec.sqrt x :=
  SqrtBackend.dispatch_eq_spec x

/-- Public FMA agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem fma_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    fma x y z = Spec.fma x y z :=
  FmaBackend.dispatch_eq_spec x y z

end Proof
end Model
end FloatLib.Floats.Formats.BinaryInterchange

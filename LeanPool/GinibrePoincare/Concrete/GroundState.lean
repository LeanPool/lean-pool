/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/GroundState.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

public import LeanPool.GinibrePoincare.Concrete.Weights
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.Ring

/-!
# Vandermonde ground-state transform

The unnormalised transform is multiplication by the holomorphic Vandermonde.
A normalised transform is also defined from the actual mass of
`|V_n|² γ_n`; positivity and finiteness of that mass remain explicit analytic
obligations.
-/


@[expose] public section


namespace GinibrePoincare

noncomputable section

/-- Multiplication by the Vandermonde determinant. -/
def vandermondeTransform {n : ℕ} (f : Configuration n → ℂ) :
    Configuration n → ℂ :=
  fun z => vandermonde z * f z

/-- Symmetric observables become alternating after multiplication by `V_n`. -/
theorem vandermondeTransform_isAlternating {n : ℕ}
    (f : Configuration n → ℂ) (hf : IsSymmetric f) :
    IsAlternating (vandermondeTransform f) := by
  intro σ z
  unfold vandermondeTransform
  rw [vandermonde_permute σ z, hf σ z]
  ring

/-- Pointwise squared-modulus identity for the unnormalised transform. -/
theorem normSq_vandermondeTransform {n : ℕ}
    (f : Configuration n → ℂ) (z : Configuration n) :
    Complex.normSq (vandermondeTransform f z) =
      vandermondeWeight z * Complex.normSq (f z) := by
  simp [vandermondeTransform, vandermondeWeight, Complex.normSq_mul]

end

end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGradientBasis.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CompactLipschitzLSIExtension
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Alternative Bakry Emery gradient basis

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_directionalEnergy_orthonormalBasis`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
/-- Coordinate energy in an orthonormal basis is the literal Hilbert gradient
energy, including at points where the total derivative is defined to be zero. -/
theorem bakryEmery_directionalEnergy_orthonormalBasis
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : E → ℝ) (x : E) : directionalEnergy b f x = ‖gradient f x‖^2 := by
  have h : InnerProductSpace.toDual ℝ E (gradient f x) = fderiv ℝ f x := by
    simp [gradient]
  unfold directionalEnergy
  rw [← h]
  simpa only [InnerProductSpace.toDual_apply_apply] using b.sum_sq_inner_left (gradient f x)
end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/CenterOfMass.lean.
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

public import LeanPool.GinibrePoincare.Concrete.Configuration

/-!
# Centre of mass

The real and imaginary parts of the coordinate sum are the equality
directions in the optimal Ginibre Poincaré inequality.
-/


@[expose] public section


open scoped BigOperators

namespace GinibrePoincare

/-- Sum of the particle coordinates. -/
def coordinateSum {n : ℕ} (z : Configuration n) : ℂ :=
  ∑ i : Fin n, z i

/-- Real part of the coordinate sum. -/
def centerOfMassReal {n : ℕ} (z : Configuration n) : ℝ :=
  (coordinateSum z).re

/-- Imaginary part of the coordinate sum. -/
def centerOfMassImag {n : ℕ} (z : Configuration n) : ℝ :=
  (coordinateSum z).im

/-- The coordinate sum is permutation invariant. -/
theorem coordinateSum_permute {n : ℕ}
    (σ : ParticlePermutation n) (z : Configuration n) :
    coordinateSum (permute σ z) = coordinateSum z := by
  unfold coordinateSum
  simpa [permute] using (Equiv.sum_comp σ z)

/-- The real centre-of-mass statistic is symmetric. -/
theorem centerOfMassReal_isSymmetric {n : ℕ} :
    IsSymmetric (fun z : Configuration n => centerOfMassReal z) := by
  intro σ z
  simp [centerOfMassReal, coordinateSum_permute]

/-- The imaginary centre-of-mass statistic is symmetric. -/
theorem centerOfMassImag_isSymmetric {n : ℕ} :
    IsSymmetric (fun z : Configuration n => centerOfMassImag z) := by
  intro σ z
  simp [centerOfMassImag, coordinateSum_permute]

end GinibrePoincare

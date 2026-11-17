/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/Vandermonde.lean.
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
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The complex Vandermonde polynomial

This file connects the Vandermonde determinant used in the Ginibre density to
Mathlib's Vandermonde matrix.  It proves the product formula, the precise
collision zero set, nonvanishing on collision-free configurations, and
alternation under particle permutations.
-/


@[expose] public section


namespace GinibrePoincare

/-- The Vandermonde determinant of a complex particle configuration. -/
def vandermonde {n : ℕ} (z : Configuration n) : ℂ :=
  (Matrix.vandermonde z).det

/-- Product formula for the Vandermonde determinant. -/
theorem vandermonde_eq_product {n : ℕ} (z : Configuration n) :
    vandermonde z = ∏ i : Fin n, ∏ j > i, (z j - z i) := by
  exact Matrix.det_vandermonde z

/-- The Vandermonde vanishes exactly on the collision locus. -/
theorem vandermonde_eq_zero_iff {n : ℕ} (z : Configuration n) :
    vandermonde z = 0 ↔ z ∈ collisionSet n := by
  simpa only [vandermonde, mem_collisionSet_iff] using
    (Matrix.det_vandermonde_eq_zero_iff (v := z))

/-- The Vandermonde is nonzero exactly at collision-free configurations. -/
theorem vandermonde_ne_zero_iff {n : ℕ} (z : Configuration n) :
    vandermonde z ≠ 0 ↔ CollisionFree z := by
  simpa only [vandermonde, CollisionFree] using
    (Matrix.det_vandermonde_ne_zero_iff (v := z))

/-- Relabelling the particles multiplies the Vandermonde by the permutation sign. -/
theorem vandermonde_permute {n : ℕ} (σ : ParticlePermutation n)
    (z : Configuration n) :
    vandermonde (permute σ z) =
      permutationSign σ * vandermonde z := by
  have hmatrix :
      Matrix.vandermonde (permute σ z) =
        (Matrix.vandermonde z).submatrix σ id := by
    ext i j
    simp [permute]
  unfold vandermonde
  rw [hmatrix]
  simpa [permutationSign] using
    (Matrix.det_permute σ (Matrix.vandermonde z))

/-- The Vandermonde observable is alternating. -/
theorem vandermonde_isAlternating {n : ℕ} :
    IsAlternating (fun z : Configuration n => vandermonde z) := by
  intro σ z
  exact vandermonde_permute σ z

end GinibrePoincare

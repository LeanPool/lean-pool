/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/NormalizedGroundState.lean.
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

public import LeanPool.GinibrePoincare.Concrete.GroundState
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring

/-!
# Normalized Vandermonde transform

The scale is the square root of the actual mass of `|V_n|² γ_n`.  The
definition therefore agrees with the ground-state transform once positivity
and finiteness of the mass have been proved.
-/


@[expose] public section


namespace GinibrePoincare

noncomputable section

/-- Real square-root normalization associated with the raw Ginibre mass. -/
def groundStateNormalization (n : ℕ) : ℝ :=
  Real.sqrt (ginibreNormalizingMass n).toReal

/-- Normalized multiplication by the Vandermonde. -/
def normalizedVandermondeTransform (n : ℕ)
    (f : Configuration n → ℂ) : Configuration n → ℂ :=
  fun z => ((groundStateNormalization n : ℂ)⁻¹) *
    vandermondeTransform f z

/-- Pointwise formula for the normalized transform. -/
theorem normalizedVandermondeTransform_apply (n : ℕ)
    (f : Configuration n → ℂ) (z : Configuration n) :
    normalizedVandermondeTransform n f z =
      ((groundStateNormalization n : ℂ)⁻¹) *
        vandermonde z * f z := by
  unfold normalizedVandermondeTransform vandermondeTransform
  ring

/-- The normalized transform sends symmetric functions to alternating ones. -/
theorem normalizedVandermondeTransform_isAlternating {n : ℕ}
    (f : Configuration n → ℂ) (hf : IsSymmetric f) :
    IsAlternating (normalizedVandermondeTransform n f) := by
  intro σ z
  unfold normalizedVandermondeTransform
  rw [vandermondeTransform_isAlternating f hf σ z]
  ring

end

end GinibrePoincare

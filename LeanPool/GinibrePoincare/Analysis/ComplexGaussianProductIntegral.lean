/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexGaussianProductIntegral.lean.
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

public import LeanPool.GinibrePoincare.Concrete.GaussianProbability
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Factoring coordinatewise integrals under the complex Gaussian product -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace GinibrePoincare

noncomputable section

theorem integrable_prod_coordinateFunctions_complexGaussianMeasure
    (n : ℕ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, Integrable (f i)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    Integrable (fun z : Configuration n ↦ ∏ i, f i (z i))
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact Integrable.fintype_prod hf

theorem integral_prod_coordinateFunctions_complexGaussianMeasure
    (n : ℕ) (f : Fin n → ℂ → ℂ) :
    (∫ z : Configuration n, ∏ i, f i (z i) ∂complexGaussianMeasure n) =
      ∏ i, ∫ w : ℂ, f i w
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  simpa using (integral_fintype_prod_eq_prod
    (𝕜 := ℂ) (E := fun _ : Fin n ↦ ℂ)
    (μ := fun _ : Fin n ↦
      (complexCoordinateGaussianProbability n : Measure ℂ)) f)

theorem integrable_and_integral_prod_coordinateFunctions_complexGaussianMeasure
    (n : ℕ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, Integrable (f i)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    Integrable (fun z : Configuration n ↦ ∏ i, f i (z i))
        (complexGaussianMeasure n) ∧
      (∫ z : Configuration n, ∏ i, f i (z i) ∂complexGaussianMeasure n) =
        ∏ i, ∫ w : ℂ, f i w
          ∂(complexCoordinateGaussianProbability n : Measure ℂ) :=
  ⟨integrable_prod_coordinateFunctions_complexGaussianMeasure n f hf,
    integral_prod_coordinateFunctions_complexGaussianMeasure n f⟩

end

end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/EntropyProductDecomposition.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Entropy product decomposition

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `squareEntropy_prod_decomposition`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The square moment of a fiber in a product probability space. -/
def fiberSquareMoment {α β : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : α × β → ℝ) (x : α) : ℝ := ∫ y, f (x, y) ^ 2 ∂ν

theorem fiberSquareMoment_nonneg {α β : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : α × β → ℝ) (x : α) : 0 ≤ fiberSquareMoment ν f x :=
  integral_nonneg (fun y => sq_nonneg (f (x, y)))

/-- The exact chain decomposition of square entropy under a product law.
This is the algebraic/measure-theoretic tensorization step; it is not an LSI.
The logarithmic fiber moment is an explicit integrability condition. -/
theorem squareEntropy_prod_decomposition
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (f : α × β → ℝ)
    (hsq : Integrable (fun p => f p ^ 2) (μ.prod ν))
    (hlog : Integrable (fun p => f p ^ 2 * Real.log (f p ^ 2)) (μ.prod ν))
    (hfiber : Integrable (fun x => fiberSquareMoment ν f x *
      Real.log (fiberSquareMoment ν f x)) μ) :
    squareEntropy (μ.prod ν) f =
      (∫ x, squareEntropy ν (fun y => f (x, y)) ∂μ) +
        squareEntropy μ (fun x => Real.sqrt (fiberSquareMoment ν f x)) := by
  have hsqrt : ∀ x, Real.sqrt (fiberSquareMoment ν f x) ^ 2 = fiberSquareMoment ν f x :=
    fun x => Real.sq_sqrt (fiberSquareMoment_nonneg ν f x)
  have him : Integrable
      (fun x => ∫ y, f (x, y) ^ 2 * Real.log (f (x, y) ^ 2) ∂ν) μ :=
    hlog.integral_prod_left
  unfold squareEntropy
  simp only [hsqrt]
  change _ = (∫ x, (∫ y, f (x, y) ^ 2 * Real.log (f (x, y) ^ 2) ∂ν) -
      fiberSquareMoment ν f x * Real.log (fiberSquareMoment ν f x) ∂μ) + _
  rw [integral_sub him hfiber, integral_prod (fun p => f p ^ 2 * Real.log (f p ^ 2)) hlog]
  have hm : (∫ x, fiberSquareMoment ν f x ∂μ) = ∫ p, f p ^ 2 ∂μ.prod ν :=
    (integral_prod (fun p => f p ^ 2) hsq).symm
  rw [hm]
  ring

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ProductWeightedMeasure.lean.
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

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product weighted measure

Part of the ginibre measure and holomorphic geometry development of the
Ginibre Poincaré formalization.

Main results: `pi_withDensity_ofReal_eq`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace GinibrePoincare
noncomputable section

/-- Coordinatewise nonnegative integrable weights preserve product structure. -/
theorem pi_withDensity_ofReal_eq
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)]
    (w : ι → E → ℝ) (_hw : ∀ i, Measurable (w i))
    (hi : ∀ i, Integrable (w i) (μ i)) (hp : ∀ i x, 0 ≤ w i x)
    [∀ i, SigmaFinite ((μ i).withDensity (fun x => ENNReal.ofReal (w i x)))] :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (w i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, w i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hir : ∀ i, Integrable (w i) ((μ i).restrict (s i)) :=
    fun i => (hi i).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hir)
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hp i (x i)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hp i))]
  congr 1
  funext i
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hir i) (ae_of_all _ (hp i))

end
end GinibrePoincare

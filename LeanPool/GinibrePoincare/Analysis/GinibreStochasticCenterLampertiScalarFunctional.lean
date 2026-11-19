/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLampertiScalarFunctional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiGenerator
public import LeanPool.GinibrePoincare.Analysis.LampertiRadiusPathFunctional

/-! A genuine measurable Lamperti path functional, built from actual finite
Riemann sums, with no measurability assumption on an ordinary path integral.
It is the real-radius construction `lampertiRadiusPathFunctional` read through
the radius `Complex.normSq` of the center path. -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The Riemann-sum Lamperti functional of a complex center path `p`: the increment of `|p|`
from `√(ginibreCenterSquared n z)`, minus a `k + 1`-point Riemann sum of the drift, over
`√(2α/n)`. -/
def ginibreCenterScalarLampertiRiemannFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (k : ℕ) (p : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  lampertiRadiusRiemannFunctional Complex.normSq (ginibreLampertiCenterDrift n α)
    (ginibreCenterSquared n z) (Real.sqrt (2*α/(n : ℝ))) k p t

/-- The pathwise Lamperti functional of the center: the limit as `k → ∞` of the Riemann-sum
functionals `ginibreCenterScalarLampertiRiemannFunctional n α z k p t`. -/
def ginibreCenterScalarLampertiPathFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  lampertiRadiusPathFunctional Complex.normSq (ginibreLampertiCenterDrift n α)
    (ginibreCenterSquared n z) (Real.sqrt (2*α/(n : ℝ))) p t

theorem ginibreCenterScalarLampertiRiemannFunctional_measurable (n : ℕ) (α : ℝ)
    (z : Configuration n) (k : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreCenterScalarLampertiRiemannFunctional n α z k p t) :=
  lampertiRadiusRiemannFunctional_measurable Complex.continuous_normSq.measurable
    (ginibreLampertiCenterDrift_measurable n α) _ _ k t

theorem ginibreCenterScalarLampertiPathFunctional_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    Measurable (ginibreCenterScalarLampertiPathFunctional n α z) :=
  lampertiRadiusPathFunctional_measurable Complex.continuous_normSq.measurable
    (ginibreLampertiCenterDrift_measurable n α) _ _

theorem ginibreCenterScalarLampertiPathFunctional_eq_integral (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → ℂ) (hp : Continuous p) (hpos : ∀ s, 0 < Complex.normSq (p s))
    (t : ℝ≥0) :
    ginibreCenterScalarLampertiPathFunctional n α z p t =
      (Real.sqrt (Complex.normSq (p t))-Real.sqrt (ginibreCenterSquared n z)-
        ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α (Complex.normSq (p s.toNNReal))) /
          Real.sqrt (2*α/(n : ℝ)) :=
  lampertiRadiusPathFunctional_eq_integral Complex.continuous_normSq
    (ginibreLampertiCenterDrift_continuousOn n α) _ _ p hp hpos t
end
end GinibrePoincare

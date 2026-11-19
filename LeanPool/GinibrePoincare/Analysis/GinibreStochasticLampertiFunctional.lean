/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLampertiFunctional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLampertiGenerator
public import LeanPool.GinibrePoincare.Analysis.LampertiRadiusPathFunctional

/-! A genuine measurable Lamperti path functional, built from actual finite
Riemann sums, with no measurability assumption on an ordinary path integral.
It is the real-radius construction `lampertiRadiusPathFunctional` read through
`pairwiseRadius`. -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem pairwiseRadius_recentered (n : ℕ) (z : Configuration n) :
    pairwiseRadius (recenteredConfiguration n z)=pairwiseRadius z := by
  simp only [pairwiseRadius_eq_radialObservable, radialObservable, recenteredSqNorm,
      recentered_idempotent]

/-- The Riemann-sum radial Lamperti functional: the increment of `√(pairwiseRadius p)` from
`√(pairwiseRadius z)`, minus a `k + 1`-point Riemann sum of the drift, over `√(2α/n)`. -/
def ginibreLampertiRiemannFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (k : ℕ) (p : ℝ≥0 → Configuration n) (t : ℝ≥0) : ℝ :=
  lampertiRadiusRiemannFunctional pairwiseRadius (ginibreLampertiRadialDrift n α)
    (pairwiseRadius z) (Real.sqrt (2*α/(n : ℝ))) k p t

/-- The pathwise radial Lamperti functional: the limit as `k → ∞` of the Riemann-sum
functionals `ginibreLampertiRiemannFunctional n α z k p t`. -/
def ginibreLampertiPathFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → Configuration n) (t : ℝ≥0) : ℝ :=
  lampertiRadiusPathFunctional pairwiseRadius (ginibreLampertiRadialDrift n α)
    (pairwiseRadius z) (Real.sqrt (2*α/(n : ℝ))) p t

theorem ginibreLampertiRiemannFunctional_measurable (n : ℕ) (α : ℝ)
    (z : Configuration n) (k : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreLampertiRiemannFunctional n α z k p t) :=
  lampertiRadiusRiemannFunctional_measurable
    (ginibre_contDiff_pairwiseRadius n).continuous.measurable
    (ginibreLampertiRadialDrift_measurable n α) _ _ k t

theorem ginibreLampertiPathFunctional_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    Measurable (ginibreLampertiPathFunctional n α z) :=
  lampertiRadiusPathFunctional_measurable
    (ginibre_contDiff_pairwiseRadius n).continuous.measurable
    (ginibreLampertiRadialDrift_measurable n α) _ _

theorem ginibreLampertiPathFunctional_eq_integral (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → Configuration n) (hp : Continuous p) (hpos : ∀ s, 0 < pairwiseRadius (p s))
    (t : ℝ≥0) :
    ginibreLampertiPathFunctional n α z p t =
      (Real.sqrt (pairwiseRadius (p t))-Real.sqrt (pairwiseRadius z)-
        ∫ s in (0 : ℝ)..t, ginibreLampertiRadialDrift n α (pairwiseRadius (p s.toNNReal))) /
          Real.sqrt (2*α/(n : ℝ)) :=
  lampertiRadiusPathFunctional_eq_integral (ginibre_contDiff_pairwiseRadius n).continuous
    (ginibreLampertiRadialDrift_continuousOn n α) _ _ p hp hpos t
end
end GinibrePoincare

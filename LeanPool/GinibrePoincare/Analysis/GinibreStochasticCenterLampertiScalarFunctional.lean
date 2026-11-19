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
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-! A genuine measurable Lamperti path functional, built from actual finite
Riemann sums, with no measurability assumption on an ordinary path integral. -/

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
  (Real.sqrt (Complex.normSq (p t))-Real.sqrt (ginibreCenterSquared n z)-
    ∑ i : Fin (k+1), ginibreLampertiCenterDrift n α
      (Complex.normSq (p (ginibreUniformBrownianTime t k i)))*((t : ℝ)/((k : ℝ)+1))) /
        Real.sqrt (2*α/(n : ℝ))

/-- The pathwise Lamperti functional of the center: the limit as `k → ∞` of the Riemann-sum
functionals `ginibreCenterScalarLampertiRiemannFunctional n α z k p t`. -/
def ginibreCenterScalarLampertiPathFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun k => ginibreCenterScalarLampertiRiemannFunctional n α z k p t)

theorem ginibreCenterScalarLampertiRiemannFunctional_measurable (n : ℕ) (α : ℝ)
    (z : Configuration n) (k : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreCenterScalarLampertiRiemannFunctional n α z k p t) := by
  have hr (s : ℝ≥0) : Measurable (fun p : ℝ≥0 → ℂ => Complex.normSq (p s)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply s)
  have hg : Measurable (fun p : ℝ≥0 → ℂ => ∑ i : Fin (k+1),
      ginibreLampertiCenterDrift n α (Complex.normSq (p (ginibreUniformBrownianTime t k i)))*
        ((t : ℝ)/((k : ℝ)+1))) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((ginibreLampertiCenterDrift_measurable n α).comp (hr _)).mul_const _
  exact (((Real.continuous_sqrt.measurable.comp (hr t)).sub measurable_const).sub hg).div_const _

theorem ginibreCenterScalarLampertiPathFunctional_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    Measurable (ginibreCenterScalarLampertiPathFunctional n α z) := by
  apply Measurable.of_eval
  intro t
  exact (StronglyMeasurable.limUnder (fun k =>
    (ginibreCenterScalarLampertiRiemannFunctional_measurable n α z k
        t).stronglyMeasurable)).measurable

theorem ginibreCenterScalarLampertiPathFunctional_eq_integral (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → ℂ) (hp : Continuous p) (hpos : ∀ s, 0 < Complex.normSq (p s))
    (t : ℝ≥0) :
    ginibreCenterScalarLampertiPathFunctional n α z p t =
      (Real.sqrt (Complex.normSq (p t))-Real.sqrt (ginibreCenterSquared n z)-
        ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α (Complex.normSq (p s.toNNReal))) /
          Real.sqrt (2*α/(n : ℝ)) := by
  let w := fun s : ℝ => ginibreLampertiCenterDrift n α (Complex.normSq (p s.toNNReal))
  have hw : Continuous w := (ginibreLampertiCenterDrift_continuousOn n α).comp_continuous
    (Complex.continuous_normSq.comp (hp.comp continuous_real_toNNReal))
    (fun s => hpos _)
  have h := itoContinuousScalarRiemann_fin_tendsto w t hw.continuousOn
  have hl : Tendsto (fun k => ginibreCenterScalarLampertiRiemannFunctional n α z k p t) atTop
      (𝓝 ((Real.sqrt (Complex.normSq (p t))-Real.sqrt (ginibreCenterSquared n z)-
        ∫ s in (0 : ℝ)..t, w s)/Real.sqrt (2*α/(n : ℝ)))) := by
    have hc : Tendsto (fun _ : ℕ => Real.sqrt (Complex.normSq (p t))-Real.sqrt (ginibreCenterSquared
        n z))
        atTop (𝓝 (Real.sqrt (Complex.normSq (p t))-Real.sqrt (ginibreCenterSquared n z))) :=
            tendsto_const_nhds
    simpa only [ginibreCenterScalarLampertiRiemannFunctional, w, Real.toNNReal_coe] using
      (hc.sub h).div_const (Real.sqrt (2*α/(n : ℝ)))
  exact hl.limUnder_eq
end
end GinibrePoincare

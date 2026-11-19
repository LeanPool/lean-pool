/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLampertiFunctional.lean and
GinibreStochasticCenterLampertiScalarFunctional.lean, whose shared argument is stated here once
for an arbitrary real-valued radius.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Lamperti path functionals of a real radius

A path `p` in a space `X` is read through a real-valued radius `R : X → ℝ`. Its Lamperti
functional is the increment of `√(R ∘ p)` from `√r₀`, minus the time integral of a drift
`b ∘ R ∘ p`, divided by a scale `σ`. The functional is built from actual finite Riemann sums,
so it is measurable on the full path space without any measurability assumption on an ordinary
path integral, and it equals the integral form along continuous paths with positive radius.

The radial Lamperti functional (`R = pairwiseRadius`) and the scalar center Lamperti functional
(`R = Complex.normSq`) are both instances of this construction. -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The Riemann-sum Lamperti functional of a path `p` read through the radius `R`: the increment
of `√(R (p t))` from `√r₀`, minus a `k + 1`-point Riemann sum of the drift `b ∘ R ∘ p`, over the
scale `σ`. -/
def lampertiRadiusRiemannFunctional {X : Type*} (R : X → ℝ) (b : ℝ → ℝ) (r₀ σ : ℝ) (k : ℕ)
    (p : ℝ≥0 → X) (t : ℝ≥0) : ℝ :=
  (Real.sqrt (R (p t))-Real.sqrt r₀-
    ∑ i : Fin (k+1), b (R (p (ginibreUniformBrownianTime t k i)))*((t : ℝ)/((k : ℝ)+1))) / σ

/-- The pathwise Lamperti functional of a path `p` read through the radius `R`: the limit as
`k → ∞` of the Riemann-sum functionals `lampertiRadiusRiemannFunctional R b r₀ σ k p t`. -/
def lampertiRadiusPathFunctional {X : Type*} (R : X → ℝ) (b : ℝ → ℝ) (r₀ σ : ℝ)
    (p : ℝ≥0 → X) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun k => lampertiRadiusRiemannFunctional R b r₀ σ k p t)

theorem lampertiRadiusRiemannFunctional_measurable {X : Type*} [MeasurableSpace X]
    {R : X → ℝ} {b : ℝ → ℝ} (hR : Measurable R) (hb : Measurable b) (r₀ σ : ℝ) (k : ℕ)
    (t : ℝ≥0) :
    Measurable (fun p => lampertiRadiusRiemannFunctional R b r₀ σ k p t) := by
  have hr (s : ℝ≥0) : Measurable (fun p : ℝ≥0 → X => R (p s)) :=
    hR.comp (measurable_pi_apply s)
  have hg : Measurable (fun p : ℝ≥0 → X => ∑ i : Fin (k+1),
      b (R (p (ginibreUniformBrownianTime t k i)))*((t : ℝ)/((k : ℝ)+1))) := by
    apply Finset.measurable_sum
    intro i _
    exact (hb.comp (hr _)).mul_const _
  exact (((Real.continuous_sqrt.measurable.comp (hr t)).sub measurable_const).sub hg).div_const _

theorem lampertiRadiusPathFunctional_measurable {X : Type*} [MeasurableSpace X]
    {R : X → ℝ} {b : ℝ → ℝ} (hR : Measurable R) (hb : Measurable b) (r₀ σ : ℝ) :
    Measurable (lampertiRadiusPathFunctional R b r₀ σ) := by
  apply Measurable.of_eval
  intro t
  exact (StronglyMeasurable.limUnder (fun k =>
    (lampertiRadiusRiemannFunctional_measurable hR hb r₀ σ k t).stronglyMeasurable)).measurable

theorem lampertiRadiusPathFunctional_eq_integral {X : Type*} [TopologicalSpace X]
    {R : X → ℝ} {b : ℝ → ℝ} (hR : Continuous R) (hb : ContinuousOn b (Ioi 0)) (r₀ σ : ℝ)
    (p : ℝ≥0 → X) (hp : Continuous p) (hpos : ∀ s, 0 < R (p s)) (t : ℝ≥0) :
    lampertiRadiusPathFunctional R b r₀ σ p t =
      (Real.sqrt (R (p t))-Real.sqrt r₀-∫ s in (0 : ℝ)..t, b (R (p s.toNNReal))) / σ := by
  let w := fun s : ℝ => b (R (p s.toNNReal))
  have hw : Continuous w :=
    hb.comp_continuous (hR.comp (hp.comp continuous_real_toNNReal)) (fun s => hpos _)
  have h := itoContinuousScalarRiemann_fin_tendsto w t hw.continuousOn
  have hc : Tendsto (fun _ : ℕ => Real.sqrt (R (p t))-Real.sqrt r₀) atTop
      (𝓝 (Real.sqrt (R (p t))-Real.sqrt r₀)) := tendsto_const_nhds
  have hl : Tendsto (fun k => lampertiRadiusRiemannFunctional R b r₀ σ k p t) atTop
      (𝓝 ((Real.sqrt (R (p t))-Real.sqrt r₀-∫ s in (0 : ℝ)..t, w s) / σ)) := by
    simpa only [lampertiRadiusRiemannFunctional, w, Real.toNNReal_coe] using
      (hc.sub h).div_const σ
  exact hl.limUnder_eq

end
end GinibrePoincare

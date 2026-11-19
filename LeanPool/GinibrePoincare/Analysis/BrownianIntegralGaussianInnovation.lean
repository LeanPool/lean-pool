/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianInnovation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianAugmentedRadialIncrement

/-!
# Brownian integral Gaussian innovation

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUnitInnovation_gaussian_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Actual scalar innovation formed by a predictable unit vector and the fresh
coordinate Brownian increment. -/
def brownianUnitInnovation {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : Ω → EuclideanSpace ℝ ι) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  inner ℝ (u ω) (WithLp.toLp 2 (fun j => B j (s+t) ω-B j s ω))

/-- A genuine past-measurable unit-vector innovation is Gaussian of variance
t and independent of every actual random variable measurable in the whole
completed Brownian past. -/
theorem brownianUnitInnovation_gaussian_independent
    {Ω ι A : Type*} [mAmbient : MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace A] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0)
    (u : Ω → EuclideanSpace ℝ ι)
    (hu : @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ u)
    (hunit : ∀ ω, ‖u ω‖ = 1) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) (i : ι) :
    HasLaw (brownianUnitInnovation B u s t) (gaussianReal 0 t) P ∧
      IndepFun Y (brownianUnitInnovation B u s t) P := by
  classical
  let W := fun ω => (Y ω, u ω)
  obtain ⟨hl, hi, hcoord, hindcoord, he⟩ := brownianFamily_augmented_radial_fresh_increment
    B P hB hind s t W (hY.prodMk hu) (fun p : A × EuclideanSpace ℝ ι => p.2)
    measurable_snd i
  have heq : (fun ω => (brownianRadialFrame (u ω) (EuclideanSpace.single i 1)
      (WithLp.toLp 2 (fun j => B j (s+t) ω-B j s ω))) i) =
      brownianUnitInnovation B u s t := by
    funext ω
    have hu0 : u ω ≠ 0 := by
      intro hh
      have := hunit ω
      simp [hh] at this
    have hh := he ω
    simpa [W, brownianRadialUnitVector, hu0, hunit ω, brownianUnitInnovation] using hh
  constructor
  · have hc := hcoord i
    change HasLaw (fun ω => (brownianRadialFrame (u ω) (EuclideanSpace.single i 1)
      (WithLp.toLp 2 (fun j => B j (s+t) ω-B j s ω))) i) (gaussianReal 0 t) P at hc
    rwa [heq] at hc
  · have hh := hi.comp measurable_fst (show Measurable (fun x : EuclideanSpace ℝ ι => x i) by
      fun_prop)
    simpa only [Function.comp_def, W, heq] using hh

end
end GinibrePoincare

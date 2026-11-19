/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOUReversalWeight.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUContinuousReversal
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Ginibre Hamiltonian Gaussian OU reversal weight

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `invariant_measure_withDensity_of_invariant_weight`,
`gradientPathReversalWeight_reverse`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

theorem invariant_measure_withDensity_of_invariant_weight
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (R : E → E)
    (hR : Measurable R) (hμ : μ.map R = μ) (w : E → ENNReal)
    (hw : Measurable w) (hwr : ∀ x, w (R x) = w x) :
    (μ.withDensity w).map R=μ.withDensity w := by
  ext s hs
  rw [Measure.map_apply hR hs, withDensity_apply _ (hR hs), withDensity_apply _ hs]
  have hm : Measurable (s.indicator w) := hw.indicator hs
  have he : (R ⁻¹' s).indicator w = (s.indicator w) ∘ R := by
    funext x
    by_cases h : R x ∈ s
    · simp [h, hwr]
    · simp [h]
  rw [← lintegral_indicator (hR hs), he]
  simp only [Function.comp_apply]
  rw [← lintegral_map hm hR]
  rw [hμ, lintegral_indicator hs]

/-- The path weight `exp (-(V (x 0) + V (x T)) / 2 + ∫ s in 0..T, A (x s))`, as an extended
nonnegative real. -/
def gradientPathReversalWeight {E : Type*} (T : ℝ) (V A : E → ℝ) (x : ℝ → E) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(V (x 0)+V (x T))/2 + ∫ s in (0 : ℝ)..T, A (x s)))

theorem gradientPathReversalWeight_reverse {E : Type*} (T : ℝ) (V A : E → ℝ) (x : ℝ → E) :
    gradientPathReversalWeight T V A (fun s => x (T-s)) = gradientPathReversalWeight T V A x := by
  unfold gradientPathReversalWeight
  have hi := intervalIntegral.integral_comp_sub_left (fun s => A (x s)) (a := 0) (b := T) T
  simp only [sub_self, sub_zero] at hi ⊢
  rw [hi]
  congr 2
  ring

end
end GinibrePoincare

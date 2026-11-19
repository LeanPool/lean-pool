/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialSobolevClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreL2Norm
public import LeanPool.GinibrePoincare.Analysis.GinibreRadialSobolevCore
public import LeanPool.GinibrePoincare.Analysis.EntropyL2Closure
public import LeanPool.GinibrePoincare.Analysis.GaussianRadialLift
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Radial Sobolev closure

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `radialSobolevCore_has_pair`, `radialSobolevClosure_lsi_of_core`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- Entropy respects equality of representatives almost everywhere. -/
theorem squareEntropy_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ} (h : f =ᵐ[μ] g) : squareEntropy μ f = squareEntropy μ g := by
  apply squareEntropy_eq_of_moments
  · apply integral_congr_ae
    exact h.mono (fun x hx => by dsimp; rw [hx])
  · apply integral_congr_ae
    exact h.mono (fun x hx => by dsimp; rw [hx])

/-- Once the actual smooth radial core inequality is proved, its full L²
value-gradient Sobolev extension follows, including finiteness of entropy. -/
theorem radialSobolevClosure_lsi_of_core (n : ℕ) (hn : 0 < n)
    (hcore : ∀ f : Configuration n → ℝ, IsRadialSobolevCore f →
      ginibreSquareEntropy n f ≤ smoothGinibreEnergy n f) :
    ∀ p ∈ radialSobolevClosure n,
      Integrable (fun z => p.1 z ^ 2 * Real.log (p.1 z ^ 2)) (ginibreMeasure n) ∧
        squareEntropy (ginibreMeasure n) p.1 ≤ (1 / (n : ℝ)) * ‖p.2‖ ^ 2 := by
  have := ginibreMeasure_isProbabilityMeasure hn
  apply entropy_bound_on_closure
  intro p hp
  obtain ⟨f, hf, hv, hg⟩ := hp
  have he : squareEntropy (ginibreMeasure n) p.1 = ginibreSquareEntropy n f :=
    squareEntropy_congr_ae _ hv
  have hgrad : ‖p.2‖ ^ 2 = ∫ z, realGradientNormSq f z ∂ginibreMeasure n := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hg] with z hz
    rw [hz, ginibreEuclideanGradient_norm_sq]
  constructor
  · apply (integrable_square_mul_log_ginibre hn hf.1.1.continuous hf.1.2.1).congr
    exact hv.symm.mono (fun z hz => by dsimp; rw [hz])
  · rw [he, hgrad]
    exact hcore f hf

end
end GinibrePoincare

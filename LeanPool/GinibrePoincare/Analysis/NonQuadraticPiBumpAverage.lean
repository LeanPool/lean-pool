/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiBumpAverage.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBump

/-!
# Non quadratic pi bump average

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `piL2BumpAverage_tendsto`.

The product bump average is the general kernel average `lebesgueL2KernelAverage` of
`LebesgueL2Mollification` with kernel `piPlanarBump d φ`; its lemmas are specializations.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
/-- The mollification of `u ∈ L²(ℂ^d)` by the product bump: the Bochner integral of the
translates `lebesgueL2Translate d y u` against the weight `piPlanarBump d φ y`. -/
def piL2BumpAverage (d : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (Configuration d))) : Lp W 2 (volume : Measure (Configuration d))
        :=
  lebesgueL2KernelAverage d (piPlanarBump d φ) u

omit [CompleteSpace W] in
theorem integrable_piL2BumpIntegrand (d : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (Configuration d))) :
    Integrable (fun y => piPlanarBump d φ y • lebesgueL2Translate d y u) :=
  integrable_lebesgueL2KernelIntegrand d (piPlanarBump_continuous d φ)
    (piPlanarBump_compact d φ) u

theorem piL2BumpAverage_error_le (d : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (Configuration d))) (ε : ℝ)
    (he : ∀ y ∈ Function.support (piPlanarBump d φ),
      ‖lebesgueL2Translate d y u - u‖ ≤ ε) :
    ‖piL2BumpAverage d φ u - u‖ ≤ ε :=
  lebesgueL2KernelAverage_error_le d (piPlanarBump_continuous d φ) (piPlanarBump_compact d φ)
    (piPlanarBump_nonneg d φ) (piPlanarBump_integral d φ) u ε he

theorem piL2BumpAverage_tendsto (d : ℕ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp W 2 (volume : Measure (Configuration d))) :
    Tendsto (fun m => piL2BumpAverage d (φ m) u) atTop (𝓝 u) :=
  lebesgueL2KernelAverage_tendsto d (fun m => piPlanarBump d (φ m))
    (fun m => piPlanarBump_continuous d (φ m)) (fun m => piPlanarBump_compact d (φ m))
    (fun m => piPlanarBump_nonneg d (φ m)) (fun m => piPlanarBump_integral d (φ m)) _ hφ
    (fun m y hy => by
      simpa only [dist_zero_right] using (piPlanarBump_support_ball d (φ m) y hy).le) u
end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenSmoothSolver.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenFundamental
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenPotential

/-!
# Correspondence auxiliary Cauchy Green smooth solver

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreenSmooth_compact_solvability`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The literal Cauchy–Green convolution solves ∂bar u=a for every actual
smooth compact planar source, with a genuine smooth global solution. -/
theorem cauchyGreenPotential_solves_dbar (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (z : ℂ) :
    planarDbar (cauchyGreenPotential a) z = a z := by
  let θ : ℂ → ℂ := fun y => a (z-y)
  have hθ : ContDiff ℝ 1 θ := (ha.of_le (by simp)).comp
    (contDiff_const.sub contDiff_id)
  have hcθ : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have h := cauchyGreenKernel_fundamental_identity θ hθ hcθ
  have hder (y : ℂ) : planarDbar θ y = -planarDbar a (z-y) :=
    planarDbar_sub_left a (ha.differentiable (by simp)) z y
  simp_rw [hder, mul_neg, integral_neg] at h
  rw [cauchyGreenPotential_dbar_integral a ha hc z]
  have hh := neg_injective h
  simpa [θ] using hh

theorem cauchyGreenSmooth_compact_solvability (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ z, planarDbar u z = a z :=
  ⟨cauchyGreenPotential a, cauchyGreenPotential_contDiff a ha hc,
    cauchyGreenPotential_solves_dbar a ha hc⟩

end
end GinibrePoincare

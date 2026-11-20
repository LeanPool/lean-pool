/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungKernel.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungPairing
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenKernel

/-!
# Correspondence Dolbeault Young kernel

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultCauchyGreenL2_norm`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The Cauchy–Green kernel restricted (by an indicator) to the closed ball of radius `R`. -/
def dolbeaultTruncatedCauchyGreen (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall 0 R).indicator cauchyGreenKernel

theorem dolbeaultTruncatedCauchyGreen_integrable (R : ℝ) :
    Integrable (dolbeaultTruncatedCauchyGreen R) volume := by
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (cauchyGreenKernel_locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) R))

/-- The locally singular Cauchy–Green kernel gives a genuine bounded coordinate
homotopy on ordinary L² after truncation; no L² assumption on the kernel is used. -/
def dolbeaultCauchyGreenL2 {n : ℕ} (j : Fin n) (R : ℝ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  dolbeaultCoordinateConvolutionCLM j (dolbeaultTruncatedCauchyGreen R)
    (dolbeaultTruncatedCauchyGreen_integrable R)

theorem dolbeaultCauchyGreenL2_norm {n : ℕ} (j : Fin n) (R : ℝ)
    (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultCauchyGreenL2 j R u‖ ≤
      (∫ y : ℂ, ‖dolbeaultTruncatedCauchyGreen R y‖)*‖u‖ :=
  dolbeaultCoordinateConvolution_norm j (dolbeaultTruncatedCauchyGreen R) u

end
end GinibrePoincare

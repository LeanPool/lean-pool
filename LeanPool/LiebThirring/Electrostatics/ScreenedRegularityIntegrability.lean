/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityBasic
public import LeanPool.LiebThirring.Analysis.FundamentalSolutionIntegrability

/-!
# Integrability of screened-potential test integrands

Continuity and compact support give integrability of screened-potential test integrands.
-/

public section

open MeasureTheory Laplacian
open scoped NNReal

namespace LiebThirring

theorem integrable_screenedPotentialReal_mul_laplacian {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    {f : Position → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun x => screenedPotentialReal Z R x * Δ f x) :=
  ((continuous_screenedPotentialReal hM Z R hR).mul (continuous_laplacian_position
    hf)).integrable_of_hasCompactSupport (hasCompactSupport_laplacian_position hfc).mul_left

end LiebThirring

end

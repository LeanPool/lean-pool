/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockPayload
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailBoundedProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# UpperWaveTailBoundedGrid

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The bounded good-mass wave-tail lane through the triadic grid

This file weakens the literal bounded wave-tail Whitney sum to the terminal
exceptional exponent, restores the exact outer mean and one-coordinate factor,
translates the centered witness to each descendant cube, and applies the
strict-descendant triadic maximum.  The resulting scale keeps the profile-tail
triangle constant, the squared `sigma` pole, the tuned exponential decay, and
exactly one outer mean coefficient.

The root row, rare and collar witnesses, terminal absorption, other named
lanes, and cutoff observable are not treated here.  These declarations are
conditional internal A for the bounded good-mass wave-tail lane.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- The terminal exceptional exponent is weaker than the exponent of the
bounded wave-tail witness throughout the profile window. -/
theorem upperProfileTargetSigma_le_tailSigma {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    upperProfileTargetSigma sigma ≤ upperProfileTailSigma sigma := by
  have hden : 0 < 1 + sigma / 4 := by linarith
  rw [upperProfileTargetSigma, upperProfileTailSigma, upperProfileSigma]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hden]
  nlinarith [sq_nonneg sigma]


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity

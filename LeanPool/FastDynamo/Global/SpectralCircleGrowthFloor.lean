/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.CorrectedRieszProjectionSpectralCalculus
public import LeanPool.FastDynamo.Global.DomainOperatorNumericalRange
public import LeanPool.FastDynamo.Global.MatchingCellScalingParameters
public import LeanPool.FastDynamo.Operator.CompactBaseFredholm
public import LeanPool.FastDynamo.Operator.FixedSectorLowerOrderDecay

/-!
# The growth floor of a spectral circle on its open disk

`SpectralCircle.growthFloor_le_re_of_mem_ball`: every point of the open disk of a spectral
circle has real part at least the circle's growth floor `center.re - radius`.  This is the
open-disk companion of `SpectralCircle.growthFloor_le_re`; it converts the eigenvalue
localization of `exists_domain_eigenpair_mem_ball` into the lower bound `g_* ≤ Re λ` of the
proof of `prop:global-spectral-transfer`, in `Global/HorizontalSpectralExtraction.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

/-! ## Growth floor from an open-disk membership -/

namespace SpectralCircle

/-- Every point of the open disk obeys the growth-floor bound.  This is the
open-disk companion of `SpectralCircle.growthFloor_le_re`; it is what the
eigenvalue localization of `exists_domain_eigenpair_mem_ball` produces. -/
theorem growthFloor_le_re_of_mem_ball {Gamma : SpectralCircle} {z : ℂ}
    (hz : z ∈ Metric.ball Gamma.center Gamma.radius) :
    Gamma.growthFloor ≤ z.re :=
  SpectralCircle.growthFloor_le_re (Γ := Gamma)
    (Metric.ball_subset_closedBall hz)

end SpectralCircle

end

end FastDynamo

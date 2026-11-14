/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedDeepBandTailProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHsepResidualScale

/-!
# SharpFramedDeepBandTailOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Orlicz split for the framed centered deep-band tail

This file applies the already-verified upper-profile separation split to the
literal squared centered deep-band tail in one good-cell Whitney lane.  The
unframed square uses the exact `Gamma_1` certificate supplied by the grouped
deep-band estimate, and its deterministic `2` witness is identified with the
separately computed ordinary layer profile.

Only the normalized inner good-mass centered-tail lane is treated.  The outer
`probeMeanGoodWaveConst M * vecNormSq p`, the root row, good base, band mean,
after-band and wave-tail lanes, every collar lane, layer/grid/depth
aggregation, and the cutoff observable are absent.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Literal carriers -/

/-- The common sharp coefficient and good-layer mass square root for the
centered deep-band square. -/
def probeSharpDeepBandTailGoodMassCoeff (d n : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (probeSharpLayerMassEnvelope d n)


theorem probeSharpDeepBandTailGoodMassCoeff_nonneg (d n : ℕ) :
    0 ≤ probeSharpDeepBandTailGoodMassCoeff d n := by
  rw [probeSharpDeepBandTailGoodMassCoeff]
  positivity


/-! ## Exact descendant identity and unframed certificate -/


/-! ## Explicit ordinary and rare lanes -/


end

end Algsuperdiff.Section3.Provider.Multiscale

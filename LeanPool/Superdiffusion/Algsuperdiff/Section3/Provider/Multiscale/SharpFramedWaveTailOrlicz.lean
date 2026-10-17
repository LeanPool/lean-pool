/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHsepResidualScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandOrlicz

/-!
# SharpFramedWaveTailOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Orlicz split for the framed random-depth wave tail

This file applies the upper-profile separation split to the literal squared
random-depth wave-tail term in one good-cell Whitney lane.  Unlike the
after-band and centered deep-band squares, the unframed input is not
`Gamma_1`: at the profile parameters it has the exact exponent
`upperProfileTailSigma sigma = (1 + sigma / 4)^{-1}`.  The bounded hsep
witness retains that exponent, while the product with the hsep residual has
the target exceptional exponent `Gamma_((1 - sigma) / 3)`.

Only the normalized inner good-mass wave-tail lane is treated.  The outer
`probeMeanGoodWaveConst M * vecNormSq p`, all other good/collar lanes, root
row, layer/grid/depth aggregation, and cutoff observable are absent.
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
random-depth wave-tail square. -/
def probeSharpWaveTailGoodMassCoeff (d n : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (probeSharpLayerMassEnvelope d n)


theorem probeSharpWaveTailGoodMassCoeff_nonneg (d n : ℕ) :
    0 ≤ probeSharpWaveTailGoodMassCoeff d n := by
  rw [probeSharpWaveTailGoodMassCoeff]
  positivity


/-! ## Exact descendant identity -/


/-! ## Profile-tail input and explicit split -/


end

end Algsuperdiff.Section3.Provider.Multiscale

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BfaPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpMeanLayerEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveTermTranslation

/-!
# SharpMeanLayerProperties

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Elementary properties of the sharp mean-layer envelope

This file proves the sign and measurability facts needed to turn the sharp
mean-layer domination into Orlicz lanes.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

theorem probeSharpLayerMassEnvelope_nonneg (d n : ℕ) :
    0 ≤ probeSharpLayerMassEnvelope d n := by
  rw [probeSharpLayerMassEnvelope]
  positivity


end

end Algsuperdiff.Section3.Provider.Multiscale

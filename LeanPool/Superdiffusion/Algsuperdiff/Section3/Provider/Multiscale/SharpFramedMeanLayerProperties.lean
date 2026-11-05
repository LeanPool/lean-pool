/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayerEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpMeanLayerProperties

/-!
# SharpFramedMeanLayerProperties

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Sign and measurability of the framed sharp layer envelope

These elementary properties support later Orlicz aggregation.
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


theorem measurable_probeSharpLayerFrame
    (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ n : ℕ) (i : ℤ) :
    Measurable (probeSharpLayerFrame M m E b k₀ n i) := by
  exact measurable_comp_hsep M m E b fun h : ℕ =>
    probeMeanLayerFrame M m (whitneyScaleSeq b h k₀) n i


end

end Algsuperdiff.Section3.Provider.Multiscale

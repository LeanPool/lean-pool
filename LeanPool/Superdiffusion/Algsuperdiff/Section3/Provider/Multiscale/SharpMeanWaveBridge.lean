/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam1PerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpSimplexMean
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SuperposedConclusion

/-!
# SharpMeanWaveBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}


def probeLayerWaveFactor (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ)
    (n : ℕ) (L : ℤ) (omega : CutoffSample d) : ℝ :=
  M.gamma * (3 : ℝ) ^ (-(2 * M.gamma *
      ((m - (n : ℤ) - (hn n : ℤ) : ℤ) : ℝ))) *
    Real.sqrt (layerSimplexFourthMass m hn n
      (m - (n : ℤ) - (hn n : ℤ)) L omega)


end

end Algsuperdiff.Section3.Provider.Multiscale

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTerm

/-!
# WaveSharpUpper

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A macroscopic cube-averaged wave term

This internal analytic provider keeps the cube-averaged `L⁴` carrier for the
macroscopic increment.  It obtains the `sqrt gamma * sqrt (L-ell) *
3^(gamma*(L-ell))` `Gamma₂` scale directly from the proved increment estimate,
with no translated-cube maximum and therefore no grid penalty.
-/


namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-- A dimension-only constant for the macroscopic `L⁴` term. -/
def waveSharpUpperConst (d : ℕ) : ℝ :=
  (Real.exp 1) ^ (1 / 4 : ℝ) *
    (IndependentSums.gammaMomentConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        ((d : ℝ) ^ 2 * geometricConcentrationConst))) * 2


/-- The macroscopic `L⁴` wave term, without a translated-cube
maximum. -/
def waveSharpUpperTerm (M : ABKModel d) (lout ell L : ℤ)
    (omega : CutoffSample d) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    streamIncrementLpNorm 4 lout ell L omega.1


end

end Algsuperdiff.Section3.Provider.Multiscale

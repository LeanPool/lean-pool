/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.ComponentPotentialBadFamily

/-!
# FiniteComponentPotential

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Zero-trace potential for finite bad-component sums

This file packages the one-component result from
`ComponentPotentialBadFamily` under finite summation.  It is the finite
approximation input for the closed-`L²` construction of the full superposed
competitor.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport Set
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- A finite sum of actual bad-component slope defects is a zero-trace
potential field on the open root cube.  The nonzero-dimension instance needed
by the component theorem is derived there from `M`. -/
theorem potentialZeroTraceFieldOn_sum_globalCompetitorSlope_sub_badComponents
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    (A : Finset (Set (TriadicCube d)))
    (hA : ∀ C ∈ A, C ∈ badComponents
      (badFamily M m (whitneyScale M m E b k₀ omega) omega))
    (p : Vec d) :
    HCPolySupport.Book.Ch01.PotentialZeroTraceFieldOn
      (openCubeSet (originCube d m))
      (fun x => ∑ C ∈ A, (globalCompetitorSlope m
        (simplexScale m (whitneyScale M m E b k₀ omega)
          (componentWindowLayer m (whitneyScale M m E b k₀ omega) C)) C p x - p)) := by
  apply potentialZeroTraceFieldOn_sum A
  intro C hC
  exact potentialZeroTraceFieldOn_globalCompetitorSlope_sub_badComponent
    hb0 hb hk₀ hne (hA C hC) p

end

end Algsuperdiff.Section3.Provider.Affine

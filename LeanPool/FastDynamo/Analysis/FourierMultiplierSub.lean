/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneBesselWeight

/-!
# Additivity of whole-plane Fourier multipliers

This file proves that the Fourier multiplier on whole-plane tempered distributions is additive
in its scalar symbol (`fourierMultiplierCLM_sub`), the identity used to identify a multiplier
whose symbol is a difference of two symbols with the difference of the two multipliers.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped FourierTransform LineDeriv SchwartzMap

/-- Fourier multipliers are additive in their scalar symbol. -/
theorem fourierMultiplierCLM_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g h : WholePlane → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) :
    TemperedDistribution.fourierMultiplierCLM F (g - h) =
      TemperedDistribution.fourierMultiplierCLM F g -
        TemperedDistribution.fourierMultiplierCLM F h := by
  apply ContinuousLinearMap.ext
  intro T
  simp only [TemperedDistribution.fourierMultiplierCLM_apply]
  rw [TemperedDistribution.smulLeftCLM_sub hg hh]
  simp only [sub_apply]
  exact map_sub (FourierTransform.fourierInvₗ ℂ _) _ _

end

end FastDynamo

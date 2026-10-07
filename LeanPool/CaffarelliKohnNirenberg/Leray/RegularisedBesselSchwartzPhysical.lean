/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselEmbedding

/-!
# Physical L² realization of Schwartz Bessel fields

The inverse Fourier-weight realization of a canonical Schwartz
Sobolev lift is its original spatial L² class.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The canonical Schwartz Bessel lift realizes physically as the
original Schwartz L² field. -/
theorem regularisedBesselSobolevToL2_schwartz
    (s : ℝ) (hs : 0 ≤ s)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedBesselSobolevToL2 s hs
      (regularisedBesselOfSchwartz s ψ) = ψ.toLp 2 := by
  apply (LinearMap.ker_eq_bot.mp
    (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ComplexVec3) (μ := volume) (p := 2)))
  exact (regularisedBesselSobolevToL2_toTemperedDistribution_eq
    s hs (regularisedBesselOfSchwartz s ψ)).trans
      ((regularisedBesselOfSchwartz_toDistr s ψ).trans
        (Lp.toTemperedDistribution_toLp_eq (p := 2) (μ := volume) ψ).symm)

end CKN.Leray

end

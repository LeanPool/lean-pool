/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzDenseRange

/-!
# Linear Schwartz core of the Bessel potential space

The canonical Schwartz lift is linear, and its range is dense in
the complete complex vector-valued Bessel space.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The canonical vector Bessel lift is additive. -/
theorem regularisedBesselOfSchwartz_add
    (s : ℝ) (ψ χ : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedBesselOfSchwartz s (ψ + χ) =
      regularisedBesselOfSchwartz s ψ +
        regularisedBesselOfSchwartz s χ := by
  apply BesselPotentialSpace.ext
  simp only [regularisedBesselOfSchwartz_toDistr,
    BesselPotentialSpace.toDistr_add, map_add]

/-- The canonical vector Bessel lift commutes with complex scaling. -/
theorem regularisedBesselOfSchwartz_smul
    (s : ℝ) (c : ℂ) (ψ : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedBesselOfSchwartz s (c • ψ) =
      c • regularisedBesselOfSchwartz s ψ := by
  apply BesselPotentialSpace.ext
  simp only [regularisedBesselOfSchwartz_toDistr,
    BesselPotentialSpace.toDistr_smul, map_smul]

/-- The canonical vector Schwartz lift as a complex linear map. -/
@[expose]
def regularisedBesselSchwartzLinear (s : ℝ) :
    𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ]
      BesselPotentialSpace L2Vec3 ComplexVec3 s 2 where
  toFun := regularisedBesselOfSchwartz s
  map_add' := regularisedBesselOfSchwartz_add s
  map_smul' := regularisedBesselOfSchwartz_smul s

end CKN.Leray

end

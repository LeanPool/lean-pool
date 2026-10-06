/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBilinear
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzCore

/-!
# Canonical Bessel lifts of Schwartz tensor fields

The tensor produced by regularized Schwartz multiplication is lifted
linearly into the complete Bessel potential space.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete Sobolev field represented by a complex Schwartz tensor. -/
@[expose]
def regularisedTensorBesselOfSchwartz (s : ℝ)
    (ψ : 𝓢(L2Vec3, ComplexTensor3)) :
    BesselPotentialSpace L2Vec3 ComplexTensor3 s 2 :=
  (ψ.memSobolev (s := s) (p := 2)).toBesselPotentialSpace

/-- The canonical tensor lift retains its Schwartz distribution. -/
theorem regularisedTensorBesselOfSchwartz_toDistr
    (s : ℝ) (ψ : 𝓢(L2Vec3, ComplexTensor3)) :
    (regularisedTensorBesselOfSchwartz s ψ).toDistr =
      (ψ : 𝓢'(L2Vec3, ComplexTensor3)) :=
  (ψ.memSobolev (s := s) (p := 2)).toBesselPotentialSpace_toDistr

/-- Canonical tensor Bessel lifting is additive. -/
theorem regularisedTensorBesselOfSchwartz_add
    (s : ℝ) (ψ χ : 𝓢(L2Vec3, ComplexTensor3)) :
    regularisedTensorBesselOfSchwartz s (ψ + χ) =
      regularisedTensorBesselOfSchwartz s ψ +
        regularisedTensorBesselOfSchwartz s χ := by
  apply BesselPotentialSpace.ext
  simp only [regularisedTensorBesselOfSchwartz_toDistr,
    BesselPotentialSpace.toDistr_add, map_add]

/-- Canonical tensor Bessel lifting commutes with complex scaling. -/
theorem regularisedTensorBesselOfSchwartz_smul
    (s : ℝ) (c : ℂ) (ψ : 𝓢(L2Vec3, ComplexTensor3)) :
    regularisedTensorBesselOfSchwartz s (c • ψ) =
      c • regularisedTensorBesselOfSchwartz s ψ := by
  apply BesselPotentialSpace.ext
  simp only [regularisedTensorBesselOfSchwartz_toDistr,
    BesselPotentialSpace.toDistr_smul, map_smul]

/-- The tensor Schwartz lift as a complex linear map. -/
@[expose]
def regularisedTensorBesselSchwartzLinear (s : ℝ) :
    𝓢(L2Vec3, ComplexTensor3) →ₗ[ℂ]
      BesselPotentialSpace L2Vec3 ComplexTensor3 s 2 where
  toFun := regularisedTensorBesselOfSchwartz s
  map_add' := regularisedTensorBesselOfSchwartz_add s
  map_smul' := regularisedTensorBesselOfSchwartz_smul s

end CKN.Leray

end

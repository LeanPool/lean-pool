/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMollifierSchwartz

/-!
# Regularized convolution on Schwartz velocity fields

The fixed complexified mollifier acts by Schwartz convolution on
complex Schwartz vector fields.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Schwartz convolution with the complexified regularized mollifier. -/
@[expose]
def regularisedSchwartzMollify
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) :
    𝓢(L2Vec3, ComplexVec3) :=
  SchwartzMap.convolution
    (ContinuousLinearMap.lsmul ℂ ℂ)
    (regularisedComplexMollifierSchwartz ρ ε hε) ψ

/-- The Schwartz mollification equals pointwise convolution with the
complexified real kernel. -/
theorem regularisedSchwartzMollify_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    regularisedSchwartzMollify ρ ε hε ψ x =
      MeasureTheory.convolution
        (fun y : L2Vec3 =>
          ((regMollifierKernel ρ ε hε y : ℝ) : ℂ))
        (ψ : L2Vec3 → ComplexVec3)
        (ContinuousLinearMap.lsmul ℂ ℂ) volume x := by
  rw [regularisedSchwartzMollify,
    SchwartzMap.convolution_apply]
  rfl

end CKN.Leray

end

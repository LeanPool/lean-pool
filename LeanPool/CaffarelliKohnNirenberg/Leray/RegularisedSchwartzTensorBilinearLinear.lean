/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorBesselSchwartz

/-!
# Bilinearity of the Schwartz tensor

Schwartz convolution and pointwise tensor pairing are linear in their
respective inputs, so the regularized tensor is bilinear.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Schwartz mollification by a fixed profile is complex linear. -/
@[expose]
def regularisedSchwartzMollifyLinear
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ] 𝓢(L2Vec3, ComplexVec3) :=
  (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (regularisedComplexMollifierSchwartz ρ ε hε)).toLinearMap

/-- The linear mollifier map agrees with Schwartz convolution. -/
theorem regularisedSchwartzMollifyLinear_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedSchwartzMollifyLinear ρ ε hε g =
      regularisedSchwartzMollify ρ ε hε g := rfl

/-- The regularized tensor with two Schwartz inputs is complex bilinear. -/
@[expose]
def regularisedSchwartzTensorBilinearLinear
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ]
      𝓢(L2Vec3, ComplexVec3) →ₗ[ℂ]
        𝓢(L2Vec3, ComplexTensor3) :=
  LinearMap.mk₂ ℂ (regularisedSchwartzTensorBilinear ρ ε hε)
    (by
      intro g h f
      simp only [regularisedSchwartzTensorBilinear,
        ← regularisedSchwartzMollifyLinear_apply,
        map_add, add_apply])
    (by
      intro c g f
      simp only [regularisedSchwartzTensorBilinear,
        ← regularisedSchwartzMollifyLinear_apply,
        map_smul, smul_apply])
    (by
      intro g f h
      simp only [regularisedSchwartzTensorBilinear, map_add])
    (by
      intro c g f
      simp only [regularisedSchwartzTensorBilinear, map_smul])

/-- The bundled bilinear tensor has the original pointwise output. -/
theorem regularisedSchwartzTensorBilinearLinear_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (g f : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedSchwartzTensorBilinearLinear ρ ε hε g f =
      regularisedSchwartzTensorBilinear ρ ε hε g f := rfl

end CKN.Leray

end

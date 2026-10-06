/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselOrderedDistribution

/-!
# Continuous distribution embedding of Sobolev fields

The complete Bessel potential carrier maps continuously to tempered
distributions. This embedding lets distributional derivatives be compared
under strong Sobolev limits.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The underlying tempered distribution depends continuously and
complex linearly on a Bessel-potential field. -/
@[expose]
def regularisedBesselToDistrCLM (s : ℝ) :
    BesselPotentialSpace L2Vec3 ComplexVec3 s 2 →L[ℂ]
      𝓢'(L2Vec3, ComplexVec3) :=
  (TemperedDistribution.besselPotential L2Vec3 ComplexVec3 (-s)).comp
    ((MeasureTheory.Lp.toTemperedDistributionCLM ComplexVec3 volume 2).comp
      (BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 s 2).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem regularisedBesselToDistrCLM_apply (s : ℝ)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    regularisedBesselToDistrCLM s v = v.toDistr := by
  have h : regularisedBesselToDistrCLM s v = TemperedDistribution.besselPotential L2Vec3 ComplexVec3
      (-s) v.toLp := by
    simp [regularisedBesselToDistrCLM, BesselPotentialSpace.toLpₗᵢ_apply]
  rw [h]
  exact BesselPotentialSpace.besselPotential_neg_toLp_eq

/-- The continuous linear map taking an ordered list of distributional
directional derivatives. -/
@[expose]
def regularisedOrderedDistributionDerivativeCLM
    (α : List L2Vec3) :
    𝓢'(L2Vec3, ComplexVec3) →L[ℂ]
      𝓢'(L2Vec3, ComplexVec3) :=
  α.foldl (fun L m =>
    (LineDeriv.lineDerivOpCLM ℂ
      (𝓢'(L2Vec3, ComplexVec3)) m).comp L)
    (ContinuousLinearMap.id ℂ (𝓢'(L2Vec3, ComplexVec3)))

@[simp]
theorem regularisedOrderedDistributionDerivativeCLM_apply
    (α : List L2Vec3) (D : 𝓢'(L2Vec3, ComplexVec3)) :
    regularisedOrderedDistributionDerivativeCLM α D =
      α.foldl (fun F m => LineDeriv.lineDerivOp m F) D := by
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α m ih =>
      simp only [regularisedOrderedDistributionDerivativeCLM,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        ContinuousLinearMap.comp_apply,
        LineDeriv.lineDerivOpCLM_apply]
      exact congrArg (LineDeriv.lineDerivOp m) ih

end CKN.Leray

end

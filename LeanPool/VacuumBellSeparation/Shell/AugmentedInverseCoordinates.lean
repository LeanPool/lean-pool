/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Inverse coordinates with retained auxiliary parameters

An invertible derivative in the active variables gives an ordinary
inverse-function chart after retaining the other variables unchanged.
This is a proved triangular derivative construction, not an assumed
submersion or coarea theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {E F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Augmented derivative equivalence of type `(E × N) ≃L[ℝ] (F × N)`. -/
noncomputable def augmentedDerivativeEquiv (L : E ≃L[ℝ] F) (M : N →L[ℝ] F) :
    (E × N) ≃L[ℝ] (F × N) :=
  (ContinuousLinearEquiv.prodComm ℝ E N).trans
    (((ContinuousLinearEquiv.refl ℝ N).skewProd L M).trans
      (ContinuousLinearEquiv.prodComm ℝ N F))

theorem augmentedDerivativeEquiv_apply (L : E ≃L[ℝ] F) (M : N →L[ℝ] F)
    (x : E × N) : augmentedDerivativeEquiv L M x = (L x.1 + M x.2, x.2) := rfl

theorem hasFDerivAt_augment_of_active {f : E × N → F}
    (hf : DifferentiableAt ℝ f 0) (L : E ≃L[ℝ] F)
    (hactive : HasFDerivAt (fun x : E => f (x, 0)) (L : E →L[ℝ] F) 0) :
    HasFDerivAt (fun q : E × N => (f q, q.2))
      (augmentedDerivativeEquiv L ((fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ E N)) :
        (E × N) →L[ℝ] (F × N)) 0 := by
  have hin : HasFDerivAt (fun x : E => f (x, 0))
      ((fderiv ℝ f 0).comp (ContinuousLinearMap.inl ℝ E N)) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.inl_apply, map_zero]
      using hf.hasFDerivAt.comp (0 : E)
      ((ContinuousLinearMap.inl ℝ E N).hasFDerivAt (x := (0 : E)))
  have hl := hin.unique hactive
  have hsplit (q : E × N) : fderiv ℝ f 0 q =
      L q.1 + fderiv ℝ f 0 (0, q.2) := by
    have hq : q = (q.1, 0) + (0, q.2) := by simp
    have hx := congrArg (fun A : E →L[ℝ] F => A q.1) hl
    calc
      fderiv ℝ f 0 q = fderiv ℝ f 0 ((q.1, 0) + (0, q.2)) := congrArg _ hq
      _ = fderiv ℝ f 0 (q.1, 0) + fderiv ℝ f 0 (0, q.2) := map_add _ _ _
      _ = _ := congrArg (fun y => y + fderiv ℝ f 0 (0, q.2)) hx
  refine (hf.hasFDerivAt.prodMk (ContinuousLinearMap.snd ℝ E N).hasFDerivAt).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro q
  exact Prod.ext (hsplit q) rfl

theorem hasStrictFDerivAt_augment_of_active {f : E × N → F}
    (hf : ContDiffAt ℝ ⊤ f 0) (L : E ≃L[ℝ] F)
    (hactive : HasFDerivAt (fun x : E => f (x, 0)) (L : E →L[ℝ] F) 0) :
    HasStrictFDerivAt (fun q : E × N => (f q, q.2))
      (augmentedDerivativeEquiv L ((fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ E N)) :
        (E × N) →L[ℝ] (F × N)) 0 :=
  (hf.prodMk (ContinuousLinearMap.snd ℝ E N).contDiff.contDiffAt).hasStrictFDerivAt
    (hasFDerivAt_augment_of_active (hf.differentiableAt (by simp)) L hactive) (by simp)

/-- Augmented local coordinates. -/
noncomputable def augmentedLocalCoordinates [CompleteSpace E] [CompleteSpace N]
    {f : E × N → F} (hf : ContDiffAt ℝ ⊤ f 0) (L : E ≃L[ℝ] F)
    (hactive : HasFDerivAt (fun x : E => f (x, 0)) (L : E →L[ℝ] F) 0) :
    OpenPartialHomeomorph (E × N) (F × N) :=
  (hasStrictFDerivAt_augment_of_active hf L hactive).toOpenPartialHomeomorph
    (fun q => (f q, q.2))

theorem augmentedLocalCoordinates_apply [CompleteSpace E] [CompleteSpace N]
    {f : E × N → F} (hf : ContDiffAt ℝ ⊤ f 0) (L : E ≃L[ℝ] F)
    (hactive : HasFDerivAt (fun x : E => f (x, 0)) (L : E →L[ℝ] F) 0) (q : E × N) :
    augmentedLocalCoordinates hf L hactive q = (f q, q.2) := rfl

theorem zero_mem_augmentedLocalCoordinates [CompleteSpace E] [CompleteSpace N]
    {f : E × N → F} (hf : ContDiffAt ℝ ⊤ f 0) (L : E ≃L[ℝ] F)
    (hactive : HasFDerivAt (fun x : E => f (x, 0)) (L : E →L[ℝ] F) 0) :
    0 ∈ (augmentedLocalCoordinates hf L hactive).source :=
  (hasStrictFDerivAt_augment_of_active hf L hactive).mem_toOpenPartialHomeomorph_source

end VacuumBellSeparation

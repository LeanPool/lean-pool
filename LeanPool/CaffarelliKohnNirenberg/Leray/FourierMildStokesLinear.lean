/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierStokesLinearity

/-!
# The bounded linear Stokes action used in the mild integral

For each positive elapsed time, `K(t)` is a bounded linear map from tensor
`L²` to velocity `L²`, with the Abel-kernel bound from
`lem:reg-multiplier-bounds`.
-/

public section

noncomputable section

namespace CKN.Leray

/-- The real-linear Stokes operator between tensor and vector `L²` spaces at positive time. -/
@[expose]
def realStokesLinearMap {t : ℝ} (ht : 0 < t) :
    RealTensorL2 →ₗ[ℝ] RealVectorL2 where
  toFun := realStokesOperator ht
  map_add' := realStokesOperator_add ht
  map_smul' := realStokesOperator_smul ht

/-- The continuous linear Stokes map at positive elapsed time. -/
@[expose]
def realStokesContinuousLinearMap {t : ℝ} (ht : 0 < t) :
    RealTensorL2 →L[ℝ] RealVectorL2 :=
  (realStokesLinearMap ht).mkContinuous
    (1 / Real.sqrt (2 * Real.exp 1 * t)) (by
      intro F
      exact realStokesOperator_norm_le ht F)

/-- Evaluation of the bounded linear Stokes map agrees with the Fourier
defined operator. -/
theorem realStokesContinuousLinearMap_apply {t : ℝ} (ht : 0 < t)
    (F : RealTensorL2) :
    realStokesContinuousLinearMap ht F = realStokesOperator ht F := rfl

end CKN.Leray

end

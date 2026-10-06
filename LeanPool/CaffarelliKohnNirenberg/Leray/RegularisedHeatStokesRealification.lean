/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEnergyIntervalReal

/-!
# Realification of the heat and Stokes operators

The complex Fourier heat and Stokes operators applied to complexified
real data are themselves complexifications of the corresponding real
physical operators.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Heat evolution of real physical data remains in the real subspace
of complex spatial L². -/
theorem heatSemigroup_complexify_real
    (t : ℝ) (ht : 0 ≤ t) (b : RealVectorL2) :
    heatSemigroup t ht (complexifyVectorL2 b) =
      complexifyVectorL2 (realHeatOperator t ht b) := by
  have hconj : conjLp complexVecConj
      (heatSemigroup t ht (complexifyVectorL2 b)) =
      heatSemigroup t ht (complexifyVectorL2 b) := by
    change conjLp complexVecConj
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
        (heatMultiplier t ht •
          Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 b))) = _
    rw [conjLp_fourierTransform_symm complexVecConj complexVecConj_smul,
      conjReflectLp_heatMultiplier_smul,
      conjReflectLp_fourier_complexifyVectorL2]
    rfl
  exact (complexifyVectorL2_realPartVectorL2_of_conj _ hconj).symm

/-- The Stokes output of a real physical tensor remains in the real
subspace of complex spatial L². -/
theorem stokesL2Operator_complexify_real
    {t : ℝ} (ht : 0 < t) (F : RealTensorL2) :
    stokesL2Operator ht (complexifyTensorL2 F) =
      complexifyVectorL2 (realStokesOperator ht F) := by
  have hconj : conjLp complexVecConj
      (stokesL2Operator ht (complexifyTensorL2 F)) =
      stokesL2Operator ht (complexifyTensorL2 F) := by
    change conjLp complexVecConj
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
        (stokesFourierMultiplier ht
          (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
            (complexifyTensorL2 F)))) = _
    rw [conjLp_fourierTransform_symm complexVecConj complexVecConj_smul,
      conjReflectLp_stokesFourierMultiplier,
      conjReflectLp_fourier_complexifyTensorL2]
    rfl
  exact (complexifyVectorL2_realPartVectorL2_of_conj _ hconj).symm

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalCompatibility
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorPhysicalRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorQuadratic

/-!
# The complete quadratic tensor represents the real mild tensor

A complete Sobolev velocity whose physical field is real has exactly the
original real regularized tensor as its physical nonlinear output.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The quadratic complete tensor agrees in physical L² with the
regularized mild tensor of the same real velocity. -/
theorem regularisedBesselTensorQuadratic_real_toLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (u : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b : RealVectorL2)
    (hu : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) u = complexifyVectorL2 b) :
    regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselTensorQuadratic ρ ε hε k u) =
      complexifyTensorL2 (regularizedMildTensor ρ ε hε b) := by
  unfold regularisedBesselTensorQuadratic
  rw [regularisedBesselTensorMap_physical, hu,
    regularisedTensorPhysicalMap_real_diagonal]

end CKN.Leray

end

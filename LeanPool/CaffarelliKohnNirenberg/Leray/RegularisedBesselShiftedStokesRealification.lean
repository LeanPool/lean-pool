/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselClampedTensorPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesRealification

/-!
# Realification of the shifted complete Sobolev mild integrand

If complete Sobolev and real physical velocity paths agree, their
shifted Stokes integrands represent the same real physical vector.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The physical complete Sobolev shifted integrand is exactly the
complexification of the real shifted mild integrand for the same path. -/
theorem regularisedBesselShiftedStokesIntegrand_real_toLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval T, RealVectorL2))
    (huv : ∀ q,
      regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u q) = complexifyVectorL2 (v q))
    (t τ : ℝ) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselShiftedStokesIntegrand k
        (regularisedBesselClampedTensorPath ρ ε hε k T hT u) t τ) =
    complexifyVectorL2
      (mildShiftedStokesIntegrand
        (regularizedMildClampedTensorTrajectory ρ ε hε T hT v) t τ) := by
  by_cases h : 0 < τ ∧ τ < t
  · rw [regularisedBesselShiftedStokesIntegrand_physical]
    simp only [dite_eq_left h]
    rw [regularisedBesselClampedTensorPath_real_toLp ρ ε hε k T hT u v huv,
      stokesL2Operator_complexify_real]
    simp only [mildShiftedStokesIntegrand, dite_eq_left h]
  · rw [regularisedBesselShiftedStokesIntegrand_physical]
    simp only [dite_eq_right h]
    simp [mildShiftedStokesIntegrand, h]

end CKN.Leray

end

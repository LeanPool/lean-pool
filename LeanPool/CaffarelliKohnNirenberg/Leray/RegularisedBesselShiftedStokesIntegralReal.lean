/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselRealPathNorm

/-!
# Physical realization of the shifted complete Sobolev integral

For corresponding complete Sobolev and real physical velocity paths,
their shifted Stokes integrals agree after physical realization and
complexification.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The physical L² realization of the complete shifted Stokes
integral is the complexification of the real shifted mild integral. -/
theorem regularisedBesselShiftedStokesIntegral_real_toLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval T, RealVectorL2))
    (huv : ∀ q,
      regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u q) = complexifyVectorL2 (v q))
    (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ q, ‖u q‖ ≤ R) (hv : ∀ q, ‖v q‖ ≤ R)
    (t : ℝ) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k
          (regularisedBesselClampedTensorPath ρ ε hε k T hT u) t τ) =
    complexifyVectorL2
      (∫ τ in (0 : ℝ)..T,
        mildShiftedStokesIntegrand
          (regularizedMildClampedTensorTrajectory ρ ε hε T hT v) t τ) := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  let F := regularisedBesselClampedTensorPath ρ ε hε k T hT u
  let G := regularizedMildClampedTensorTrajectory ρ ε hε T hT v
  let C := regularisedBesselTensorConstant ρ ε hε k * R ^ 2
  let D := regularizedMildMollifierConstant ρ ε * R ^ 2
  have hFcont : Continuous F :=
    regularisedBesselClampedTensorPath_continuous ρ ε hε k T hT u
  have hGcont : Continuous G :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT v
  have hFC : ∀ s, ‖F s‖ ≤ C :=
    regularisedBesselClampedTensorPath_norm_le ρ ε hε k T hT u R hR hu
  have hGC : ∀ s, ‖G s‖ ≤ D :=
    regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT v R hR hv
  have hC : 0 ≤ C :=
    mul_nonneg (regularisedBesselTensorMap_norm_le ρ ε hε k).1 (sq_nonneg R)
  have hD : 0 ≤ D :=
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg R)
  have hBint : IntervalIntegrable
      (regularisedBesselShiftedStokesIntegrand k F t) volume 0 T :=
    regularisedBesselShiftedStokesIntegrand_intervalIntegrable
      k F hFcont C hFC hC T t hT
  have hRint : IntervalIntegrable
      (mildShiftedStokesIntegrand G t) volume 0 T :=
    mildShiftedStokesIntegrand_intervalIntegrable G hGcont D hGC hD T t hT
  change E (∫ τ in (0 : ℝ)..T,
      regularisedBesselShiftedStokesIntegrand k F t τ) =
    complexifyVectorL2 (∫ τ in (0 : ℝ)..T,
      mildShiftedStokesIntegrand G t τ)
  calc
    E (∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k F t τ) =
      ∫ τ in (0 : ℝ)..T,
        E (regularisedBesselShiftedStokesIntegrand k F t τ) :=
          (E.intervalIntegral_comp_comm hBint).symm
    _ = ∫ τ in (0 : ℝ)..T,
        complexifyVectorL2 (mildShiftedStokesIntegrand G t τ) := by
          congr 1
          funext τ
          exact regularisedBesselShiftedStokesIntegrand_real_toLp
            ρ ε hε k T hT u v huv t τ
    _ = complexifyVectorL2 (∫ τ in (0 : ℝ)..T,
        mildShiftedStokesIntegrand G t τ) :=
          complexifyVectorL2.intervalIntegral_comp_comm hRint

end CKN.Leray

end

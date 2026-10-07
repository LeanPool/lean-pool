/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegralReal
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatPhysicalRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalMap

/-!
# Real physical form of the complete Sobolev mild map

The physical image of the complete local mild map is the
complexification of the real local mild right-hand side for the same
physical velocity path.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete H²ᵏ local map represents the real heat evolution
minus the real shifted Stokes integral of the same velocity path. -/
theorem regularisedBesselLocalMap_real_toLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval T, RealVectorL2))
    (huv : ∀ q,
      regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u q) = complexifyVectorL2 (v q))
    (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ q, ‖u q‖ ≤ R) (hv : ∀ q, ‖v q‖ ≤ R)
    (t : RegularizedMildTimeInterval T) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselLocalMap ρ ε hε k b T hT u t) =
    complexifyVectorL2
      (realHeatOperator t.1 t.2.1 b₀ -
        ∫ τ in (0 : ℝ)..T,
          mildShiftedStokesIntegrand
            (regularizedMildClampedTensorTrajectory ρ ε hε T hT v) t.1 τ) := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  rw [regularisedBesselLocalMap_apply]
  change E (regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
    ∫ τ in (0 : ℝ)..T,
      regularisedBesselShiftedStokesIntegrand k
        (regularisedBesselClampedTensorPath ρ ε hε k T hT u) t.1 τ) = _
  rw [map_sub,
    regularisedBesselHeat_real_toLp k t.1 t.2.1 b b₀ hb,
    regularisedBesselShiftedStokesIntegral_real_toLp
      ρ ε hε k T hT u v huv R hR hu hv t.1,
    map_sub]

end CKN.Leray

end

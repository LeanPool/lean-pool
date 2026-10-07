/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatRealization
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesRealification

/-!
# Real physical realization of complete Sobolev heat evolution

Complete Bessel heat evolution from real physical initial data agrees
with the real physical heat operator at every nonnegative time.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The physical field of complete H²ᵏ heat evolution of real data is
the complexification of real heat evolution of that same datum. -/
theorem regularisedBesselHeat_real_toLp
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselHeat ((2 * k : ℕ) : ℝ) t ht b) =
    complexifyVectorL2 (realHeatOperator t ht b₀) := by
  rw [regularisedBesselSobolevToL2CLM_apply,
    regularisedBesselHeat_realization,
    ← regularisedBesselSobolevToL2CLM_apply,
    hb, heatSemigroup_complexify_real]

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselRealPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalBall

/-!
# Closed real trajectory ball for the complete Sobolev fixed point

The complete Sobolev local mild map will be contracted on the
closed ball of trajectories with real physical L² realization.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Continuous complete H²ᵏ trajectories inside the local norm ball
whose physical L² fields are real. -/
@[expose]
def regularisedBesselLocalRealBall
    (k : ℕ) (T R : ℝ) :
    Set (C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :=
  {u | ‖u‖ ≤ R ∧
    ∀ t, regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) (u t) =
      complexifyVectorL2 (regularisedBesselRealPartPath k T u t)}

/-- The real complete Sobolev trajectory ball is closed. -/
theorem regularisedBesselLocalRealBall_isClosed
    (k : ℕ) (T R : ℝ) :
    IsClosed (regularisedBesselLocalRealBall k T R) := by
  change IsClosed
    ({u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) | ‖u‖ ≤ R} ∩
      {u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) |
        ∀ t, regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
            (by positivity) (u t) =
          complexifyVectorL2 (regularisedBesselRealPartPath k T u t)})
  exact (isClosed_Iic.preimage continuous_norm).inter
    (regularisedBesselRealPath_isClosed k T)

/-- The zero trajectory lies in every real local ball with
nonnegative radius. -/
theorem regularisedBesselLocalRealBall_zero
    (k : ℕ) (T R : ℝ) (hR : 0 ≤ R) :
    (0 : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) ∈
      regularisedBesselLocalRealBall k T R := by
  constructor
  · simpa using hR
  · intro t
    have hzero : regularisedBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
        (by positivity)
        (0 : BesselPotentialSpace L2Vec3 ComplexVec3
          ((2 * k : ℕ) : ℝ) 2) = 0 := by
      change (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity)) 0 = 0
      exact map_zero _
    simp [regularisedBesselRealPartPath, hzero]

end CKN.Leray

end

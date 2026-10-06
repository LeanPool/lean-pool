/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMollifiedInitialBesselLift
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalGlobalRepresentation

/-!
# Local Sobolev realization from mollified Leray data

The mollified initial field enters the complete H²ᵏ local mild
construction at every even order.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Every mollified Leray datum starts a complete H²ᵏ mild path that
represents the same global spatial L² trajectory on its lifespan. -/
theorem regUniformMollifiedInitial_local_bessel_representation
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (k : ℕ) :
    let b₀ := realVectorL2OfCoordinateFunction
      (regUniformMollifiedInitial ρ ε hε a)
      (regMollifiedInitial_isInJ ρ ε hε ha).1
    ∃ b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2,
      regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) b = complexifyVectorL2 b₀ ∧
      ∃ u : C(RegularizedMildTimeInterval
        (regularisedBesselLocalLifespan ρ ε hε k b),
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
        regularisedBesselLocalMap ρ ε hε k b
            (regularisedBesselLocalLifespan ρ ε hε k b)
            (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u = u ∧
          ‖u‖ ≤ regularisedBesselLocalRadius k b ∧
          ∀ t : RegularizedMildTimeInterval
            (regularisedBesselLocalLifespan ρ ε hε k b),
            regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
              (by positivity) (u t) =
              complexifyVectorL2
                (regularizedGlobalMildCurve ρ ε hε b₀
                  (regUniformMollifiedInitial_mildJData ρ ε hε ha) t.1) := by
  dsimp only
  let b₀ := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  obtain ⟨b, hb⟩ :=
    regUniformMollifiedInitial_bessel_even_lift ρ ε hε a ha k
  have hclass :
      (lerayHopfLimit_initialField_memLp
        (regUniformMollifiedInitial ρ ε hε a)
        (regMollifiedInitial_isInJ ρ ε hε ha).1).toLp
          (regUniformSpatialField (regUniformMollifiedInitial ρ ε hε a)) = b₀ := by
    rfl
  have hb₀ :
      regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) b = complexifyVectorL2 b₀ := by
    simpa only [regularisedBesselSobolevToL2CLM_apply, hclass] using hb
  refine ⟨b, hb₀, ?_⟩
  exact regularisedBesselLocalGlobalRepresentation
    ρ ε hε k b b₀ hb₀
      (regUniformMollifiedInitial_mildJData ρ ε hε ha)

end CKN.Leray

end

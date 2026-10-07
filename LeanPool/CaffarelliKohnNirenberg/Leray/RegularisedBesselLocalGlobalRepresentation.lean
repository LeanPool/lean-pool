/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalGlobalAgreement

/-!
# Local complete Sobolev representation of the global mild curve

For every real complete Sobolev initial state, the global regularized
mild solution is represented by a complete Sobolev mild curve on a
positive interval.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The global regularized mild curve has a real complete H²ᵏ
representation on the explicit local lifespan. -/
theorem regularisedBesselLocalGlobalRepresentation
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (hbJ : RegularizedMildJData b₀) :
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
              (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1) := by
  obtain ⟨u, hfix, hu⟩ := regularisedBesselLocalRealFixedPoint
    ρ ε hε k b b₀ hb
  exact ⟨u, hfix, hu.1, fun t =>
    regularisedBesselLocalRealFixedPoint_eq_global
      ρ ε hε k b b₀ hb hbJ u hfix hu t⟩

end CKN.Leray

end

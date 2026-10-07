/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalRealTrajectory
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationMildUniqueness

/-!
# Agreement of the complete local trajectory with the global mild curve

The real physical realization of the complete H²ᵏ fixed point is the
existing global regularized mild curve throughout its local lifespan.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The physical L² path of any real complete Sobolev local fixed point
agrees with the unique global regularized mild solution. -/
theorem regularisedBesselLocalRealFixedPoint_eq_global
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (hbJ : RegularizedMildJData b₀)
    (u : C(RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hfix : regularisedBesselLocalMap ρ ε hε k b
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u = u)
    (hu : u ∈ regularisedBesselLocalRealBall k
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalRadius k b))
    (t : RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b)) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) (u t) =
      complexifyVectorL2
        (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1) := by
  let T := regularisedBesselLocalLifespan ρ ε hε k b
  let v := regularisedBesselRealPartPath k T u
  have htraj : IsRegularizedMildTrajectory ρ ε hε b₀ T v :=
    regularisedBesselLocalRealFixedPoint_isTrajectory
      ρ ε hε k b b₀ hb u hfix hu
  have hglobal := regularizedMildIntervalPath_eq_global
    ρ ε hε b₀ hbJ T
      (regularisedBesselLocalLifespan_pos ρ ε hε k b).le v htraj t
  rw [← hglobal]
  exact hu.2 t

end CKN.Leray

end

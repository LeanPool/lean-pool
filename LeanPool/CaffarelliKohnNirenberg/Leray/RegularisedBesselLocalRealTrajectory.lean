/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalRealFixedPoint
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap

/-!
# Physical mild equation of the real complete Sobolev fixed point

The real physical trajectory of a complete H²ᵏ fixed point solves the
regularized L² mild equation on the same local interval.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A real complete Sobolev local fixed point is a physical L² mild
trajectory with the same initial datum. -/
theorem regularisedBesselLocalRealFixedPoint_isTrajectory
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (u : C(RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hfix : regularisedBesselLocalMap ρ ε hε k b
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u = u)
    (hu : u ∈ regularisedBesselLocalRealBall k
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalRadius k b)) :
    IsRegularizedMildTrajectory ρ ε hε b₀
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselRealPartPath k
        (regularisedBesselLocalLifespan ρ ε hε k b) u) := by
  let T := regularisedBesselLocalLifespan ρ ε hε k b
  let hT : 0 ≤ T := (regularisedBesselLocalLifespan_pos ρ ε hε k b).le
  let R := regularisedBesselLocalRadius k b
  let v := regularisedBesselRealPartPath k T u
  have hR : 0 ≤ R := by dsimp [R, regularisedBesselLocalRadius]; positivity
  have huPoint : ∀ q, ‖u q‖ ≤ R := (u.norm_le hR).1 hu.1
  have hvPoint : ∀ q, ‖v q‖ ≤ R := by
    intro q
    exact le_trans (v.norm_coe_le_norm q |>.trans
      (regularisedBesselRealPartPath_norm_le k T u)) hu.1
  intro t
  have hphysical := regularisedBesselLocalMap_real_toLp
    ρ ε hε k T hT b b₀ hb u v hu.2 R hR huPoint hvPoint t
  have hfixAt := congrArg (fun w : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) => w t) hfix
  have heq : complexifyVectorL2 (v t) =
      complexifyVectorL2
        (realHeatOperator t.1 t.2.1 b₀ -
          ∫ τ in (0 : ℝ)..T,
            mildShiftedStokesIntegrand
              (regularizedMildClampedTensorTrajectory ρ ε hε T hT v) t.1 τ) := by
    calc
      complexifyVectorL2 (v t) =
          regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
            (by positivity) (u t) := (hu.2 t).symm
      _ = regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
            (by positivity)
              (regularisedBesselLocalMap ρ ε hε k b T hT u t) := by
        rw [hfixAt]
      _ = _ := hphysical
  have hshift : v t = regularizedMildLocalMap ρ ε hε b₀ T hT v t := by
    have hreal := congrArg realPartVectorL2 heq
    simpa only [realPartVectorL2_complexifyVectorL2,
      regularizedMildLocalMap_eq_shifted] using hreal
  exact hshift.trans
    (regularizedMildLocalMap_eq_rightHandSide ρ ε hε b₀ T hT v t)

end CKN.Leray

end

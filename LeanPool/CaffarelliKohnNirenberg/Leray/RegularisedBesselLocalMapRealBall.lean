/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalMapPhysicalReal
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalRealBall
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselRealPathNorm
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealFourierCutoff

/-!
# Invariance of the real complete Sobolev trajectory ball

The complete mild map preserves real physical realizations when its initial
datum is real in physical L².
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The local complete Sobolev mild map preserves the closed real ball. -/
theorem regularisedBesselLocalMap_realBall
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (u : C(RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hu : u ∈ regularisedBesselLocalRealBall k
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalRadius k b)) :
    regularisedBesselLocalMap ρ ε hε k b
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u ∈
        regularisedBesselLocalRealBall k
          (regularisedBesselLocalLifespan ρ ε hε k b)
          (regularisedBesselLocalRadius k b) := by
  let T := regularisedBesselLocalLifespan ρ ε hε k b
  let R := regularisedBesselLocalRadius k b
  let hT : 0 ≤ T := (regularisedBesselLocalLifespan_pos ρ ε hε k b).le
  have hR : 0 ≤ R := by dsimp [R, regularisedBesselLocalRadius]; positivity
  obtain ⟨huNorm, huReal⟩ := hu
  constructor
  · exact regularisedBesselLocalMap_ball ρ ε hε k b u huNorm
  · intro t
    let v := regularisedBesselRealPartPath k T u
    have huPoint : ∀ q, ‖u q‖ ≤ R := (u.norm_le hR).1 huNorm
    have hvPoint : ∀ q, ‖v q‖ ≤ R := by
      intro q
      exact le_trans (v.norm_coe_le_norm q |>.trans
        (regularisedBesselRealPartPath_norm_le k T u)) huNorm
    have hphysical := regularisedBesselLocalMap_real_toLp
      ρ ε hε k T hT b b₀ hb u v huReal R hR huPoint hvPoint t
    change regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity)
        (regularisedBesselLocalMap ρ ε hε k b T hT u t) =
      complexifyVectorL2
        (realPartVectorL2
          (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
            (by positivity)
              (regularisedBesselLocalMap ρ ε hε k b T hT u t)))
    rw [hphysical, realPartVectorL2_complexifyVectorL2]

end CKN.Leray

end

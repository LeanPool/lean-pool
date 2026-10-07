/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalMapRealBall
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalContraction
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Real local fixed point in the complete Sobolev space

The complete H²ᵏ mild map has a fixed point whose physical L² trajectory
is real, on the same positive interval as its complex fixed point.
-/

public section

open MeasureTheory FourierTransform Set
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A real physical complete H²ᵏ mild solution exists on the explicit
positive local lifespan. -/
theorem regularisedBesselLocalRealFixedPoint
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀) :
    ∃ u : C(RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      regularisedBesselLocalMap ρ ε hε k b
          (regularisedBesselLocalLifespan ρ ε hε k b)
          (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u = u ∧
        u ∈ regularisedBesselLocalRealBall k
          (regularisedBesselLocalLifespan ρ ε hε k b)
          (regularisedBesselLocalRadius k b) := by
  let T := regularisedBesselLocalLifespan ρ ε hε k b
  let hT : 0 ≤ T := (regularisedBesselLocalLifespan_pos ρ ε hε k b).le
  let R := regularisedBesselLocalRadius k b
  let S : Set (C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :=
    regularisedBesselLocalRealBall k T R
  let f : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) →
      C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
    regularisedBesselLocalMap ρ ε hε k b T hT
  have hmap : MapsTo f S S := by
    intro u hu
    exact regularisedBesselLocalMap_realBall ρ ε hε k b b₀ hb u hu
  have hclosed : IsClosed S := regularisedBesselLocalRealBall_isClosed k T R
  have hzero : (0 : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) ∈ S := by
    have hR : 0 ≤ R := by
      dsimp [R, regularisedBesselLocalRadius]
      positivity
    exact regularisedBesselLocalRealBall_zero k T R hR
  let κ : NNReal := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hκ : κ < 1 := by
    exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)
  have hLipschitz (u v : S) :
      dist (f u) (f v) ≤ κ * dist u v := by
    change dist (f u.1) (f v.1) ≤ κ * dist u.1 v.1
    rw [dist_eq_norm, dist_eq_norm]
    have hlip := regularisedBesselLocalMap_contraction
      ρ ε hε k b u.1 v.1 u.2.1 v.2.1
    change ‖f u.1 - f v.1‖ ≤ (1 / 2 : ℝ) * ‖u.1 - v.1‖ at hlip
    exact hlip
  have hlip : LipschitzWith κ (hmap.restrict f S S) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      change dist (f u) (f v) ≤ κ * dist u v
      exact hLipschitz u v
  have hcontract : ContractingWith κ (hmap.restrict f S S) := ⟨hκ, hlip⟩
  obtain ⟨u, hu, hfixed, -, -⟩ := ContractingWith.exists_fixedPoint'
    hclosed.isComplete hmap hcontract hzero (by simp [edist_dist])
  exact ⟨u, hfixed.eq, hu⟩

end CKN.Leray

end

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearContraction
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Uniform-time linear complete Sobolev fixed point

A prescribed bounded physical L² velocity gives a unique complete
Sobolev solution of its linearized mild equation on a time interval
independent of the initial complete Sobolev norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The linearized complete H²ᵏ mild map has a fixed point on the
uniform energy time step, without a complete Sobolev norm ball. -/
theorem regularisedBesselLinearLocalFixedPoint
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (B : ℝ) (hB : 0 ≤ B)
    (g : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B), ComplexVectorL2))
    (hg : ∀ q, ‖g q‖ ≤ B) :
    ∃ v : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      regularisedBesselLinearLocalMap ρ ε hε k b
        (regularisedBesselUniformEnergyStep ρ ε hε k B)
        (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
        g B hB hg v = v := by
  let T := regularisedBesselUniformEnergyStep ρ ε hε k B
  let hT : 0 ≤ T := (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
  let f : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) →
      C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
    regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg
  let κ : NNReal := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hκ : κ < 1 := by
    exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)
  have hLipschitz (v w : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
      dist (f v) (f w) ≤ κ * dist v w := by
    rw [dist_eq_norm, dist_eq_norm]
    have h := regularisedBesselLinearLocalMap_contraction
      ρ ε hε k b B hB g hg v w
    change ‖f v - f w‖ ≤ (1 / 2 : ℝ) * ‖v - w‖ at h
    exact h
  have hlip : LipschitzWith κ f :=
    LipschitzWith.of_dist_le_mul hLipschitz
  have hcontract : ContractingWith κ f := ⟨hκ, hlip⟩
  obtain ⟨v, hv, -, -⟩ := hcontract.exists_fixedPoint 0
    (by simp [edist_dist])
  exact ⟨v, hv.eq⟩

/-- The linearized complete Sobolev mild equation has at most one
continuous solution on the uniform energy time step. -/
theorem regularisedBesselLinearLocalFixedPoint_unique
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (B : ℝ) (hB : 0 ≤ B)
    (g : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B), ComplexVectorL2))
    (hg : ∀ q, ‖g q‖ ≤ B)
    (v w : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hv : regularisedBesselLinearLocalMap ρ ε hε k b
      (regularisedBesselUniformEnergyStep ρ ε hε k B)
      (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
      g B hB hg v = v)
    (hw : regularisedBesselLinearLocalMap ρ ε hε k b
      (regularisedBesselUniformEnergyStep ρ ε hε k B)
      (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
      g B hB hg w = w) : v = w := by
  have hcontract := regularisedBesselLinearLocalMap_contraction
    ρ ε hε k b B hB g hg v w
  rw [hv, hw] at hcontract
  have hzero : ‖v - w‖ = 0 := by
    linarith only [hcontract, norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end CKN.Leray

end

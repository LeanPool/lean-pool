/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalMap

/-!
# Invariance of the complete Sobolev mild ball

The complete H²ᵏ mild map sends the explicit closed trajectory ball
into itself on its positive local lifespan.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The chosen complete H²ᵏ trajectory ball is invariant under the
local regularized mild map. -/
theorem regularisedBesselLocalMap_ball
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (u : C(RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hu : ‖u‖ ≤ regularisedBesselLocalRadius k b) :
    ‖regularisedBesselLocalMap ρ ε hε k b
      (regularisedBesselLocalLifespan ρ ε hε k b)
      (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u‖ ≤
      regularisedBesselLocalRadius k b := by
  let T := regularisedBesselLocalLifespan ρ ε hε k b
  let R := regularisedBesselLocalRadius k b
  have hT : 0 ≤ T := (regularisedBesselLocalLifespan_pos ρ ε hε k b).le
  have hR : 0 ≤ R := by dsimp [R, regularisedBesselLocalRadius]; positivity
  have huPoint : ∀ t, ‖u t‖ ≤ R := (u.norm_le hR).1 hu
  let F := regularisedBesselClampedTensorPath ρ ε hε k T hT u
  let C := regularisedBesselTensorConstant ρ ε hε k * R ^ 2
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    intro s
    exact regularisedBesselClampedTensorPath_norm_le
      ρ ε hε k T hT u R hR huPoint s
  have hC : 0 ≤ C :=
    mul_nonneg (regularisedBesselTensorMap_norm_le ρ ε hε k).1
      (sq_nonneg R)
  apply (regularisedBesselLocalMap ρ ε hε k b T hT u).norm_le hR |>.2
  intro t
  rw [regularisedBesselLocalMap_apply]
  have hInt := regularisedBesselShiftedStokesIntegral_norm_le
    k F C hFC hC T t.1 hT
  have hHeat := regularisedBesselHeat_norm_le
    ((2 * k : ℕ) : ℝ) t.1 t.2.1 b
  calc
    ‖regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k F t.1 τ‖ ≤
      ‖regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b‖ +
        ‖∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k F t.1 τ‖ := norm_sub_le _ _
    _ ≤ ‖b‖ + 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T :=
      add_le_add hHeat hInt
    _ = ‖b‖ + 2 * (regularisedBesselTensorConstant ρ ε hε k /
          Real.sqrt (2 * Real.exp 1)) * R ^ 2 * Real.sqrt T := by
      dsimp [C]
      ring
    _ ≤ R := regularisedBesselLocalLifespan_ball_bound ρ ε hε k b

end CKN.Leray

end

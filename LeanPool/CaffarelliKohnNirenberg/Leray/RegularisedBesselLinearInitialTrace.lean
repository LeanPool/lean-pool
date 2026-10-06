/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearLocalMap

/-!
# Initial value of the linear complete Sobolev mild map

The prescribed physical coefficient does not alter the initial state
of the complete Sobolev mild equation.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Every image of the linear complete Sobolev mild map takes its
prescribed complete Sobolev initial datum at time zero. -/
theorem regularisedBesselLinearLocalMap_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg v
      ⟨0, le_refl _, hT⟩ = b := by
  rw [regularisedBesselLinearLocalMap_apply,
    regularisedBesselHeat_zero]
  have hzero : (fun τ : ℝ =>
      regularisedBesselShiftedStokesIntegrand k
        (regularisedBesselLinearTensorPath ρ ε hε k T hT g v) 0 τ) = 0 := by
    funext τ
    have h : ¬(0 < τ ∧ τ < 0) := by
      intro hp
      linarith only [hp.1, hp.2]
    simp only [regularisedBesselShiftedStokesIntegrand, dite_eq_right h,
      Pi.zero_apply]
  rw [hzero]
  simp [intervalIntegral]

end CKN.Leray

end

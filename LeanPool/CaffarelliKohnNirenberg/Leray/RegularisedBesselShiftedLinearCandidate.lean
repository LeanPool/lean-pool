/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearEnergyBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalComplexShiftPath

/-!
# Uniform complete Sobolev candidate from a later time

At every nonnegative start time, the global mild curve supplies a
bounded physical coefficient for a complete Sobolev mild equation
on the same uniform time step.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- From any nonnegative start time and complete Sobolev initial state,
the equation linearized around the shifted global mild curve has an
H²ᵏ solution on a time step fixed by the initial physical L² bound. -/
theorem regularisedBesselShiftedLinearCandidate
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a : ℝ) (ha : 0 ≤ a) :
    let T := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
    let g := regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T
    ∃ v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      regularisedBesselLinearLocalMap ρ ε hε k b T
        (regularisedBesselUniformEnergyStep_pos ρ ε hε k ‖b₀‖
          (norm_nonneg b₀)).le
        g ‖b₀‖ (norm_nonneg b₀)
        (regularisedGlobalComplexShiftPath_norm_le_initial
          ρ ε hε b₀ hbJ a T ha) v = v ∧
      ‖v‖ ≤ 2 * ‖b‖ := by
  dsimp only
  let T := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
  let g := regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T
  let hg : ∀ q, ‖g q‖ ≤ ‖b₀‖ :=
    regularisedGlobalComplexShiftPath_norm_le_initial ρ ε hε b₀ hbJ a T ha
  obtain ⟨v, hv⟩ := regularisedBesselLinearLocalFixedPoint
    ρ ε hε k b ‖b₀‖ (norm_nonneg b₀) g hg
  exact ⟨v, hv,
    regularisedBesselLinearLocalFixedPoint_norm_le_twice
      ρ ε hε k b ‖b₀‖ (norm_nonneg b₀) g hg v hv⟩

end CKN.Leray

end

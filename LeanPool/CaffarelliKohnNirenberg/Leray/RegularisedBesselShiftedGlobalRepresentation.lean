/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedLinearCandidate
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedPhysicalAgreement
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearInitialTrace

/-!
# Uniform Sobolev realization after a global restart

Every complete Sobolev state of the global mild curve extends as a complete
Sobolev path over a time step fixed by the initial physical energy bound.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Starting from any nonnegative time where the global mild curve has an
H²ᵏ realization, the same curve has an H²ᵏ path over the uniform step. -/
theorem regularisedBesselShiftedGlobalRepresentation
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a : ℝ) (ha : 0 ≤ a)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b =
        complexifyVectorL2 (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a)) :
    let δ := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
    ∃ v : C(RegularizedMildTimeInterval δ,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      v ⟨0, le_refl _,
        (regularisedBesselUniformEnergyStep_pos ρ ε hε k ‖b₀‖
          (norm_nonneg b₀)).le⟩ = b ∧
      ‖v‖ ≤ 2 * ‖b‖ ∧
      ∀ t : RegularizedMildTimeInterval δ,
        regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
          (by positivity) (v t) =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ (a + t.1)) := by
  dsimp only
  let δ := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
  let hδ : 0 ≤ δ :=
    (regularisedBesselUniformEnergyStep_pos ρ ε hε k ‖b₀‖
      (norm_nonneg b₀)).le
  obtain ⟨v, hfix, hnorm⟩ :=
    regularisedBesselShiftedLinearCandidate ρ ε hε k b b₀ hbJ a ha
  refine ⟨v, ?_, hnorm, ?_⟩
  · have hfix0 := congrArg
      (fun z : C(RegularizedMildTimeInterval δ,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) =>
        z ⟨0, le_refl _, hδ⟩) hfix
    rw [regularisedBesselLinearLocalMap_zero] at hfix0
    exact hfix0.symm
  · intro t
    exact regularisedBesselLinearFixedPoint_physical_eq_global_shift
      ρ ε hε k b₀ hbJ a δ ha hδ b hb v hfix t

end CKN.Leray

end

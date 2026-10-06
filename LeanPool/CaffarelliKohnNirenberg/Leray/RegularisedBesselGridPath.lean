/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedGlobalRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselAppendPath

/-!
# Complete Sobolev paths on uniform continuation grids

The physical L² energy bound fixes one positive continuation step.
Successive Sobolev restarts then concatenate into a path through any
finite number of steps.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A complete Sobolev realization at time zero extends continuously
through any finite number of uniform continuation steps. -/
theorem regularisedBesselGlobalGridPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b = complexifyVectorL2 b₀)
    (n : ℕ) :
    let δ := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
    ∃ v : C(RegularizedMildTimeInterval ((n : ℝ) * δ),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval ((n : ℝ) * δ),
        regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
          (by positivity) (v t) =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1) := by
  dsimp only
  let δ := regularisedBesselUniformEnergyStep ρ ε hε k ‖b₀‖
  have hδ : 0 ≤ δ :=
    (regularisedBesselUniformEnergyStep_pos ρ ε hε k ‖b₀‖
      (norm_nonneg b₀)).le
  change ∃ v : C(RegularizedMildTimeInterval ((n : ℝ) * δ),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2),
      ∀ t : RegularizedMildTimeInterval ((n : ℝ) * δ),
        regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
          (by positivity) (v t) =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1)
  induction n with
  | zero =>
      have hzero : ((0 : ℕ) : ℝ) * δ = 0 := by norm_num
      rw [hzero]
      let v : C(RegularizedMildTimeInterval 0,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
        ⟨fun _ => b, continuous_const⟩
      refine ⟨v, ?_⟩
      intro t
      have ht0 : t.1 = 0 := by
        have htle : t.1 ≤ 0 := t.2.2
        exact le_antisymm htle t.2.1
      change regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
        (by positivity) b =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1)
      rw [ht0, regularizedGlobalMildCurve_zero]
      exact hb
  | succ n ih =>
      let a : ℝ := (n : ℝ) * δ
      have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg n) hδ
      obtain ⟨v, hv⟩ := ih
      let bₙ : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2 :=
        v ⟨a, ha, le_refl _⟩
      have hbₙ : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
          (by positivity) bₙ =
          complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a) :=
        hv ⟨a, ha, le_refl _⟩
      obtain ⟨w, hw0, -, hw⟩ :=
        regularisedBesselShiftedGlobalRepresentation
          ρ ε hε k b₀ hbJ a ha bₙ hbₙ
      have hmatch : v ⟨a, ha, le_refl _⟩ =
          w ⟨0, le_refl _, hδ⟩ := hw0.symm
      let z := regularisedBesselAppendPath k a δ ha hδ v w hmatch
      have hz (t : RegularizedMildTimeInterval (a + δ)) :
          regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
            (by positivity) (z t) =
            complexifyVectorL2
              (regularizedGlobalMildCurve ρ ε hε b₀ hbJ t.1) := by
        by_cases ht : t.1 ≤ a
        · rw [regularisedBesselAppendPath_left k a δ ha hδ v w hmatch t ht]
          exact hv ⟨t.1, t.2.1, ht⟩
        · have ht' : a ≤ t.1 := le_of_not_ge ht
          rw [regularisedBesselAppendPath_right k a δ ha hδ v w hmatch t ht']
          have hwt := hw ⟨t.1 - a, sub_nonneg.mpr ht',
            by linarith only [t.2.2]⟩
          convert hwt using 1
          congr 1
          ring_nf
      have hnext : (((n + 1 : ℕ) : ℝ) * δ) = a + δ := by
        dsimp [a]
        push_cast
        ring_nf
      rw [hnext]
      exact ⟨z, hz⟩

end CKN.Leray

end

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalDominatedDensity
public import LeanPool.VacuumBellSeparation.Bell.NormalStateDominatedNormalization
public import LeanPool.VacuumBellSeparation.Bell.RepresentedVectorBellMaximality
public import LeanPool.VacuumBellSeparation.Bell.SignedBellCorrelation

/-!
# Faithful normal maximality forces all normal states to be maximal

This is the faithful-reference implication of SW88 Theorem 2.1 for the
original commuting A and B and their actual joint VNA. It uses arbitrary
normal states, not only represented vectors. The source's separability
assumption is unnecessary for this direction once a faithful normal reference
is supplied. No converse existence of such a reference or geometry is asserted.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normalized dominated states are dense for an actual faithful normal state.
The topology is the inherited full continuous-dual norm on NormalStateSpace. -/
theorem normalState_mem_closure_dominated_of_faithful
    (M : VonNeumannAlgebra H) (ω : NormalStateSpace M)
    (hf : ∀ a : M.toStarSubalgebra, ω.1 (star a * a) = 0 → a = 0)
    (ψ : NormalStateSpace M) :
    ψ ∈ closure {ρ : NormalStateSpace M |
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ X : M.toStarSubalgebra,
        0 ≤ X → t • ρ.1 X ≤ ω.1 X} := by
  obtain ⟨φ, _, hφ⟩ := ω.2.1
  have hnφ : IsNormalFunctional M φ := by
    simpa only [IsNormalFunctional, hφ] using ω.2.2
  have hfφ : ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0 := by
    intro a ha
    exact hf a (by simpa only [hφ] using ha)
  obtain ⟨p, _, hp⟩ := ψ.2.1
  have hnp : IsNormalFunctional M p := by
    simpa only [IsNormalFunctional, hp] using ψ.2.2
  have hep : (PositiveContinuousLinearMap.ofClass p).toContinuousLinearMap = ψ.1 :=
    ContinuousLinearMap.ext hp
  have hc := normalFunctional_mem_closure_dominated_of_faithful_normal M φ p hnφ hfφ hnp
  rw [hep] at hc
  have h := normalState_mem_closure_dominated_of_positive_closure M φ hnφ ψ hc
  simpa only [hφ] using h

namespace SW88

/-- Literal all-normal-state conclusion on original A and B. The reference's
faithfulness is its actual vanishing condition on every positive square. -/
theorem jointBellCorrelation_all_normal_maximal_of_faithful
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (ω : NormalStateSpace (jointAlgebra A B))
    (hf : ∀ a : (jointAlgebra A B).toStarSubalgebra,
      ω.1 (star a * a) = 0 → a = 0)
    (hmax : jointBellCorrelation A B ω.1 = Real.sqrt 2)
    (ψ : NormalStateSpace (jointAlgebra A B)) :
    jointBellCorrelation A B ψ.1 = Real.sqrt 2 :=
  jointBellCorrelation_maximal_of_mem_closure_dominated A B hcomm ω hmax
    (normalState_mem_closure_dominated_of_faithful (jointAlgebra A B) ω hf ψ)

/-- The same implication with the source's signed-real CHSH supremum. The
proved signed/absolute identity preserves the literal half normalization. -/
theorem jointSignedBellCorrelation_all_normal_maximal_of_faithful
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (ω : NormalStateSpace (jointAlgebra A B))
    (hf : ∀ a : (jointAlgebra A B).toStarSubalgebra,
      ω.1 (star a * a) = 0 → a = 0)
    (hmax : jointSignedBellCorrelation A B ω.1 = Real.sqrt 2)
    (ψ : NormalStateSpace (jointAlgebra A B)) :
    jointSignedBellCorrelation A B ψ.1 = Real.sqrt 2 := by
  rw [jointSignedBellCorrelation_eq A B hcomm ⟨ψ.1, ψ.2.1⟩]
  apply jointBellCorrelation_all_normal_maximal_of_faithful A B hcomm ω hf
  rwa [jointSignedBellCorrelation_eq A B hcomm ⟨ω.1, ω.2.1⟩] at hmax

end SW88
end VacuumBellSeparation.Bipartite

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CommutantVectorStateDensity
public import LeanPool.VacuumBellSeparation.Bell.DominatedNormalStateResidual

/-!
# Maximal Bell correlation for every represented unit-vector state

This is the original-H vector-state part of the SW88 Theorem 2.1 argument.
The reference unit vector separates the actual jointly generated algebra.
Commutant-orbit approximation supplies genuinely dominated normal states;
convex maximality inheritance and full-dual norm continuity give the result.
No representation or density theorem for arbitrary normal states is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.SW88

open HC00
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Maximality extends to the actual norm closure of dominated normal states.
Domination is an inequality on every positive element of the original joint algebra. -/
theorem jointBellCorrelation_maximal_of_mem_closure_dominated
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (ω : NormalStateSpace (jointAlgebra A B))
    (hmax : jointBellCorrelation A B ω.1 = Real.sqrt 2)
    {φ : NormalStateSpace (jointAlgebra A B)}
    (hφ : φ ∈ closure {ψ : NormalStateSpace (jointAlgebra A B) |
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ T : (jointAlgebra A B).toStarSubalgebra,
        0 ≤ T → t • ψ.1 T ≤ ω.1 T}) :
    jointBellCorrelation A B φ.1 = Real.sqrt 2 := by
  apply jointBellCorrelation_eq_of_mem_closure_normal A B ?_ hφ
  rintro ψ ⟨t, ht, ht1, hdom⟩
  exact jointBellCorrelation_maximal_normal_of_dominated A B hcomm ω ψ hmax ht ht1 hdom

/-- A maximal separating unit reference vector forces every original-H unit
vector state to be maximal. This conclusion is not all-normal-state maximality. -/
theorem jointBellCorrelation_vectorState_maximal_of_separating
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B)
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hsep : IsSeparatingForAlgebra (jointAlgebra A B) Ω)
    (hmax : jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) Ω) = Real.sqrt 2)
    (χ : H) (hχ : ‖χ‖ = 1) :
    jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) χ) = Real.sqrt 2 := by
  have hclosure := vectorNormalState_mem_closure_dominated
    (jointAlgebra A B) Ω hΩ hsep χ hχ
  exact jointBellCorrelation_maximal_of_mem_closure_dominated A B hcomm
    (vectorNormalState (jointAlgebra A B) Ω hΩ) hmax hclosure

end VacuumBellSeparation.Bipartite.SW88

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalStateExistence
public import LeanPool.VacuumBellSeparation.Bell.FaithfulNormalBellMaximality

/-!
# SW88 Theorem 2.1 on the original joint von Neumann algebra

The signed-real Bell quantity is the source's supremum over selfadjoint
contractions, with the literal factor one half. All normal states means the
existing positive, unital, all-directed order-normal full-dual carrier.
SeparableSpace and Nontrivial refer to the original full Hilbert space.
No geometry, named predual identification, or maximizing quartet is asserted.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 TopologicalSpace
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Package the constructed faithful state in the exact normal-state carrier. -/
theorem exists_faithful_mem_normalStateSpace [SeparableSpace H] [Nontrivial H]
    (M : VonNeumannAlgebra H) :
    ∃ ω : NormalStateSpace M,
      ∀ a : M.toStarSubalgebra, ω.1 (star a * a) = 0 → a = 0 := by
  obtain ⟨φ, hunit, hn, hf⟩ := exists_faithful_normal_state_of_separable M
  let f : StrongDual ℂ M.toStarSubalgebra :=
    (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap
  have hs : IsNormalStateFunctional M f := ⟨⟨φ, hunit, fun _ => rfl⟩, hn⟩
  exact ⟨⟨f, hs⟩, hf⟩

namespace SW88

/-- The abstract SW88 Theorem 2.1 equivalence for the signed CHSH supremum.
Faithfulness is its literal vanishing condition on every positive square. -/
theorem jointSignedBellCorrelation_all_normal_maximal_iff_exists_faithful
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B) :
    (∀ ψ : NormalStateSpace (jointAlgebra A B),
      jointSignedBellCorrelation A B ψ.1 = Real.sqrt 2) ↔
    ∃ ω : NormalStateSpace (jointAlgebra A B),
      (∀ a : (jointAlgebra A B).toStarSubalgebra,
        ω.1 (star a * a) = 0 → a = 0) ∧
      jointSignedBellCorrelation A B ω.1 = Real.sqrt 2 := by
  constructor
  · intro h
    obtain ⟨ω, hf⟩ := exists_faithful_mem_normalStateSpace (jointAlgebra A B)
    exact ⟨ω, hf, h ω⟩
  · rintro ⟨ω, hf, hmax⟩ ψ
    exact jointSignedBellCorrelation_all_normal_maximal_of_faithful A B hcomm ω hf hmax ψ

/-- The equivalent absolute-value convention already used by the HC00 API. -/
theorem jointBellCorrelation_all_normal_maximal_iff_exists_faithful
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B) :
    (∀ ψ : NormalStateSpace (jointAlgebra A B),
      jointBellCorrelation A B ψ.1 = Real.sqrt 2) ↔
    ∃ ω : NormalStateSpace (jointAlgebra A B),
      (∀ a : (jointAlgebra A B).toStarSubalgebra,
        ω.1 (star a * a) = 0 → a = 0) ∧
      jointBellCorrelation A B ω.1 = Real.sqrt 2 := by
  constructor
  · intro h
    obtain ⟨ω, hf⟩ := exists_faithful_mem_normalStateSpace (jointAlgebra A B)
    exact ⟨ω, hf, h ω⟩
  · rintro ⟨ω, hf, hmax⟩ ψ
    exact jointBellCorrelation_all_normal_maximal_of_faithful A B hcomm ω hf hmax ψ

end SW88
end VacuumBellSeparation.Bipartite

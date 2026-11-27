/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CoefficientPredualDuality
public import LeanPool.VacuumBellSeparation.Bell.CoefficientWeakTopology
public import LeanPool.VacuumBellSeparation.Bell.SW88MaximalCorrelationEquivalence

/-!
States in the concrete coefficient Banach predual and the full original
order-normal state space are the same functionals, with exactly the same
norm metric. No normality field is required in the predual-state definition:
it is derived from membership in the actual coefficient space.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 TopologicalSpace
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance coefficientState_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Coefficient state space with underlying type `{f : coefficientPredual M // IsStateFunctional M
f.1}`. -/
abbrev CoefficientStateSpace (M : VonNeumannAlgebra H) :=
  {f : coefficientPredual M // IsStateFunctional M f.1}

theorem normalState_mem_coefficientPredual (M : VonNeumannAlgebra H)
    (ω : NormalStateSpace M) : ω.1 ∈ coefficientPredual M := by
  obtain ⟨φ, _, hφ⟩ := ω.2.1
  have hn : IsNormalFunctional M φ := by
    simpa only [IsNormalFunctional, hφ] using ω.2.2
  have he : (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap = ω.1 :=
    ContinuousLinearMap.ext hφ
  rw [← he]
  exact (isNormalFunctional_iff_mem_coefficientPredual M φ).mp hn

theorem coefficientState_isNormal (M : VonNeumannAlgebra H)
    (ω : CoefficientStateSpace M) : IsNormalFunctional M ω.1.1 := by
  obtain ⟨φ, _, hφ⟩ := ω.2
  have he : (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap = ω.1.1 :=
    ContinuousLinearMap.ext hφ
  have hm : (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap ∈
      coefficientPredual M := he.symm ▸ ω.1.2
  have hn := (isNormalFunctional_iff_mem_coefficientPredual M φ).mpr hm
  simpa only [IsNormalFunctional, hφ] using hn

/-- Identify normal states with positive normalized elements of the coefficient predual. -/
def coefficientNormalStateEquiv (M : VonNeumannAlgebra H) :
    CoefficientStateSpace M ≃ NormalStateSpace M where
  toFun ω := ⟨ω.1.1, ω.2, coefficientState_isNormal M ω⟩
  invFun ω := ⟨⟨ω.1, normalState_mem_coefficientPredual M ω⟩, ω.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coefficientNormalStateEquiv_apply (M : VonNeumannAlgebra H)
    (ω : CoefficientStateSpace M) : (coefficientNormalStateEquiv M ω).1 = ω.1.1 := rfl

@[simp] theorem coefficientNormalStateEquiv_symm_apply (M : VonNeumannAlgebra H)
    (ω : NormalStateSpace M) : ((coefficientNormalStateEquiv M).symm ω).1.1 = ω.1 := rfl

theorem coefficientNormalStateEquiv_isometry (M : VonNeumannAlgebra H) :
    Isometry (coefficientNormalStateEquiv M) :=
  isometry_iff_dist_eq.mpr (fun _ _ => rfl)

/-- SW88's statement on states in the explicit actual Banach predual.
The operator algebra is unchanged and its dual identification is proved
separately by coefficientPredualDualEquiv, not a hypothesis here. -/
theorem SW88.jointSignedBellCorrelation_all_predual_maximal_iff_exists_faithful
    [SeparableSpace H] [Nontrivial H]
    (A B : VonNeumannAlgebra H) (hcomm : Commuting A B) :
    (∀ ψ : CoefficientStateSpace (jointAlgebra A B),
      jointSignedBellCorrelation A B ψ.1.1 = Real.sqrt 2) ↔
    ∃ ω : CoefficientStateSpace (jointAlgebra A B),
      (∀ a : (jointAlgebra A B).toStarSubalgebra,
        ω.1.1 (star a * a) = 0 → a = 0) ∧
      jointSignedBellCorrelation A B ω.1.1 = Real.sqrt 2 := by
  let e := coefficientNormalStateEquiv (jointAlgebra A B)
  constructor
  · intro h
    have hn (ψ : NormalStateSpace (jointAlgebra A B)) :
        jointSignedBellCorrelation A B ψ.1 = Real.sqrt 2 := h (e.symm ψ)
    obtain ⟨ω, hf, hm⟩ :=
      (SW88.jointSignedBellCorrelation_all_normal_maximal_iff_exists_faithful A B hcomm).mp hn
    exact ⟨e.symm ω, hf, hm⟩
  · rintro ⟨ω, hf, hm⟩ ψ
    exact (SW88.jointSignedBellCorrelation_all_normal_maximal_iff_exists_faithful A B hcomm).mpr
      ⟨e ω, hf, hm⟩ (e ψ)

end VacuumBellSeparation.Bipartite

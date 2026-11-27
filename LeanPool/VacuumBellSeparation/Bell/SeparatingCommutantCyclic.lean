/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BicommutantOrbit
public import LeanPool.VacuumBellSeparation.Bell.BipartiteNormalStateDefs

/-! Separating and commutant-cyclic vectors in the original concrete Hilbert
space. This supplies no GNS construction for an arbitrary normal state. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Predicate for separating for algebra. -/
def IsSeparatingForAlgebra (M : VonNeumannAlgebra H) (Ω : H) : Prop :=
  ∀ T : H →L[ℂ] H, T ∈ M → T Ω = 0 → T = 0

theorem cyclicForAlgebra_iff_closedOperatorOrbit (M : VonNeumannAlgebra H) (Ω : H) :
    IsCyclicForAlgebra M Ω ↔ (operatorOrbit M.toStarSubalgebra Ω).topologicalClosure = ⊤ := by
  have he : {x : H | ∃ T : H →L[ℂ] H, T ∈ M ∧ x = T Ω} =
      (operatorOrbit M.toStarSubalgebra Ω : Set H) := by
    ext x
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨T, hT, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      exact ⟨T, hT, rfl⟩
  unfold IsCyclicForAlgebra
  rw [he, Submodule.span_eq]

theorem commutant_cyclic_of_separating (M : VonNeumannAlgebra H) (Ω : H)
    (hsep : IsSeparatingForAlgebra M Ω) : IsCyclicForAlgebra M.commutant Ω := by
  apply (cyclicForAlgebra_iff_closedOperatorOrbit M.commutant Ω).mpr
  let K := (operatorOrbit M.commutant.toStarSubalgebra Ω).topologicalClosure
  have hΩ : Ω ∈ K := (operatorOrbit M.commutant.toStarSubalgebra Ω).le_topologicalClosure
    ⟨1, one_mem _, by simp⟩
  have hP : K.starProjection ∈ M := by
    have hP' : K.starProjection ∈ M.commutant.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro T hT
      exact starProjection_commutes_of_invariant M.commutant.toStarSubalgebra K
        (fun S hS x hx => closedOperatorOrbit_invariant _ Ω hS hx) hT
    simpa only [VonNeumannAlgebra.commutant_commutant] using hP'
  have hz : (1 : H →L[ℂ] H) - K.starProjection = 0 :=
    hsep _ (sub_mem (one_mem M) hP) (by
      simp only [sub_apply, one_apply_eq_self,
        Submodule.starProjection_eq_self_iff.mpr hΩ, sub_self])
  have hPone : K.starProjection = 1 := (sub_eq_zero.mp hz).symm
  change K = ⊤
  apply top_unique
  intro x hx
  apply Submodule.starProjection_eq_self_iff.mp
  rw [hPone]
  rfl

theorem separating_of_commutant_cyclic (M : VonNeumannAlgebra H) (Ω : H)
    (hcyc : IsCyclicForAlgebra M.commutant Ω) : IsSeparatingForAlgebra M Ω := by
  intro T hT hTΩ
  have ho : operatorOrbit M.commutant.toStarSubalgebra Ω ≤ T.ker := by
    rintro x ⟨S, hS, rfl⟩
    change T (S Ω) = 0
    have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hS) T hT
    simpa only [mul_apply_eq_comp, hTΩ, map_zero] using
      congrArg (fun R : H →L[ℂ] H => R Ω) hc
  have hk := (operatorOrbit M.commutant.toStarSubalgebra Ω).topologicalClosure_minimal
    ho T.isClosed_ker
  have he := (cyclicForAlgebra_iff_closedOperatorOrbit M.commutant Ω).mp hcyc
  apply ContinuousLinearMap.ext
  intro x
  change T x = 0
  apply hk
  rw [he]
  trivial

theorem separating_iff_commutant_cyclic (M : VonNeumannAlgebra H) (Ω : H) :
    IsSeparatingForAlgebra M Ω ↔ IsCyclicForAlgebra M.commutant Ω :=
  ⟨commutant_cyclic_of_separating M Ω, separating_of_commutant_cyclic M Ω⟩

end VacuumBellSeparation.Bipartite

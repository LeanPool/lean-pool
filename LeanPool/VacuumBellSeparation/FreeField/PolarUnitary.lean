/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual polar unitary of an injective bounded map with dense range

The norm identity for the CFC square root of K* K gives an isometry on its
range. Mathlib's dense isometric extension constructs the full map. Dense
range of K and closed range of an isometry make this extension surjective.
No bounded inverse of the Gram square root is required.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Polar gram root obtained from `CFC.sqrt`. -/
noncomputable def polarGramRoot (K : E →L[ℂ] H) : E →L[ℂ] E :=
  CFC.sqrt (K.adjoint.comp K)

theorem polarGramRoot_adjoint_comp_self (K : E →L[ℂ] H) :
    (polarGramRoot K).adjoint.comp (polarGramRoot K) = K.adjoint.comp K := by
  have hp : 0 ≤ K.adjoint.comp K := nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self K)
  change star (CFC.sqrt (K.adjoint.comp K)) * CFC.sqrt (K.adjoint.comp K) = _
  rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, ← pow_two, CFC.sq_sqrt _ hp]

theorem norm_polarGramRoot (K : E →L[ℂ] H) (x : E) :
    ‖polarGramRoot K x‖ = ‖K x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [(polarGramRoot K).apply_norm_sq_eq_inner_adjoint_right,
    K.apply_norm_sq_eq_inner_adjoint_right, polarGramRoot_adjoint_comp_self]

theorem polarGramRoot_injective (K : E →L[ℂ] H) (hK : Function.Injective K) :
    Function.Injective (polarGramRoot K) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hK
  rw [map_zero]
  apply norm_eq_zero.mp
  rw [← norm_polarGramRoot K, map_sub, hxy, sub_self, norm_zero]

theorem polarGramRoot_denseRange (K : E →L[ℂ] H) (hK : Function.Injective K) :
    DenseRange (polarGramRoot K) := by
  have hs : IsSelfAdjoint (polarGramRoot K) := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hker : (polarGramRoot K).ker = ⊥ := LinearMap.ker_eq_bot.mpr (polarGramRoot_injective K hK)
  have horth : (polarGramRoot K).rangeᗮ = ⊥ := by
    rw [(polarGramRoot K).orthogonal_range]
    change (star (polarGramRoot K)).ker = ⊥
    rw [hs.star_eq, hker]
  have hclose := (polarGramRoot K).range.topologicalClosure_eq_top_iff.mpr horth
  rw [denseRange_iff_closure_range]
  change ((polarGramRoot K).range.topologicalClosure : Set E) = Set.univ
  rw [hclose]
  rfl

/-- Polar isometry of type `E →ₗᵢ[ℂ] H`. -/
noncomputable def polarIsometry (K : E →L[ℂ] H) (hK : Function.Injective K) : E →ₗᵢ[ℂ] H :=
  K.toLinearMap.extendOfIsometry (e := (polarGramRoot K).toLinearMap)
    (polarGramRoot_denseRange K hK) (fun x => (norm_polarGramRoot K x).symm)

@[simp] theorem polarIsometry_polarGramRoot (K : E →L[ℂ] H) (hK : Function.Injective K)
    (x : E) : polarIsometry K hK (polarGramRoot K x) = K x :=
  LinearMap.extendOfIsometry_eq _ _ _ _

theorem polarIsometry_surjective (K : E →L[ℂ] H) (hK : Function.Injective K)
    (hd : DenseRange K) : Function.Surjective (polarIsometry K hK) := by
  have hr : Set.range K ⊆ Set.range (polarIsometry K hK) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨polarGramRoot K x, polarIsometry_polarGramRoot K hK x⟩
  have hdU : DenseRange (polarIsometry K hK) := hd.mono hr
  intro y
  have hy := hdU y
  rw [(polarIsometry K hK).isometry.isClosedEmbedding.isClosed_range.closure_eq] at hy
  exact hy

/-- Linear isometry equivalence for the polar unitary, of type `E ≃ₗᵢ[ℂ] H`. -/
noncomputable def polarUnitary (K : E →L[ℂ] H) (hK : Function.Injective K)
    (hd : DenseRange K) : E ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (polarIsometry K hK) (polarIsometry_surjective K hK hd)

@[simp] theorem polarUnitary_polarGramRoot (K : E →L[ℂ] H) (hK : Function.Injective K)
    (hd : DenseRange K) (x : E) : polarUnitary K hK hd (polarGramRoot K x) = K x :=
  polarIsometry_polarGramRoot K hK x

theorem polarUnitary_factorization (K : E →L[ℂ] H) (hK : Function.Injective K)
    (hd : DenseRange K) :
    (polarUnitary K hK hd).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (polarGramRoot K) = K := by
  ext x
  exact polarUnitary_polarGramRoot K hK hd x

end VacuumBellSeparation

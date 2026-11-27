/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplementaryGramPartition
public import LeanPool.VacuumBellSeparation.FreeField.ModularWeightNorm
public import LeanPool.VacuumBellSeparation.FreeField.SourceReserveFactorization
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Reserve factors and Riesz vectors from the two actual source weights

The two estimates are genuine hypotheses on the given linear map. Their
combination uses a bounded continuous-calculus partition, followed by the
proved dense-range factorization of the actual reserve. No inverse of the
reserve on the whole Hilbert space is asserted.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem sourceReserve_bound_of_two_modular_weights
    (T : ComplexSourceHilbert hm U →ₗ[ℂ] F) {b C₁ C₂ : ℝ}
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ z, ‖T z‖ ≤ C₁ * ‖sourceModularWeight hm U ((1 - b) / 2) z‖)
    (h₂ : ∀ z, ‖T z‖ ≤ C₂ * ‖sourceModularWeight hm U (b / 2) z‖) :
    ∀ z, ‖T z‖ ≤ (C₁ + C₂) * ‖(sourceReserve hm U ^ b) z‖ := by
  rw [sourceReserve_eq_normalized_reserve]
  apply bound_reserve_of_complementary_weights
    (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hm U))
    (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm U))
    T hb hb1 hC₁ hC₂
  · intro z
    simpa only [sourceModularWeight, sourceGram_eq_normalized_commutation,
      conjugateSourceGram_eq, gramPlus, gramMinus, normalizedCommutation,
      show (1 / 2 : ℝ) - (1 - b) / 2 = b / 2 by ring] using h₁ z
  · intro z
    simpa only [sourceModularWeight, sourceGram_eq_normalized_commutation,
      conjugateSourceGram_eq, gramPlus, gramMinus, normalizedCommutation,
      show (1 / 2 : ℝ) - b / 2 = (1 - b) / 2 by ring] using h₂ z

theorem existsUnique_sourceReserve_factor_of_two_modular_weights [CompleteSpace F]
    (hU : Bornology.IsBounded U) (T : ComplexSourceHilbert hm U →ₗ[ℂ] F)
    {b C₁ C₂ : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ z, ‖T z‖ ≤ C₁ * ‖sourceModularWeight hm U ((1 - b) / 2) z‖)
    (h₂ : ∀ z, ‖T z‖ ≤ C₂ * ‖sourceModularWeight hm U (b / 2) z‖) :
    ∃! L : ComplexSourceHilbert hm U →L[ℂ] F,
      (∀ z, L ((sourceReserve hm U ^ b) z) = T z) ∧ ‖L‖ ≤ C₁ + C₂ := by
  apply (sourceReserve_factorization_iff hm U hU T
    (by linarith : 0 ≤ b) hb1 (add_nonneg hC₁ hC₂)).mp
  exact sourceReserve_bound_of_two_modular_weights hm U T hb hb1 hC₁ hC₂ h₁ h₂

/-- The Riesz vector represents the actual linear functional after the reserve.
The second identity is the conjugate-first convention needed for real moments. -/
theorem exists_sourceReserve_riesz_of_bound (hU : Bornology.IsBounded U)
    (T : ComplexSourceHilbert hm U →ₗ[ℂ] ℂ) {b C : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hC : 0 ≤ C)
    (hT : ∀ z, ‖T z‖ ≤ C * ‖(sourceReserve hm U ^ b) z‖) :
    ∃ v : ComplexSourceHilbert hm U, ‖v‖ ≤ C ∧
      (∀ z, inner ℂ v ((sourceReserve hm U ^ b) z) = T z) ∧
      (∀ z, inner ℂ z ((sourceReserve hm U ^ b) v) = conj (T z)) := by
  obtain ⟨L, ⟨hL, hnorm⟩, _⟩ :=
    (sourceReserve_factorization_iff hm U hU T hb hb1 hC).mp hT
  let v := (InnerProductSpace.toDual ℂ (ComplexSourceHilbert hm U)).symm L
  have hv (z : ComplexSourceHilbert hm U) :
      inner ℂ v ((sourceReserve hm U ^ b) z) = T z := by
    rw [InnerProductSpace.toDual_symm_apply, hL]
  refine ⟨v, ?_, hv, ?_⟩
  · exact ((InnerProductSpace.toDual ℂ (ComplexSourceHilbert hm U)).symm.norm_map L).le.trans hnorm
  · intro z
    have hs : (sourceReserve hm U ^ b).adjoint = sourceReserve hm U ^ b :=
      (CFC.rpow_nonneg (a := sourceReserve hm U) (y := b)).isSelfAdjoint.adjoint_eq
    calc
      inner ℂ z ((sourceReserve hm U ^ b) v) =
          inner ℂ ((sourceReserve hm U ^ b) z) v := by
        rw [← adjoint_inner_left, hs]
      _ = conj (inner ℂ v ((sourceReserve hm U ^ b) z)) := (inner_conj_symm _ _).symm
      _ = conj (T z) := by rw [hv]

theorem exists_sourceReserve_riesz_of_two_modular_weights
    (hU : Bornology.IsBounded U) (T : ComplexSourceHilbert hm U →ₗ[ℂ] ℂ)
    {b C₁ C₂ : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ z, ‖T z‖ ≤ C₁ * ‖sourceModularWeight hm U ((1 - b) / 2) z‖)
    (h₂ : ∀ z, ‖T z‖ ≤ C₂ * ‖sourceModularWeight hm U (b / 2) z‖) :
    ∃ v : ComplexSourceHilbert hm U, ‖v‖ ≤ C₁ + C₂ ∧
      (∀ z, inner ℂ v ((sourceReserve hm U ^ b) z) = T z) ∧
      (∀ z, inner ℂ z ((sourceReserve hm U ^ b) v) = conj (T z)) :=
  exists_sourceReserve_riesz_of_bound hm U hU T (by linarith) hb1
    (add_nonneg hC₁ hC₂)
    (sourceReserve_bound_of_two_modular_weights hm U T hb hb1 hC₁ hC₂ h₁ h₂)

end VacuumBellSeparation

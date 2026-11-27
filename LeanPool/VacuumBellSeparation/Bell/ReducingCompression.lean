/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.Compression
public import LeanPool.VacuumBellSeparation.FreeField.Isotony

/-!
# Restriction of generated algebras to actual reducing subspaces

Compression along a Hilbert isometry is restriction when its image reduces
the generators. Operators commuting with the compressed generators extend
by zero to operators commuting with the original generators. Consequently
compression maps the actual generated double commutant into the compressed
generated double commutant. This supplies the operator-algebra step beyond
matching vector characteristic functions.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Extend operator by zero obtained from `ι.toContinuousLinearMap.comp`. -/
noncomputable def extendOperatorByZero (ι : E →ₗᵢ[ℂ] F) (B : E →L[ℂ] E) : F →L[ℂ] F :=
  ι.toContinuousLinearMap.comp (B.comp ι.toContinuousLinearMap.adjoint)

theorem compression_star (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F) :
    compression ι (star A) = star (compression ι A) := by
  simp only [compression, star_eq_adjoint, adjoint_comp, adjoint_adjoint, comp_assoc]

theorem compression_intertwines_of_commute (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F)
    (hA : A * imageProjection ι = imageProjection ι * A) (x : E) :
    A (ι x) = ι (compression ι A x) := by
  have h := congrArg (fun T : F →L[ℂ] F => T (ι x)) hA
  simpa only [imageProjection, compression, mul_apply_eq_comp, comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, adjoint_embedding_apply] using h

theorem compression_adjoint_intertwines_of_commute (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F)
    (hA : A * imageProjection ι = imageProjection ι * A) (x : F) :
    compression ι A (ι.toContinuousLinearMap.adjoint x) =
      ι.toContinuousLinearMap.adjoint (A x) := by
  have h := congrArg (fun T : F →L[ℂ] F => ι.toContinuousLinearMap.adjoint (T x)) hA
  simpa only [imageProjection, compression, mul_apply_eq_comp, comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, adjoint_embedding_apply] using h

theorem commute_extendOperatorByZero (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F)
    (hA : A * imageProjection ι = imageProjection ι * A) (B : E →L[ℂ] E)
    (hB : compression ι A * B = B * compression ι A) :
    A * extendOperatorByZero ι B = extendOperatorByZero ι B * A := by
  ext x
  change A (ι (B (ι.toContinuousLinearMap.adjoint x))) =
    ι (B (ι.toContinuousLinearMap.adjoint (A x)))
  rw [compression_intertwines_of_commute ι A hA, ← mul_apply_eq_comp, hB,
    mul_apply_eq_comp, compression_adjoint_intertwines_of_commute ι A hA]

/-- The actual algebra restriction, proved by extending each commutant
operator by zero on the orthogonal complement. -/
theorem compression_mem_generatedVNA (ι : E →ₗᵢ[ℂ] F) (S : Set (F →L[ℂ] F))
    (hS : ∀ A ∈ S, A * imageProjection ι = imageProjection ι * A)
    {T : F →L[ℂ] F} (hT : T ∈ generatedVNA S) :
    compression ι T ∈ generatedVNA (compression ι '' S) := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro B hB
  have hB' : extendOperatorByZero ι B ∈ commutantOf S := by
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    have hb := (StarSubalgebra.mem_centralizer_iff ℂ).mp hB _ ⟨A, hA, rfl⟩
    refine ⟨commute_extendOperatorByZero ι A (hS A hA) B hb.1, ?_⟩
    have hs : star A * imageProjection ι = imageProjection ι * star A := by
      have h := congrArg star (hS A hA)
      simpa only [star_mul, (imageProjection_isStarProjection ι).isSelfAdjoint.star_eq] using h.symm
    apply commute_extendOperatorByZero ι (star A) hs B
    simpa only [compression_star] using hb.2
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hT _ hB'
  ext x
  have h := congrArg (fun A : F →L[ℂ] F => ι.toContinuousLinearMap.adjoint (A (ι x))) hc
  simpa only [compression, extendOperatorByZero, mul_apply_eq_comp, comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, adjoint_embedding_apply] using h

/-- Multiplication is preserved whenever the right factor preserves the
actual embedded Hilbert subspace. -/
theorem compression_mul_of_invariant (ι : E →ₗᵢ[ℂ] F) (A B : F →L[ℂ] F)
    (hB : ∀ x, B (ι x) = ι (compression ι B x)) :
    compression ι (A * B) = compression ι A * compression ι B := by
  ext x
  change ι.toContinuousLinearMap.adjoint (A (B (ι x))) =
    ι.toContinuousLinearMap.adjoint (A (ι (compression ι B x)))
  rw [hB]

end VacuumBellSeparation

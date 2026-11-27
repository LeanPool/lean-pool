/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSIsometricRealization
public import LeanPool.VacuumBellSeparation.Bell.VectorFunctionalNormal
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import LeanPool.VacuumBellSeparation.Bell.FiniteAmplification
public import Mathlib.Algebra.BigOperators.Pi

/-!
Finite positive vector sums and their actual diagonal Hilbert amplification.
The finite index type is allowed to be empty. Domination constructs vectors
in the original H via the actual amplified bounded vector-RN theorem.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ι : Type*) [Fintype ι]

/-- The continuous operator applying T separately to every coordinate. -/
def finiteDiagonalOperator (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  finiteAmplification ι T

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem finiteDiagonalOperator_apply (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    finiteDiagonalOperator ι T x i = T (x i) := rfl

/-- The diagonal amplification is an actual unital star-algebra homomorphism. -/
def finiteDiagonalStarAlgHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
  finiteAmplificationHom ι

@[simp] theorem finiteDiagonalStarAlgHom_apply (T : H →L[ℂ] H) :
    finiteDiagonalStarAlgHom (H := H) ι T = finiteDiagonalOperator ι T := rfl

variable {ι}

/-- Literal finite sum of original-H vector functionals. -/
def finiteVectorFunctional (M : VonNeumannAlgebra H) (ξ : ι → H) :
    M.toStarSubalgebra →ₚ[ℂ] ℂ := ∑ i, vectorPositiveLinearMap M (ξ i)

@[simp] theorem finiteVectorFunctional_apply (M : VonNeumannAlgebra H)
    (ξ : ι → H) (a : M.toStarSubalgebra) :
    finiteVectorFunctional M ξ a = ∑ i, inner ℂ (ξ i) ((a : H →L[ℂ] H) (ξ i)) := by
  simp only [finiteVectorFunctional, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- A functional dominated by a finite vector sum is itself a finite vector
sum on original H; no cyclicity of H and no normal-representation field. -/
theorem exists_finite_vector_sum_of_domination (M : VonNeumannAlgebra H)
    (ψ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (ξ : ι → H) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : M.toStarSubalgebra, 0 ≤ a → ψ a ≤ C • finiteVectorFunctional M ξ a) :
    ∃ ζ : ι → H, ψ = finiteVectorFunctional M ζ := by
  let χ := finiteVectorFunctional M ξ
  let π := (finiteDiagonalStarAlgHom (H := H) ι).comp M.toStarSubalgebra.subtype
  let Ω : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 ξ
  have hχ (a : M.toStarSubalgebra) : χ a = inner ℂ Ω (π a Ω) := by
    exact (finiteVectorFunctional_apply M ξ a).trans
      (PiLp.inner_apply Ω (π a Ω)).symm
  obtain ⟨ζ, _, hζ⟩ := exists_dominated_vector_in_representation χ ψ π Ω hχ C hC hdom
  refine ⟨fun i => ζ i, ?_⟩
  apply PositiveLinearMap.ext
  intro a
  calc
    ψ a = inner ℂ ζ (π a ζ) := (hζ a).symm
    _ = ∑ i, inner ℂ (ζ i) ((a : H →L[ℂ] H) (ζ i)) := PiLp.inner_apply ζ (π a ζ)
    _ = finiteVectorFunctional M (fun i => ζ i) a :=
      (finiteVectorFunctional_apply M (fun i => ζ i) a).symm

end VacuumBellSeparation.Bipartite

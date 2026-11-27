/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveMatrixFeatures

/-!
# Positive matrix forms with finite diagonal sum extend uniquely

This is the operator-extension step used in Appendix A. The input is an
actual positive matrix on the whole occupation index, with summable real
diagonal. The constructed bounded operator has exactly these matrix
coefficients, is positive, and has finite positive trace equal to the
diagonal sum. No prior bounded extension is an assumption.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped lp

open scoped ComplexConjugate ComplexOrder

variable {ι : Type*}

/-- Continuous linear map for the positive matrix operator, of type `ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)`. -/
def positiveMatrixOperator (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  familyGramOperator (positiveMatrixFeature K) (summable_positiveMatrixFeature_norm_sq K hdiag)

theorem positiveMatrixOperator_nonneg (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) : 0 ≤ positiveMatrixOperator K hdiag :=
  familyGramOperator_nonneg _ _

theorem positiveMatrixOperator_matrix (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) (i j : ι) :
    inner ℂ (coordinateHilbertBasis ι i) (positiveMatrixOperator K hdiag
      (coordinateHilbertBasis ι j)) =
      K i j := by
  rw [positiveMatrixOperator, familyGramOperator_matrix, inner_positiveMatrixFeature]

theorem positiveTrace_positiveMatrixOperator (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) :
    positiveTrace (positiveMatrixOperator K hdiag) = ENNReal.ofReal (∑' i, (K i i).re) := by
  rw [positiveMatrixOperator, positiveTrace_familyGramOperator]
  simp only [norm_positiveMatrixFeature_sq]

theorem positiveMatrixOperator_isPositiveTraceClass (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) : IsPositiveTraceClass
      (positiveMatrixOperator K hdiag) :=
  familyGramOperator_isPositiveTraceClass _ _

theorem operator_eq_of_coordinate_matrix (A B : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))
    (h : ∀ i j, inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι j)) =
      inner ℂ (coordinateHilbertBasis ι i) (B (coordinateHilbertBasis ι j))) : A = B := by
  apply continuousLinearMap_eq_of_dense_span (coordinateHilbertBasis ι)
    (coordinateHilbertBasis ι).dense_span
  intro j
  apply lp.ext
  funext i
  simpa only [coordinateHilbertBasis_inner] using h i j

/-- Exact extension of the original sesquilinear form on finite coordinate
linear combinations. The input positivity is the usual `Matrix.PosSemidef`. -/
theorem positiveMatrixOperator_finite_form (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) (c d : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ (coordinateHilbertBasis ι) c)
      (positiveMatrixOperator K hdiag (Finsupp.linearCombination ℂ (coordinateHilbertBasis ι) d)) =
        c.sum fun i ci => d.sum fun j dj => conj ci * K i j * dj := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
    simp only [map_add, inner_add_left, h₁, h₂]
    simp [Finsupp.sum_add_index, add_mul, map_add]
  | single i a =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d₁ d₂ h₁ h₂ =>
      simp only [map_add, inner_add_right, h₁, h₂]
      simp [Finsupp.sum_add_index, mul_add]
    | single j b =>
      have hcoord : positiveMatrixOperator K hdiag (coordinateHilbertBasis ι j) i = K i j := by
        simpa only [coordinateHilbertBasis_inner] using positiveMatrixOperator_matrix K hdiag i j
      simp [Finsupp.linearCombination_single, map_smul,
        hcoord, mul_comm, mul_left_comm]

/-- A positive matrix with finite diagonal sum has a unique actual positive
trace-class extension to the full ℓ² space, with the specified trace. -/
theorem existsUnique_positive_matrix_extension (K : Matrix ι ι ℂ) (hK : K.PosSemidef)
    (hdiag : Summable fun i => (K i i).re) :
    ∃! A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ),
      IsPositiveTraceClass A ∧
      (∀ i j, inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι j)) = K i j) ∧
      positiveTrace A = ENNReal.ofReal (∑' i, (K i i).re) := by
  let : Fact K.PosSemidef := ⟨hK⟩
  refine ⟨positiveMatrixOperator K hdiag,
    ⟨positiveMatrixOperator_isPositiveTraceClass K hdiag,
      positiveMatrixOperator_matrix K hdiag, positiveTrace_positiveMatrixOperator K hdiag⟩, ?_⟩
  intro A hA
  apply operator_eq_of_coordinate_matrix A (positiveMatrixOperator K hdiag)
  intro i j
  rw [hA.2.1 i j, positiveMatrixOperator_matrix]

end VacuumBellSeparation.Gaussian

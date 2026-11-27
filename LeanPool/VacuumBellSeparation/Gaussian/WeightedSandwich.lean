/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveMatrixExtension

/-!
# Constructing positive inverse sandwiches from their weighted diagonal

For an arbitrary positive bounded operator A and arbitrary real coordinate
weights r, summability of r_i² ⟨e_i,Ae_i⟩ constructs the actual positive
trace-class operator with matrix r_i r_j ⟨e_i,Ae_j⟩. If a self-adjoint
bounded operator B has eigenvalues inverse to r on the coordinate basis,
then B Θ B = A. No commutativity between A and B is required.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped lp

variable {ι : Type*}

/-- Resolve the canonical real scalar commutation before specializing to the lp carrier. -/
theorem hilbertOperator_real_smulCommClass {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) :=
  Algebra.to_smulCommClass

local instance coordinateOperator_real_smulCommClass :
    SMulCommClass ℝ (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) :=
  hilbertOperator_real_smulCommClass (E := ℓ²(ι, ℂ))

/-- The canonical algebra scalar tower, resolved before the concrete lp specialization. -/
theorem hilbertOperator_real_isScalarTower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    IsScalarTower ℝ (E →L[ℂ] E) (E →L[ℂ] E) := IsScalarTower.right

local instance coordinateOperator_real_isScalarTower :
    IsScalarTower ℝ (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) :=
  hilbertOperator_real_isScalarTower (E := ℓ²(ι, ℂ))

theorem weightedHilbertOperator_realCFC {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

local instance coordinateOperator_realCFC :
    IsometricContinuousFunctionalCalculus ℝ
      (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) IsSelfAdjoint :=
  weightedHilbertOperator_realCFC (E := ℓ²(ι, ℂ))

/-- Weighted sandwich feature defined as `r i • CFC.sqrt A (coordinateHilbertBasis ι i)`. -/
def weightedSandwichFeature (A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) (r : ι → ℝ) (i : ι) : ℓ²(ι, ℂ) :=
  r i • CFC.sqrt A (coordinateHilbertBasis ι i)

/-- Weighted sandwich diagonal given by `r i ^ 2 * (inner ℂ (coordinateHilbertBasis ι i) (A
(coordinateHilbertBasis ι i))).re`. -/
def weightedSandwichDiagonal (A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) (r : ι → ℝ) (i : ι) : ℝ :=
  r i ^ 2 * (inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι i))).re

theorem weightedSandwichFeature_norm_sq {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (i : ι) :
    ‖weightedSandwichFeature A r i‖ ^ 2 = weightedSandwichDiagonal A r i := by
  calc
    _ = r i ^ 2 * ‖CFC.sqrt A (coordinateHilbertBasis ι i)‖ ^ 2 := by
      rw [weightedSandwichFeature, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ = _ := congrArg (fun t : ℝ => r i ^ 2 * t)
      (sqrt_norm_sq_eq_diagonal hA (coordinateHilbertBasis ι i))

theorem inner_weightedSandwichFeature {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (i j : ι) :
    inner ℂ (weightedSandwichFeature A r i) (weightedSandwichFeature A r j) =
      (r i : ℂ) * (r j : ℂ) *
        inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι j)) := by
  have hs : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hinner : inner ℂ (CFC.sqrt A (coordinateHilbertBasis ι i))
      (CFC.sqrt A (coordinateHilbertBasis ι j)) =
        inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι j)) := by
    rw [← (CFC.sqrt A).adjoint_inner_right, hs.adjoint_eq,
      ← mul_apply_eq_comp, ← pow_two, CFC.sq_sqrt A hA]
  rw [weightedSandwichFeature, weightedSandwichFeature,
    inner_smul_left_eq_smul, inner_smul_right_eq_smul, hinner]
  simp only [Algebra.smul_def, Complex.coe_algebraMap]
  ring

/-- Continuous linear map for the weighted sandwich operator, of type `ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)`. -/
def weightedSandwichOperator {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (hsum : Summable (weightedSandwichDiagonal A r)) :
    ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  familyGramOperator (weightedSandwichFeature A r)
    (by simpa only [weightedSandwichFeature_norm_sq hA] using hsum)

theorem weightedSandwichOperator_isPositiveTraceClass {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (hsum : Summable (weightedSandwichDiagonal A r)) :
    IsPositiveTraceClass (weightedSandwichOperator hA r hsum) :=
  familyGramOperator_isPositiveTraceClass _ _

theorem weightedSandwichOperator_matrix {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (hsum : Summable (weightedSandwichDiagonal A r)) (i j : ι) :
    inner ℂ (coordinateHilbertBasis ι i)
      (weightedSandwichOperator hA r hsum (coordinateHilbertBasis ι j)) =
        (r i : ℂ) * (r j : ℂ) *
          inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι j)) := by
  rw [weightedSandwichOperator, familyGramOperator_matrix, inner_weightedSandwichFeature hA]

theorem positiveTrace_weightedSandwichOperator {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (hsum : Summable (weightedSandwichDiagonal A r)) :
    positiveTrace (weightedSandwichOperator hA r hsum) =
      ENNReal.ofReal (∑' i, weightedSandwichDiagonal A r i) := by
  rw [weightedSandwichOperator, positiveTrace_familyGramOperator]
  simp only [weightedSandwichFeature_norm_sq hA]

theorem coordinate_matrix_sandwich (A B : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))
    (hB : IsSelfAdjoint B) (b : ι → ℝ)
    (heig : ∀ i, B (coordinateHilbertBasis ι i) = b i • coordinateHilbertBasis ι i) (i j : ι) :
    inner ℂ (coordinateHilbertBasis ι i) ((B * A * B) (coordinateHilbertBasis ι j)) =
      (b i : ℂ) * (b j : ℂ) * inner ℂ (coordinateHilbertBasis ι i) (A
        (coordinateHilbertBasis ι j)) := by
  simp only [mul_apply_eq_comp]
  have hmove : inner ℂ (coordinateHilbertBasis ι i) (B (A (B (coordinateHilbertBasis ι j)))) =
      inner ℂ (B (coordinateHilbertBasis ι i)) (A (B (coordinateHilbertBasis ι j))) := by
    simpa only [hB.adjoint_eq] using
      B.adjoint_inner_right (coordinateHilbertBasis ι i) (A (B (coordinateHilbertBasis ι j)))
  rw [hmove, heig, heig, LinearMapClass.map_smul_of_tower,
    inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  simp only [Algebra.smul_def, Complex.coe_algebraMap]
  ring

/-- Actual operator factorization, with no commutativity assumption. -/
theorem weightedSandwichOperator_factorization {A : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hA : 0 ≤ A) (r : ι → ℝ) (hsum : Summable (weightedSandwichDiagonal A r))
    (B : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) (hB : IsSelfAdjoint B) (b : ι → ℝ)
    (heig : ∀ i, B (coordinateHilbertBasis ι i) = b i • coordinateHilbertBasis ι i)
    (hcancel : ∀ i, b i * r i = 1) :
    B * weightedSandwichOperator hA r hsum * B = A := by
  apply operator_eq_of_coordinate_matrix
  intro i j
  rw [coordinate_matrix_sandwich _ B hB b heig, weightedSandwichOperator_matrix]
  have hi : (b i : ℂ) * (r i : ℂ) = 1 := by exact_mod_cast hcancel i
  have hj : (b j : ℂ) * (r j : ℂ) = 1 := by exact_mod_cast hcancel j
  calc
    _ = ((b i : ℂ) * r i) * ((b j : ℂ) * r j) *
        inner ℂ (coordinateHilbertBasis ι i) (A (coordinateHilbertBasis ι j)) := by ring
    _ = _ := by rw [hi, hj, one_mul, one_mul]

end VacuumBellSeparation.Gaussian

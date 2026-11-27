/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveMatrixExtension
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtCompact

/-!
# Actual operators from square-summable infinite matrix coefficients

A matrix whose full squared coefficient sum is finite defines an actual
Hilbert--Schmidt operator on the full coordinate Hilbert space. Positivity
of its finitely supported form implies positivity of this operator by
density and continuity. Only the square trace is finite: no summability
of the original diagonal and no trace-class assumption on the operator
are imposed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal lp ComplexConjugate ComplexOrder

variable {ι : Type*}

/-- Matrix Hilbert schmidt square given by `∑' i, ∑' j, ENNReal.ofReal (‖K i j‖ ^ 2)`. -/
def matrixHilbertSchmidtSquare (K : Matrix ι ι ℂ) : ℝ≥0∞ :=
  ∑' i, ∑' j, ENNReal.ofReal (‖K i j‖ ^ 2)

theorem matrix_row_norm_sq_summable (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (i : ι) :
    Summable fun j => ‖K i j‖ ^ 2 := by
  have hi : (∑' j, ENNReal.ofReal (‖K i j‖ ^ 2)) < ∞ :=
    lt_of_le_of_lt
      (le_tsum (f := fun i => ∑' j, ENNReal.ofReal (‖K i j‖ ^ 2)) i) hK
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hi.ne

/-- The conjugated row is the vector representing the corresponding
complex-linear coordinate functional. -/
def matrixRowVector (K : Matrix ι ι ℂ) (hK : matrixHilbertSchmidtSquare K < ∞)
    (i : ι) : ℓ²(ι, ℂ) :=
  ⟨fun j => conj (K i j), by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat, Complex.norm_conj, Real.rpow_two]
      using matrix_row_norm_sq_summable K hK i⟩

@[simp] theorem matrixRowVector_apply (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (i j : ι) :
    matrixRowVector K hK i j = conj (K i j) := rfl

theorem matrixRowVector_norm_sq (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (i : ι) :
    ‖matrixRowVector K hK i‖ ^ 2 = ∑' j, ‖K i j‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, matrixRowVector_apply, Complex.norm_conj] using
    (lp.hasSum_norm (p := 2) (by norm_num) (matrixRowVector K hK i)).tsum_eq.symm

theorem ofReal_matrixRowVector_norm_sq (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (i : ι) :
    ENNReal.ofReal (‖matrixRowVector K hK i‖ ^ 2) =
      ∑' j, ENNReal.ofReal (‖K i j‖ ^ 2) := by
  rw [matrixRowVector_norm_sq]
  exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    (matrix_row_norm_sq_summable K hK i)

theorem matrixRowVector_summable_norm_sq (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) :
    Summable fun i => ‖matrixRowVector K hK i‖ ^ 2 := by
  have hs := ENNReal.summable_toReal hK.ne
  change Summable (fun i => (∑' j, ENNReal.ofReal (‖K i j‖ ^ 2)).toReal) at hs
  simpa only [← ofReal_matrixRowVector_norm_sq K hK,
    ENNReal.toReal_ofReal (sq_nonneg _)] using hs

/-- Continuous linear map for the hilbert schmidt matrix operator, of type `ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι,
ℂ)`. -/
def hilbertSchmidtMatrixOperator (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  familyAnalysis (matrixRowVector K hK) (matrixRowVector_summable_norm_sq K hK)

theorem hilbertSchmidtMatrixOperator_matrix (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (i j : ι) :
    inner ℂ (coordinateHilbertBasis ι i)
      (hilbertSchmidtMatrixOperator K hK (coordinateHilbertBasis ι j)) = K i j := by
  rw [coordinateHilbertBasis_inner]
  change inner ℂ (matrixRowVector K hK i) (coordinateHilbertBasis ι j) = _
  rw [← inner_conj_symm, coordinateHilbertBasis_inner, matrixRowVector_apply]
  simp

theorem hilbertSchmidtMatrixOperator_square (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) :
    basisHilbertSchmidtSquare (coordinateHilbertBasis ι) (hilbertSchmidtMatrixOperator K hK) =
      matrixHilbertSchmidtSquare K := by
  rw [basisHilbertSchmidtSquare_adjoint (coordinateHilbertBasis ι) (coordinateHilbertBasis ι)]
  unfold basisHilbertSchmidtSquare matrixHilbertSchmidtSquare hilbertSchmidtMatrixOperator
  simp only [familyAnalysis_adjoint_basis, ofReal_matrixRowVector_norm_sq]

theorem positiveTrace_hilbertSchmidtMatrixOperator_square (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) :
    positiveTrace ((hilbertSchmidtMatrixOperator K hK).adjoint.comp
      (hilbertSchmidtMatrixOperator K hK)) = matrixHilbertSchmidtSquare K := by
  rw [positiveTrace_adjoint_comp (coordinateHilbertBasis ι), hilbertSchmidtMatrixOperator_square]

theorem hilbertSchmidtMatrixOperator_isCompact (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) :
    IsCompactOperator (hilbertSchmidtMatrixOperator K hK) := by
  apply isCompactOperator_of_hilbertSchmidt (coordinateHilbertBasis ι)
  rwa [hilbertSchmidtMatrixOperator_square]

theorem coordinate_operator_finite_form (T : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))
    (K : Matrix ι ι ℂ)
    (hT : ∀ i j, inner ℂ (coordinateHilbertBasis ι i) (T (coordinateHilbertBasis ι j)) = K i j)
    (c d : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ (coordinateHilbertBasis ι) c)
      (T (Finsupp.linearCombination ℂ (coordinateHilbertBasis ι) d)) =
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
      simp [Finsupp.linearCombination_single, map_smul,
        hT, mul_comm, mul_left_comm]

theorem operator_nonneg_of_positive_coordinate_matrix
    (T : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)) (K : Matrix ι ι ℂ) (hK : K.PosSemidef)
    (hT : ∀ i j, inner ℂ (coordinateHilbertBasis ι i) (T (coordinateHilbertBasis ι j)) = K i j) :
    0 ≤ T := by
  have hquad (x : ℓ²(ι, ℂ)) :
      0 ≤ (inner ℂ x (T x)).re ∧ (inner ℂ x (T x)).im = 0 := by
    have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (coordinateHilbertBasis ι).dense_span
    apply hd.induction
      (P := fun x => 0 ≤ (inner ℂ x (T x)).re ∧ (inner ℂ x (T x)).im = 0) ?_ ?_ x
    · intro y hy
      rw [← Finsupp.range_linearCombination] at hy
      obtain ⟨c, rfl⟩ := hy
      rw [coordinate_operator_finite_form T K hT]
      have hc := Complex.nonneg_iff.mp (hK.2 c)
      exact ⟨hc.1, hc.2.symm⟩
    · have hre : Continuous (fun x : ℓ²(ι, ℂ) => (inner ℂ x (T x)).re) := by
        fun_prop
      have him : Continuous (fun x : ℓ²(ι, ℂ) => (inner ℂ x (T x)).im) := by
        fun_prop
      exact (isClosed_le continuous_const hre).inter
        (isClosed_eq him continuous_const)
  apply nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
  intro x
  have hre : 0 ≤ (inner ℂ (T x) x).re := by
    change 0 ≤ RCLike.re (inner ℂ (T x) x)
    rw [inner_re_symm]
    exact (hquad x).1
  have him : (inner ℂ (T x) x).im = 0 := by
    change RCLike.im (inner ℂ (T x) x) = 0
    rw [inner_im_symm]
    exact neg_eq_zero.mpr (hquad x).2
  refine ⟨?_, hre⟩
  apply Complex.ext <;> simp [him]

theorem hilbertSchmidtMatrixOperator_nonneg (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (hpos : K.PosSemidef) :
    0 ≤ hilbertSchmidtMatrixOperator K hK :=
  operator_nonneg_of_positive_coordinate_matrix _ K hpos
    (hilbertSchmidtMatrixOperator_matrix K hK)

/-- The positive extension is unique among bounded operators, and its
actual square trace is the full squared matrix-coefficient sum. -/
theorem existsUnique_positive_hilbertSchmidt_matrix_extension (K : Matrix ι ι ℂ)
    (hK : matrixHilbertSchmidtSquare K < ∞) (hpos : K.PosSemidef) :
    ∃! T : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ), 0 ≤ T ∧
      (∀ i j, inner ℂ (coordinateHilbertBasis ι i) (T (coordinateHilbertBasis ι j)) = K i j) ∧
      positiveTrace (T * T) = matrixHilbertSchmidtSquare K := by
  let T := hilbertSchmidtMatrixOperator K hK
  have hT : 0 ≤ T := hilbertSchmidtMatrixOperator_nonneg K hK hpos
  refine ⟨T, ⟨hT, hilbertSchmidtMatrixOperator_matrix K hK, ?_⟩, ?_⟩
  · have hs := positiveTrace_hilbertSchmidtMatrixOperator_square K hK
    change positiveTrace (star T * T) = _ at hs
    rwa [hT.isSelfAdjoint.star_eq] at hs
  · intro A hA
    apply operator_eq_of_coordinate_matrix A T
    intro i j
    rw [hA.2.1 i j, hilbertSchmidtMatrixOperator_matrix]

end VacuumBellSeparation.Gaussian

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtTrace
public import LeanPool.VacuumBellSeparation.Gaussian.L2ProductInner

/-!
# Actual bounded analysis operators for square-summable Hilbert families

For a family with summable squared norms, the actual coefficient map
`x ↦ (⟨v_i,x⟩)_i` takes values in the full ℓ² space and is bounded by
the square root of the summed squared norms. Its adjoint sends coordinate
vectors to the original family. The resulting positive Gram operator
has finite positive trace equal to that sum.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal lp

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem norm_inner_sq_le (x y : E) : ‖inner ℂ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (inner ℂ x y)) (norm_inner_le_norm
    (𝕜 := ℂ) x y) 2

omit [CompleteSpace E] in
theorem summable_family_inner_norm_sq (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2)
    (x : E) : Summable fun i => ‖inner ℂ (v i) x‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => norm_inner_sq_le (v i) x)
    (hv.mul_right (‖x‖ ^ 2))

/-- Family analysis vector. -/
def familyAnalysisVector (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) (x : E) : ℓ²(ι, ℂ) :=
  ⟨fun i => inner ℂ (v i) x, by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa [Real.rpow_two] using summable_family_inner_norm_sq v hv x⟩

omit [CompleteSpace E] in
@[simp] theorem familyAnalysisVector_apply (v : ι → E)
    (hv : Summable fun i => ‖v i‖ ^ 2) (x : E) (i : ι) :
    familyAnalysisVector v hv x i = inner ℂ (v i) x := rfl

omit [CompleteSpace E] in
theorem norm_familyAnalysisVector_le (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2)
    (x : E) : ‖familyAnalysisVector v hv x‖ ≤ Real.sqrt (∑' i, ‖v i‖ ^ 2) * ‖x‖ := by
  have hs : 0 ≤ ∑' i, ‖v i‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hn : ‖familyAnalysisVector v hv x‖ ^ 2 = ∑' i, ‖inner ℂ (v i) x‖ ^ 2 := by
    simpa [Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) (familyAnalysisVector v hv x)).tsum_eq.symm
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [hn, mul_pow, Real.sq_sqrt hs, ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun i => norm_inner_sq_le (v i) x)
    (summable_family_inner_norm_sq v hv x) (hv.mul_right (‖x‖ ^ 2))

/-- Linear map for the family analysis linear. -/
def familyAnalysisLinear (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) :
    E →ₗ[ℂ] ℓ²(ι, ℂ) where
  toFun := familyAnalysisVector v hv
  map_add' := by intro x y; ext i; exact inner_add_right _ _ _
  map_smul' := by intro c x; ext i; exact inner_smul_right _ _ _

/-- Continuous linear map for the family analysis, of type `E →L[ℂ] ℓ²(ι, ℂ)`. -/
def familyAnalysis (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) : E →L[ℂ] ℓ²(ι, ℂ) :=
  (familyAnalysisLinear v hv).mkContinuous (Real.sqrt (∑' i, ‖v i‖ ^ 2))
    (norm_familyAnalysisVector_le v hv)

omit [CompleteSpace E] in
@[simp] theorem familyAnalysis_apply (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2)
    (x : E) (i : ι) : familyAnalysis v hv x i = inner ℂ (v i) x := rfl

/-- The Hilbert basis induced by the standard coordinate representation. -/
def coordinateHilbertBasis (ι : Type*) : HilbertBasis ι ℂ ℓ²(ι, ℂ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem coordinateHilbertBasis_inner (i : ι) (x : ℓ²(ι, ℂ)) :
    inner ℂ (coordinateHilbertBasis ι i) x = x i := by
  classical
  change inner ℂ (lp.single 2 i 1) x = x i
  simp [lp.inner_single_left]

theorem familyAnalysis_adjoint_basis (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) (i : ι) :
    (familyAnalysis v hv).adjoint (coordinateHilbertBasis ι i) = v i := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, coordinateHilbertBasis_inner, familyAnalysis_apply]

/-- Continuous linear map for the family gram operator, of type `ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)`. -/
def familyGramOperator (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) :
    ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) := (familyAnalysis v hv).comp (familyAnalysis v hv).adjoint

theorem familyGramOperator_nonneg (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) :
    0 ≤ familyGramOperator v hv :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint (familyAnalysis v hv))

theorem familyGramOperator_matrix (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) (i j : ι) :
    inner ℂ (coordinateHilbertBasis ι i) (familyGramOperator v hv (coordinateHilbertBasis ι j)) =
      inner ℂ (v i) (v j) := by
  rw [familyGramOperator, ContinuousLinearMap.comp_apply, familyAnalysis_adjoint_basis,
    coordinateHilbertBasis_inner, familyAnalysis_apply]

theorem positiveTrace_familyGramOperator (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) :
    positiveTrace (familyGramOperator v hv) = ENNReal.ofReal (∑' i, ‖v i‖ ^ 2) := by
  rw [positiveTrace_eq_tsum_diagonal (coordinateHilbertBasis ι) (familyGramOperator_nonneg v hv),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hv]
  apply tsum_congr
  intro i
  rw [familyGramOperator_matrix, ← RCLike.re_eq_complex_re, inner_self_eq_norm_sq]

theorem familyGramOperator_isPositiveTraceClass (v : ι → E)
    (hv : Summable fun i => ‖v i‖ ^ 2) : IsPositiveTraceClass (familyGramOperator v hv) := by
  refine ⟨familyGramOperator_nonneg v hv, ?_⟩
  rw [positiveTrace_familyGramOperator]
  exact ENNReal.ofReal_lt_top

end VacuumBellSeparation.Gaussian

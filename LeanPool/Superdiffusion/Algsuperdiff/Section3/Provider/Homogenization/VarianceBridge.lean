/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.NormalizedP4
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.NormalizedStructuralLaw
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.ArbitraryIntegrability
public import Mathlib.Analysis.Matrix.Order

/-!
# VarianceBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Law-generic and normalized-law deterministic block-matrix variance bridges

ABK26 Lemma `l.var.bounds` (display `e.var.a.star`) bounds the variance of the
normalized starred inverse coarse block matrix `𝐁^{1/2} 𝐀_{m,*}^{-1}(□_n)
𝐁^{1/2}` by twice the variance of its descendant average plus eight times the
second moment of the trace-type response average `⨍_z Σ_i 𝐉(z + □_k, 𝐁^{-1/2}
e_i, 𝐁^{1/2} e_i; a_m)`.

Under that reading the printed proof is exact with the literal factors `2` and
`8`, and it is the reading used by the pinned CoarseGraining formalization of
the same display (`Homogenization.Book.Ch05.Section56`,
`VarianceEstimateQuadratic`).

This file bridges CoarseGraining's arbitrary-normalizer form to the
manuscript's shape.  Two changes of variable are needed.

* *Reflection.*  CoarseGraining's fluctuating object is the coarse block matrix
  `𝐀(U)`, the manuscript's is the starred inverse `𝐀_*^{-1}(U) = 𝐑𝐀(U)𝐑`, which
  CoarseGraining renders as `blockReflect`.  Since `𝐑` is the symmetric
  involutive block swap, `𝐁^{1/2}(𝐑𝐀𝐑)𝐁^{1/2} = (𝐑𝐁^{1/2})ᵀ 𝐀 (𝐑𝐁^{1/2})`, so
  every CoarseGraining statement transports under `S ↦ 𝐑S`.  The same
  substitution turns CoarseGraining's response probes into the manuscript's,
  because `𝐉(U, 𝐑P, 𝐑Q) = 𝐉(U, Q, P)`.
* *General `𝐁`.*  CoarseGraining's integrated statement already carries
  arbitrary deterministic normalizers `S` and `T`; the manuscript instance is
  `S = 𝐁^{-1/2}`, `T = 𝐁^{1/2}`, implemented here through Mathlib's continuous
  functional calculus square root `CFC.sqrt`.

## Main results

* `starredFluctuationMatrix_eq_fullBlockFluctuationMatrixWithNormalizer`
* `blockJTraceAverageWithNormalizers_blockSwapMat_mul_ae`
* `starredFluctuationOperatorNormSq_le_two_descendantsAverage_add_eight_blockJTraceAverageSq_ae`
* `integral_starredFluctuationOperatorNormSq_le_two_descendantsAverage_add_eight_blockJTraceAverageSq_of_integrable`
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch05.Section56
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The block swap matrix `𝐑` -/

/-- The block swap matrix `𝐑` of ABK26, as a `2d × 2d` matrix. -/
def blockSwapMat (d : ℕ) : FullBlockMat d :=
  Matrix.of fun alpha beta => if Sum.swap alpha = beta then (1 : ℝ) else 0

theorem sum_swap_eq_iff (alpha beta : BlockCoord d) :
    Sum.swap alpha = beta ↔ alpha = Sum.swap beta := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

theorem blockSwapMat_transpose (d : ℕ) :
    Matrix.transpose (blockSwapMat d) = blockSwapMat d := by
  ext alpha beta
  have hiff : (Sum.swap beta = alpha) ↔ (Sum.swap alpha = beta) := by
    rw [sum_swap_eq_iff, eq_comm]
  simp only [Matrix.transpose_apply, blockSwapMat, Matrix.of_apply]
  exact if_congr hiff rfl rfl

theorem blockSwapMat_mul (M : FullBlockMat d) :
    blockSwapMat d * M = M.submatrix Sum.swap id := by
  ext alpha beta
  simp [blockSwapMat, Matrix.mul_apply, Matrix.submatrix_apply]

theorem mul_blockSwapMat (M : FullBlockMat d) :
    M * blockSwapMat d = M.submatrix id Sum.swap := by
  ext alpha beta
  simp only [Matrix.mul_apply, blockSwapMat, Matrix.of_apply, Matrix.submatrix_apply,
    id_eq]
  simp [sum_swap_eq_iff]

theorem blockSwapMat_mul_mul (M : FullBlockMat d) :
    blockSwapMat d * M * blockSwapMat d = M.submatrix Sum.swap Sum.swap := by
  rw [blockSwapMat_mul, mul_blockSwapMat, Matrix.submatrix_submatrix]
  rfl

/-- The manuscript's `𝐀_*^{-1} = 𝐑𝐀𝐑` in full `2d × 2d` form. -/
theorem toFullBlockMat_blockReflect (A : BlockMat d) :
    toFullBlockMat (blockReflect A) =
      (toFullBlockMat A).submatrix Sum.swap Sum.swap := by
  ext alpha beta
  cases alpha <;> cases beta <;> rfl

theorem fullBlockMatrixProbe_blockSwapMat_mul (X : FullBlockMat d)
    (alpha : BlockCoord d) :
    fullBlockMatrixProbe (blockSwapMat d * X) alpha =
      Prod.swap (fullBlockMatrixProbe X alpha) := by
  have hvec :
      Matrix.mulVec (blockSwapMat d * X) (Pi.single alpha 1) =
        fun gamma => Matrix.mulVec X (Pi.single alpha (1 : ℝ)) (Sum.swap gamma) := by
    rw [← Matrix.mulVec_mulVec]
    funext gamma
    simp [blockSwapMat, Matrix.mulVec, dotProduct]
  unfold fullBlockMatrixProbe
  rw [hvec]
  rfl

/-! ## The symmetric square root -/

/-- The continuous-functional-calculus square root of a positive semidefinite
real matrix is symmetric. -/
theorem transpose_cfcSqrt (B : FullBlockMat d) :
    Matrix.transpose (CFC.sqrt B) = CFC.sqrt B := by
  have hps : (CFC.sqrt B).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have h2 : Matrix.conjTranspose (CFC.sqrt B) = CFC.sqrt B := hps.isHermitian
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using h3

/-! ## The manuscript objects -/

/-- The starred inverse coarse block matrix `𝐀_*^{-1}(U;a) = 𝐑𝐀(U;a)𝐑`. -/
def starredInverseCoarseBlockMatrix (U : Set (Vec d)) (a : RegCoeffField d) :
    BlockMat d :=
  blockReflect (coarseBlockMatrix U a.toFun)

/-- The manuscript fluctuation matrix
`𝐁^{1/2}(𝐀_*^{-1}(U;a) - 𝐑𝐂𝐑)𝐁^{1/2}`, centered at the deterministic starred
inverse normalizer `𝐑𝐂𝐑` attached to the annealed block matrix `𝐂`. -/
def starredFluctuationMatrix (B : FullBlockMat d) (C : BlockMat d)
    (U : Set (Vec d)) (a : RegCoeffField d) : FullBlockMat d :=
  CFC.sqrt B *
      (toFullBlockMat (starredInverseCoarseBlockMatrix U a) -
        toFullBlockMat (blockReflect C)) *
    CFC.sqrt B

/-- Squared operator norm of the manuscript fluctuation matrix. -/
def starredFluctuationOperatorNormSq (B : FullBlockMat d) (C : BlockMat d)
    (U : Set (Vec d)) (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (starredFluctuationMatrix B C U a)‖ ^ (2 : ℕ)

/-- Descendant average of the manuscript fluctuation matrices. -/
def starredDescendantsAverageFluctuationMatrix (B : FullBlockMat d)
    (C : BlockMat d) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    FullBlockMat d :=
  descendantsAverageFullBlockMat Q j
    (fun R => starredFluctuationMatrix B C (cubeSet R) a)

/-- Squared operator norm of the descendant-average manuscript fluctuation. -/
def starredDescendantsAverageFluctuationOperatorNormSq (B : FullBlockMat d)
    (C : BlockMat d) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (starredDescendantsAverageFluctuationMatrix B C Q j a)‖ ^ (2 : ℕ)

/-- The manuscript trace-type response average
`⨍_z Σ_i 𝐉(z + □_k, 𝐁^{-1/2} e_i, 𝐁^{1/2} e_i; a)`. -/
def starredBlockJTraceAverage (B : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : ℝ :=
  blockJTraceAverageWithNormalizers (CFC.sqrt (B⁻¹)) (CFC.sqrt B) Q j a

/-- Square of the manuscript trace-type response average. -/
def starredBlockJTraceAverageSq (B : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : ℝ :=
  starredBlockJTraceAverage B Q j a ^ (2 : ℕ)

/-! ## Reflection transport of the fluctuation matrices -/

variable [NeZero d] {P : Ch04.RestrictionCoeffLaw d}

omit [NeZero d] in
theorem submatrix_swap_sub (X Y : FullBlockMat d) :
    (X - Y).submatrix Sum.swap Sum.swap =
      X.submatrix Sum.swap Sum.swap - Y.submatrix Sum.swap Sum.swap := by
  ext alpha beta
  simp

theorem starredFluctuationMatrix_eq_fullBlockFluctuationMatrixWithNormalizer
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ)
    (B : FullBlockMat d) (U : Set (Vec d)) (a : RegCoeffField d) :
    starredFluctuationMatrix B
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) U a =
      fullBlockFluctuationMatrixWithNormalizer hP hStruct center
        (blockSwapMat d * CFC.sqrt B) U a := by
  have hswap :
      blockSwapMat d *
          (toFullBlockMat (coarseBlockMatrix U a.toFun) -
            toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)) *
          blockSwapMat d =
        toFullBlockMat (starredInverseCoarseBlockMatrix U a) -
          toFullBlockMat
            (blockReflect (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)) := by
    rw [blockSwapMat_mul_mul, submatrix_swap_sub, starredInverseCoarseBlockMatrix,
      toFullBlockMat_blockReflect, toFullBlockMat_blockReflect]
  show _ =
    Matrix.transpose (blockSwapMat d * CFC.sqrt B) *
        (toFullBlockMat (coarseBlockMatrix U a.toFun) -
          toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)) *
      (blockSwapMat d * CFC.sqrt B)
  rw [Matrix.transpose_mul, blockSwapMat_transpose, transpose_cfcSqrt,
    starredFluctuationMatrix, ← hswap]
  simp only [Matrix.mul_assoc]

theorem starredDescendantsAverageFluctuationMatrix_eq_descendantsAverageFluctuationMatrixWithNormalizer
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ)
    (B : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    starredDescendantsAverageFluctuationMatrix B
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) Q j a =
      descendantsAverageFluctuationMatrixWithNormalizer hP hStruct center
        (blockSwapMat d * CFC.sqrt B) Q j a := by
  unfold starredDescendantsAverageFluctuationMatrix
    descendantsAverageFluctuationMatrixWithNormalizer
  congr 1
  funext R
  exact starredFluctuationMatrix_eq_fullBlockFluctuationMatrixWithNormalizer
    hP hStruct center B (cubeSet R) a

theorem starredFluctuationOperatorNormSq_eq
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ)
    (B : FullBlockMat d) (Q : TriadicCube d) (a : RegCoeffField d) :
    starredFluctuationOperatorNormSq B
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) (cubeSet Q) a =
      fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer hP hStruct center
        (blockSwapMat d * CFC.sqrt B) Q a := by
  unfold starredFluctuationOperatorNormSq
  rw [starredFluctuationMatrix_eq_fullBlockFluctuationMatrixWithNormalizer]
  rfl

theorem starredDescendantsAverageFluctuationOperatorNormSq_eq
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ)
    (B : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    starredDescendantsAverageFluctuationOperatorNormSq B
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) Q j a =
      descendantsAverageFluctuationOperatorNormSqWithNormalizer hP hStruct center
        (blockSwapMat d * CFC.sqrt B) Q j a := by
  unfold starredDescendantsAverageFluctuationOperatorNormSq
  rw [starredDescendantsAverageFluctuationMatrix_eq_descendantsAverageFluctuationMatrixWithNormalizer]
  rfl

/-! ## Reflection transport of the response probes -/

omit [NeZero d] in
theorem blockVecDot_swap_blockMatVecMul_swap (A : BlockMat d) (Z : BlockVec d) :
    blockVecDot (Prod.swap Z) (blockMatVecMul A (Prod.swap Z)) =
      blockVecDot Z (blockMatVecMul (blockReflect A) Z) := by
  rw [blockVecDot_blockMatVecMul_blockReflect]
  rfl

omit [NeZero d] in
theorem blockVecDot_swap_swap (X Y : BlockVec d) :
    blockVecDot (Prod.swap X) (Prod.swap Y) = blockVecDot Y X := by
  have hcomm : ∀ p q : Vec d, vecDot p q = vecDot q p := by
    intro p q
    simp [vecDot, mul_comm]
  simp [blockVecDot, hcomm X.2 Y.2, hcomm X.1 Y.1, add_comm]

omit [NeZero d] in
/-- `𝐉(U, 𝐑P, 𝐑Q) = 𝐉(U, Q, P)`, at the level of the trace budget. -/
theorem fullBlockJTraceBudgetWithNormalizers_blockSwapMat_mul
    (X Y : FullBlockMat d) (A : BlockMat d) :
    fullBlockJTraceBudgetWithNormalizers (blockSwapMat d * X) (blockSwapMat d * Y)
        A =
      fullBlockJTraceBudgetWithNormalizers Y X A := by
  unfold fullBlockJTraceBudgetWithNormalizers
  refine Finset.sum_congr rfl ?_
  intro alpha _halpha
  rw [fullBlockMatrixProbe_blockSwapMat_mul, fullBlockMatrixProbe_blockSwapMat_mul,
    blockVecDot_swap_blockMatVecMul_swap, blockVecDot_swap_blockMatVecMul_swap,
    blockReflect_blockReflect, blockVecDot_swap_swap]
  ring

/-- The sum of block responses over the coordinate probes is the trace budget. -/
theorem sum_blockJObservableCubeSetBlockVec_eq_fullBlockJTraceBudget
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (R : TriadicCube d) (S T : FullBlockMat d) :
    (∑ alpha : BlockCoord d,
        blockJObservableCubeSetBlockVec R (fullBlockMatrixProbe S alpha)
          (fullBlockMatrixProbe T alpha) a) =
      fullBlockJTraceBudgetWithNormalizers S T
        (coarseBlockMatrix (cubeSet R) a.toFun) := by
  classical
  have hcoarse :
      coarseBlockMatrix (cubeSet R) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) :=
    Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      ha R
  rw [hcoarse, ← sum_doubledResponseJ_fullBlockNormalizers_eq_traceBudget]
  refine Finset.sum_congr rfl ?_
  intro alpha _halpha
  exact
    (doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
      ha R (fullBlockMatrixProbe S alpha) (fullBlockMatrixProbe T alpha)).symm

theorem blockJTraceAverageWithNormalizers_blockSwapMat_mul
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (X Y : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    blockJTraceAverageWithNormalizers (blockSwapMat d * X) (blockSwapMat d * Y)
        Q j a =
      blockJTraceAverageWithNormalizers Y X Q j a := by
  classical
  unfold blockJTraceAverageWithNormalizers
  congr 1
  funext R
  rw [sum_blockJObservableCubeSetBlockVec_eq_fullBlockJTraceBudget ha R,
    sum_blockJObservableCubeSetBlockVec_eq_fullBlockJTraceBudget ha R,
    fullBlockJTraceBudgetWithNormalizers_blockSwapMat_mul]

theorem blockJTraceAverageWithNormalizers_blockSwapMat_mul_ae
    (hP : Ch04.RestrictionLawCarrier P) (X Y : FullBlockMat d)
    (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
        blockJTraceAverageWithNormalizers (blockSwapMat d * X) (blockSwapMat d * Y)
          Q j a) =ᵐ[P]
      fun a : RegCoeffField d =>
        blockJTraceAverageWithNormalizers Y X Q j a := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  exact blockJTraceAverageWithNormalizers_blockSwapMat_mul ha X Y Q j

/-! ## The law-generic starred variance estimate -/

/-- A conditional law-generic algebraic helper underlying the reflected
variance estimate; this declaration makes no source-node claim. -/
private theorem starredFluctuationOperatorNormSq_le_two_descendantsAverage_add_eight_blockJTraceAverageSq_ae
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (B : FullBlockMat d) (hB : B.PosDef)
    (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      starredFluctuationOperatorNormSq B
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
        (cubeSet Q) a) ≤ᵐ[P]
    fun a : RegCoeffField d =>
      2 * starredDescendantsAverageFluctuationOperatorNormSq B
          (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) Q j a +
        8 * starredBlockJTraceAverageSq B Q j a := by
  have hinv : CFC.sqrt (B⁻¹) = (CFC.sqrt B)⁻¹ :=
    (Matrix.PosSemidef.inv_sqrt hB.posSemidef).symm
  have hmain :=
    fullBlockFluctuationNormSq_le_two_childMean_add_eight_JTraceAverageSq_ae
      hP hStruct center (blockSwapMat d * CFC.sqrt B)
      (blockSwapMat d * (CFC.sqrt B)⁻¹) Q j
  filter_upwards
    [hmain,
      blockJTraceAverageWithNormalizers_blockSwapMat_mul_ae hP
        (CFC.sqrt B) ((CFC.sqrt B)⁻¹) Q j] with a hbound hJ
  have hJeq :
      starredBlockJTraceAverageSq B Q j a =
        blockJTraceAverageSqWithNormalizers
          (blockSwapMat d * CFC.sqrt B)
          (blockSwapMat d * (CFC.sqrt B)⁻¹) Q j a := by
    unfold blockJTraceAverageSqWithNormalizers starredBlockJTraceAverageSq
      starredBlockJTraceAverage
    rw [hJ, hinv]
  rw [starredFluctuationOperatorNormSq_eq hP hStruct center B Q a,
    starredDescendantsAverageFluctuationOperatorNormSq_eq
      hP hStruct center B Q j a, hJeq]
  exact hbound

/-- The arbitrary-scale integrated starred variance inequality when the two
right-hand observables are explicitly integrable.  This separates the
algebraic variance estimate from the source-specific moment argument that
supplies integrability below relative scale zero. -/
theorem integral_starredFluctuationOperatorNormSq_le_two_descendantsAverage_add_eight_blockJTraceAverageSq_of_integrable
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (B : FullBlockMat d) (hB : B.PosDef)
    (Q : TriadicCube d) (j : ℕ)
    (hdesc : Integrable
      (starredDescendantsAverageFluctuationOperatorNormSq B
        (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) Q j) P)
    (hJ : Integrable (starredBlockJTraceAverageSq B Q j) P) :
    ∫ a, starredFluctuationOperatorNormSq B
          (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
          (cubeSet Q) a ∂P ≤
      2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B
              (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
              Q j a ∂P +
        8 * ∫ a, starredBlockJTraceAverageSq B Q j a ∂P := by
  let F : RegCoeffField d → ℝ :=
    starredDescendantsAverageFluctuationOperatorNormSq B
      (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) Q j
  let J : RegCoeffField d → ℝ := starredBlockJTraceAverageSq B Q j
  have hFInt : Integrable F P := by simpa [F] using hdesc
  have hJInt : Integrable J P := by simpa [J] using hJ
  have hRhsInt : Integrable (fun a : RegCoeffField d => 2 * F a + 8 * J a) P :=
    (hFInt.const_mul (2 : ℝ)).add (hJInt.const_mul (8 : ℝ))
  have hpoint :
      (fun a : RegCoeffField d =>
        starredFluctuationOperatorNormSq B
          (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
          (cubeSet Q) a) ≤ᵐ[P]
      fun a : RegCoeffField d => 2 * F a + 8 * J a := by
    simpa [F, J] using
      starredFluctuationOperatorNormSq_le_two_descendantsAverage_add_eight_blockJTraceAverageSq_ae
        hP hStruct center B hB Q j
  have hmono :
      ∫ a, starredFluctuationOperatorNormSq B
            (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
            (cubeSet Q) a ∂P ≤
        ∫ a, 2 * F a + 8 * J a ∂P := by
    refine integral_mono_of_nonneg ?_ hRhsInt hpoint
    filter_upwards with a
    exact pow_nonneg (norm_nonneg _) 2
  calc
    ∫ a, starredFluctuationOperatorNormSq B
          (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
          (cubeSet Q) a ∂P ≤
        ∫ a, 2 * F a + 8 * J a ∂P := hmono
    _ = ∫ a, 2 * F a ∂P + ∫ a, 8 * J a ∂P := by
      rw [integral_add (hFInt.const_mul (2 : ℝ)) (hJInt.const_mul (8 : ℝ))]
    _ = 2 * ∫ a, F a ∂P + 8 * ∫ a, J a ∂P := by
      rw [integral_const_mul, integral_const_mul]
    _ = 2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B
              (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
              Q j a ∂P +
          8 * ∫ a, starredBlockJTraceAverageSq B Q j a ∂P := by
      rfl

end

end Algsuperdiff.Section3.Provider.Homogenization

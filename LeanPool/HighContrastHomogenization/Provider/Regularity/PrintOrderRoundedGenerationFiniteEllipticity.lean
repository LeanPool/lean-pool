/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBase
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationHarmonicComparison

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationFiniteEllipticity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Analytic bounds for the rounded finite energy recurrence

This file derives the Poincare and coarse-Caccioppoli inputs used in the
printed finite energy-row recurrence directly from the genuinely rounded
comparison matrix and its fixed near-unity ellipticity window.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal Matrix MatrixOrder

noncomputable section

open FiniteLipschitzCoreInternal

namespace RoundedFiniteEnergyInternal

private theorem skewPart_eq_zero_of_isSymm
    {d : ℕ} {A : Mat d} (hA : A.IsSymm) :
    skewPart A = 0 := by
  ext i j
  have hij : A j i = A i j := (Matrix.IsSymm.ext_iff.mp hA) i j
  change (A i j - A j i) / 2 = 0
  rw [hij]
  ring

private theorem blockMatVecMul_constantBlockMatrix_of_isSymm
    {d : ℕ} {A : Mat d} (hA : A.IsSymm) (P : BlockVec d) :
    blockMatVecMul (Book.Ch02.constantBlockMatrix A) P =
      (matVecMul A P.1, matVecMul A⁻¹ P.2) := by
  rcases P with ⟨p, r⟩
  have hsymm : symmPart A = A := symmPart_eq_of_isSymm hA
  have hskew : skewPart A = 0 := skewPart_eq_zero_of_isSymm hA
  apply Prod.ext
  · simp [Book.Ch02.constantBlockMatrix, blockMatVecMul, hsymm, hskew,
      matTranspose]
    ext i
    simp [matVecMul]
  · simp [Book.Ch02.constantBlockMatrix, blockMatVecMul, hsymm, hskew,
      matTranspose]
    ext i
    simp [matVecMul]

private theorem vecDot_matVecMul_le_of_matrix_le
    {d : ℕ} {A B : Mat d} (h : A ≤ B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hdiff.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  change x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x
  simp only [star_trivial] at hx
  linarith only [hx]

private theorem vecNormSq_single_one {d : ℕ} (i : Fin d) :
    vecNormSq (Pi.single i 1 : Vec d) = 1 := by
  rw [vecNormSq, vecDot]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hji hji
    simp [Pi.single_eq_of_ne hji]
  · simp

private theorem roundedReference_coordinate_quadratic_bounds
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    (99 / 100 : ℝ) ≤
        vecDot (Pi.single i 1 : Vec d)
          (matVecMul (geom.referenceMatrix abar hS) (Pi.single i 1)) ∧
      vecDot (Pi.single i 1 : Vec d)
          (matVecMul (geom.referenceMatrix abar hS) (Pi.single i 1)) ≤
        (101 / 100 : ℝ) := by
  let e : Vec d := Pi.single i 1
  let A : Mat d := geom.referenceMatrix abar hS
  have hlower := geom.reference_lower abar hS
  have hupper := geom.reference_upper abar hS
  have hlow := vecDot_matVecMul_le_of_matrix_le hlower e
  have hupp := vecDot_matVecMul_le_of_matrix_le hupper e
  have he : vecNormSq e = 1 := by
    simpa only [e] using vecNormSq_single_one i
  have hscalar (c : ℝ) :
      vecDot e (matVecMul (c • (1 : Mat d)) e) = c * vecNormSq e := by
    have hone : matVecMul (1 : Mat d) e = e := by
      funext j
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [smul_matVecMul, hone, vecDot_smul_right]
    rfl
  change (99 / 100 : ℝ) ≤ vecDot e (matVecMul A e) ∧
    vecDot e (matVecMul A e) ≤ (101 / 100 : ℝ)
  constructor
  · simpa only [hscalar, he, mul_one, A, e] using! hlow
  · simpa only [hscalar, he, mul_one, A, e] using! hupp

private theorem doubledResponseJ_le_normalizedBlockResponseMax_of_quadratic_one
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (P : BlockVec d)
    (hquad : blockVecDot P
      (blockMatVecMul
        (Book.Ch02.constantBlockMatrix (geom.referenceMatrix abar hS)) P) = 1) :
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) P
        (blockMatVecMul
          (Book.Ch02.constantBlockMatrix (geom.referenceMatrix abar hS)) P) ≤
      Book.Ch02.normalizedBlockResponseMax Q a
        (geom.referenceMatrix abar hS) := by
  have hmem :=
    Book.Ch02.normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
      Q a (geom.reference_elliptic abar hS) P hquad
  unfold Book.Ch02.normalizedBlockResponseMax
  exact le_csSup
    (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := a) (Q := Q) (R := Q) (k := Q.scale)
      (geom.referenceMatrix abar hS)
      (by simp [descendantsAtScale_self])) hmem

private theorem coarseB_diagonal_le_roundedResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i ≤
      2 * (101 / 100 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
  let U := Book.Ch02.cubeDomain Q
  let aQ := a.coeffOn Q
  let A : Mat d := geom.referenceMatrix abar hS
  let e : Vec d := Pi.single i 1
  let r : ℝ := vecDot e (matVecMul A e)
  let c : ℝ := (Real.sqrt r)⁻¹
  let P₀ : BlockVec d := (e, 0)
  let P : BlockVec d := c • P₀
  let B := Book.Ch02.coarseBlockMatrix U aQ
  let BStar := Book.Ch02.coarseStarredBlockMatrixInv U aQ
  let M := Book.Ch02.normalizedBlockResponseMax Q a A
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (geom.reference_posDef abar hS).isHermitian
  obtain ⟨hrlow, hrupp⟩ :=
    roundedReference_coordinate_quadratic_bounds (geom := geom) abar hS i
  have hrpos : 0 < r := by dsimp only [r, e, A]; linarith only [hrlow]
  have hCP₀ : blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀ =
      (matVecMul A e, 0) := by
    rw [blockMatVecMul_constantBlockMatrix_of_isSymm hAsymm]
    simp only [P₀, matVecMul_zero]
  have hquad₀ : blockVecDot P₀
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀) = r := by
    rw [hCP₀]
    simp only [P₀, blockVecDot, vecDot_zero_left, add_zero, r, e]
  have hquad : blockVecDot P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) = 1 := by
    rw [show P = c • P₀ from rfl, blockMatVecMul_smul,
      blockVecDot_smul_left, blockVecDot_smul_right, hquad₀]
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hJ : Book.Ch02.doubledResponseJ U aQ P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) ≤ M := by
    simpa only [U, aQ, A, M] using
      doubledResponseJ_le_normalizedBlockResponseMax_of_quadratic_one
        Q a abar hS P (by simpa only [A] using hquad)
  let Qv := blockMatVecMul (Book.Ch02.constantBlockMatrix A) P
  have hQquad_nonneg : 0 ≤ blockVecDot Qv (blockMatVecMul BStar Qv) := by
    by_cases hQv : Qv = 0
    · rw [hQv]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · exact ((Book.Ch02.blockCoarseMatrixTheory U aQ).starred_inverse_posDef
        Qv hQv).le
  have hpair : blockVecDot P Qv = 1 := by
    simpa only [Qv] using hquad
  have hsplit :=
    (Book.Ch02.blockCoarseMatrixTheory U aQ).doubled_response_splitting P Qv
  have hscaled : blockVecDot P (blockMatVecMul B P) ≤ 2 * (M + 1) := by
    rw [hsplit, hpair] at hJ
    nlinarith only [hJ, hQquad_nonneg]
  have hx : blockVecDot P (blockMatVecMul B P) =
      c * c * Book.Ch02.bCoarse U aQ i i := by
    have hbase : blockVecDot P₀ (blockMatVecMul B P₀) =
        Book.Ch02.bCoarse U aQ i i := by
      dsimp only [P₀, B]
      simp only [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left,
        add_zero]
      dsimp only [e]
      rw [vecDot_single_left, matVecMul_single]
      rfl
    rw [show P = c • P₀ from rfl, blockMatVecMul_smul,
      blockVecDot_smul_left, blockVecDot_smul_right, hbase]
    ring
  rw [hx] at hscaled
  have hc : r * (c * c) = 1 := by
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hMnonneg : 0 ≤ M := by
    exact Book.Ch02.normalizedBlockResponseMax_nonneg Q a A
  calc
    Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i =
        r * (c * c * Book.Ch02.bCoarse U aQ i i) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ r * (2 * (M + 1)) := mul_le_mul_of_nonneg_left hscaled hrpos.le
    _ ≤ 2 * (101 / 100 : ℝ) * (M + 1) := by
      have hrupp' : r ≤ (101 / 100 : ℝ) := by
        simpa only [r, e, A] using hrupp
      nlinarith only [hrupp', hMnonneg]
    _ = 2 * (101 / 100 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := rfl

private theorem roundedReference_inverse_coordinate_quadratic_bounds
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    (101 / 100 : ℝ)⁻¹ ≤
        vecDot (Pi.single i 1 : Vec d)
          (matVecMul (geom.referenceMatrix abar hS)⁻¹ (Pi.single i 1)) ∧
      vecDot (Pi.single i 1 : Vec d)
          (matVecMul (geom.referenceMatrix abar hS)⁻¹ (Pi.single i 1)) ≤
        (99 / 100 : ℝ)⁻¹ := by
  let e : Vec d := Pi.single i 1
  let A : Mat d := geom.referenceMatrix abar hS
  have hAell := geom.reference_elliptic abar hS
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (geom.reference_posDef abar hS).isHermitian
  have he : vecNormSq e = 1 := by
    simpa only [e] using vecNormSq_single_one i
  have hlower := hAell.2.2.2 e
  have hupper := symmPart_inv_upperBound_of_isEllipticMatrix hAell e
  have hsymm : symmPart A = A := symmPart_eq_of_isSymm hAsymm
  change vecDot e (matVecMul (symmPart A)⁻¹ e) ≤
    (99 / 100 : ℝ)⁻¹ * vecNormSq e at hupper
  rw [hsymm, he, mul_one] at hupper
  change (101 / 100 : ℝ)⁻¹ ≤ vecDot e (matVecMul A⁻¹ e) ∧
    vecDot e (matVecMul A⁻¹ e) ≤ (99 / 100 : ℝ)⁻¹
  constructor
  · simpa only [he, mul_one, A, e] using! hlower
  · simpa only [A, e] using hupper

private theorem coarseSigmaStarInv_diagonal_le_roundedResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    Book.Ch02.sigmaStarInvCoarse
        (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i ≤
      2 * (100 / 99 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
  let U := Book.Ch02.cubeDomain Q
  let aQ := a.coeffOn Q
  let A : Mat d := geom.referenceMatrix abar hS
  let e : Vec d := Pi.single i 1
  let r : ℝ := vecDot e (matVecMul A⁻¹ e)
  let c : ℝ := (Real.sqrt r)⁻¹
  let P₀ : BlockVec d := (matVecMul A⁻¹ e, 0)
  let P : BlockVec d := c • P₀
  let Q₀ : BlockVec d := (e, 0)
  let B := Book.Ch02.coarseBlockMatrix U aQ
  let BStar := Book.Ch02.coarseStarredBlockMatrixInv U aQ
  let M := Book.Ch02.normalizedBlockResponseMax Q a A
  have hAell := geom.reference_elliptic abar hS
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (geom.reference_posDef abar hS).isHermitian
  have hAdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hAell
  obtain ⟨hrlow, hrupp⟩ :=
    roundedReference_inverse_coordinate_quadratic_bounds
      (geom := geom) abar hS i
  have hrpos : 0 < r := by dsimp only [r, e, A]; linarith only [hrlow]
  have hAAinvE : matVecMul A (matVecMul A⁻¹ e) = e := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv A hAdet, matVecMul_one]
  have hCP₀ : blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀ = Q₀ := by
    rw [blockMatVecMul_constantBlockMatrix_of_isSymm hAsymm]
    simp only [P₀, Q₀, matVecMul_zero, hAAinvE]
  have hquad₀ : blockVecDot P₀
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀) = r := by
    rw [hCP₀]
    simp only [P₀, Q₀, blockVecDot, vecDot_zero_left, add_zero,
      vecDot_comm (matVecMul A⁻¹ e) e, r]
  have hquad : blockVecDot P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) = 1 := by
    rw [show P = c • P₀ from rfl, blockMatVecMul_smul,
      blockVecDot_smul_left, blockVecDot_smul_right, hquad₀]
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hJ : Book.Ch02.doubledResponseJ U aQ P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) ≤ M := by
    simpa only [U, aQ, A, M] using
      doubledResponseJ_le_normalizedBlockResponseMax_of_quadratic_one
        Q a abar hS P (by simpa only [A] using hquad)
  let Qv := blockMatVecMul (Book.Ch02.constantBlockMatrix A) P
  have hPquad_nonneg : 0 ≤ blockVecDot P (blockMatVecMul B P) := by
    by_cases hPzero : P = 0
    · rw [hPzero]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · exact ((Book.Ch02.blockCoarseMatrixTheory U aQ).block_matrix_posDef
        P hPzero).le
  have hpair : blockVecDot P Qv = 1 := by
    simpa only [Qv] using hquad
  have hsplit :=
    (Book.Ch02.blockCoarseMatrixTheory U aQ).doubled_response_splitting P Qv
  have hscaled : blockVecDot Qv (blockMatVecMul BStar Qv) ≤ 2 * (M + 1) := by
    rw [hsplit, hpair] at hJ
    nlinarith only [hJ, hPquad_nonneg]
  have hQv : Qv = c • Q₀ := by
    dsimp only [Qv, P]
    rw [blockMatVecMul_smul, hCP₀]
  have hx : blockVecDot Qv (blockMatVecMul BStar Qv) =
      c * c * Book.Ch02.sigmaStarInvCoarse U aQ i i := by
    have hbase : blockVecDot Q₀ (blockMatVecMul BStar Q₀) =
        Book.Ch02.sigmaStarInvCoarse U aQ i i := by
      dsimp only [Q₀, BStar]
      simp only [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left,
        add_zero]
      dsimp only [e]
      rw [vecDot_single_left, matVecMul_single]
      rfl
    rw [hQv, blockMatVecMul_smul, blockVecDot_smul_left,
      blockVecDot_smul_right, hbase]
    ring
  rw [hx] at hscaled
  have hc : r * (c * c) = 1 := by
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hMnonneg : 0 ≤ M := by
    exact Book.Ch02.normalizedBlockResponseMax_nonneg Q a A
  calc
    Book.Ch02.sigmaStarInvCoarse
          (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i =
        r * (c * c * Book.Ch02.sigmaStarInvCoarse U aQ i i) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ r * (2 * (M + 1)) := mul_le_mul_of_nonneg_left hscaled hrpos.le
    _ ≤ 2 * (100 / 99 : ℝ) * (M + 1) := by
      have hrupp' : r ≤ (100 / 99 : ℝ) := calc
        r ≤ (99 / 100 : ℝ)⁻¹ := by
          simpa only [r, e, A] using hrupp
        _ = (100 / 99 : ℝ) := by norm_num
      nlinarith only [hrupp', hMnonneg]
    _ = 2 * (100 / 99 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := rfl

/-- The one-cube upper coarse ellipticity norm is controlled directly by the
rounded-reference response. -/
theorem coarseBMatrixNorm_le_printOrderRoundedReferenceResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    Book.Ch02.coarseBMatrixNorm Q a ≤
      (d : ℝ) * (2 * (101 / 100 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
  let K : ℝ := 2 * (101 / 100 : ℝ) *
    (Book.Ch02.normalizedBlockResponseMax Q a
      (geom.referenceMatrix abar hS) + 1)
  have htrace : Matrix.trace
      (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) ≤
        ∑ _i : Fin d, K := by
    exact Finset.sum_le_sum fun i _hi ↦ by
      simpa only [K] using! coarseB_diagonal_le_roundedResponse Q a abar hS i
  calc
    Book.Ch02.coarseBMatrixNorm Q a ≤ Matrix.trace
        (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) := by
      exact Book.Ch02.matrixNorm_le_trace_of_posSemidef _
        (Book.Ch02.bCoarse_posSemidef _ _)
    _ ≤ ∑ _i : Fin d, K := htrace
    _ = (d : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (d : ℝ) * (2 * (101 / 100 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
      dsimp only [K]
      ring

/-- The one-cube lower coarse ellipticity inverse norm is controlled directly
by the rounded-reference response. -/
theorem coarseSigmaStarInvMatrixNorm_le_printOrderRoundedReferenceResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    Book.Ch02.coarseSigmaStarInvMatrixNorm Q a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
  let K : ℝ := 2 * (100 / 99 : ℝ) *
    (Book.Ch02.normalizedBlockResponseMax Q a
      (geom.referenceMatrix abar hS) + 1)
  have htrace : Matrix.trace
      (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) ≤
        ∑ _i : Fin d, K := by
    exact Finset.sum_le_sum fun i _hi ↦ by
      simpa only [K] using!
        coarseSigmaStarInv_diagonal_le_roundedResponse Q a abar hS i
  calc
    Book.Ch02.coarseSigmaStarInvMatrixNorm Q a ≤ Matrix.trace
        (Book.Ch02.sigmaStarInvCoarse
          (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) := by
      exact Book.Ch02.matrixNorm_le_trace_of_posSemidef _
        (Book.Ch02.sigmaStarInvCoarse_posDef _ _).posSemidef
    _ ≤ ∑ _i : Fin d, K := htrace
    _ = (d : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
      dsimp only [K]
      ring

private theorem coarseBMatrixNorm_le_commonRoundedResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    Book.Ch02.coarseBMatrixNorm Q a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (geom.referenceMatrix abar hS) + 1) := by
  let M := Book.Ch02.normalizedBlockResponseMax Q a
    (geom.referenceMatrix abar hS)
  have hraw := coarseBMatrixNorm_le_printOrderRoundedReferenceResponse
    (geom := geom) Q a abar hS
  have hM : 0 ≤ M :=
    Book.Ch02.normalizedBlockResponseMax_nonneg Q a
      (geom.referenceMatrix abar hS)
  have hcoeff :
      (d : ℝ) * (2 * (101 / 100 : ℝ)) ≤
        (d : ℝ) * (2 * (100 / 99 : ℝ)) := by
    have hd : (0 : ℝ) ≤ d := by positivity
    nlinarith only [hd]
  exact hraw.trans
    (mul_le_mul_of_nonneg_right hcoeff (by linarith only [hM]))

private theorem maxDescendantBMatrixNormAtScale_le_commonRoundedResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : Book.Ch02.TriadicCoeffFamily d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    Book.Ch02.maxDescendantBMatrixNormAtScale Q k a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
          (geom.referenceMatrix abar hS) + 1) := by
  let C : ℝ := (d : ℝ) * (2 * (100 / 99 : ℝ)) *
    (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
      (geom.referenceMatrix abar hS) + 1)
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Book.Ch02.coarseBMatrixNorm R a ≤ C := by
    intro R hR
    have hRone := coarseBMatrixNorm_le_commonRoundedResponse
      (geom := geom) R a abar hS
    have hMle :
        Book.Ch02.normalizedBlockResponseMax R a
            (geom.referenceMatrix abar hS) ≤
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
            (geom.referenceMatrix abar hS) :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a (geom.referenceMatrix abar hS) hR
    have hcoef : 0 ≤ (d : ℝ) * (2 * (100 / 99 : ℝ)) := by positivity
    dsimp only [C]
    exact hRone.trans
      (mul_le_mul_of_nonneg_left (by linarith only [hMle]) hcoef)
  simpa only [Book.Ch02.maxDescendantBMatrixNormAtScale] using
    Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hD hpoint

private theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_commonRoundedResponse
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : Book.Ch02.TriadicCoeffFamily d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
          (geom.referenceMatrix abar hS) + 1) := by
  let C : ℝ := (d : ℝ) * (2 * (100 / 99 : ℝ)) *
    (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
      (geom.referenceMatrix abar hS) + 1)
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Book.Ch02.coarseSigmaStarInvMatrixNorm R a ≤ C := by
    intro R hR
    have hRone :=
      coarseSigmaStarInvMatrixNorm_le_printOrderRoundedReferenceResponse
        (geom := geom) R a abar hS
    have hMle :
        Book.Ch02.normalizedBlockResponseMax R a
            (geom.referenceMatrix abar hS) ≤
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
            (geom.referenceMatrix abar hS) :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a (geom.referenceMatrix abar hS) hR
    have hcoef : 0 ≤ (d : ℝ) * (2 * (100 / 99 : ℝ)) := by positivity
    dsimp only [C]
    exact hRone.trans
      (mul_le_mul_of_nonneg_left (by linarith only [hMle]) hcoef)
  simpa only [Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale] using
    Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hD hpoint

/-- The finite `q = 2` upper ellipticity row is controlled directly by the
homogenization error normalized against the rounded reference matrix. -/
theorem LambdaSq_finite_two_le_printOrderRoundedReferenceError
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) {s : ℝ} (hs : 0 < s) :
    Book.Ch02.LambdaSq Q s (.finite 2) a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        ((Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (geom.referenceMatrix abar hS)) ^ 2 + 1) := by
  let B : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  let M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (n : ℤ)) a (geom.referenceMatrix abar hS)
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 2 n
  let C : ℝ := (d : ℝ) * (2 * (100 / 99 : ℝ))
  have hLambda_eq : Book.Ch02.LambdaSq Q s (.finite 2) a =
      ∑' n : ℕ, w n * B n := by
    have h := Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 2 a
      (by norm_num : (0 : ℝ) < 2) (by nlinarith only [hs] : 0 ≤ s * (2 : ℝ))
    simpa [w, B, Real.rpow_one] using h
  have hsumB : Summable (fun n : ℕ => w n * B n) := by
    have h := Book.Ch02.summable_B_series_pointwiseCoeffField Q a hs
      (by norm_num : (0 : ℝ) < 2)
    simpa [w, B, Real.rpow_one] using h
  have hsumR : Summable (fun n : ℕ => w n * (M n + 1)) := by
    have hsumM : Summable (fun n : ℕ => w n * M n) := by
      simpa [w, M] using
        Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
          Q a (geom.referenceMatrix abar hS) hs
    have hsumW : Summable w := by
      simpa [w, Book.Ch02.geometricWeight_eq_old] using
        HCPolySupport.summable_geometricWeight (s := s) (q := 2)
          (by nlinarith only [hs] : 0 < s * (2 : ℝ))
    have hsumAdd := hsumM.add hsumW
    simpa [mul_add, w, M] using hsumAdd
  have hterm : ∀ n : ℕ, w n * B n ≤ C * (w n * (M n + 1)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hscale := maxDescendantBMatrixNormAtScale_le_commonRoundedResponse
      (geom := geom) (Q := Q) (k := Q.scale - (n : ℤ))
      (sub_le_self Q.scale hn)
      a abar hS
    have hw : 0 ≤ w n := by
      simpa [w, Book.Ch02.geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n
          (by nlinarith only [hs] : 0 ≤ s * (2 : ℝ))
    dsimp only [C, B, M, w] at hscale ⊢
    calc
      Book.Ch02.geometricWeight s 2 n *
          Book.Ch02.maxDescendantBMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a ≤
        Book.Ch02.geometricWeight s 2 n *
          ((d : ℝ) * (2 * (100 / 99 : ℝ)) *
            (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
              (Q.scale - (n : ℤ)) a (geom.referenceMatrix abar hS) + 1)) :=
        mul_le_mul_of_nonneg_left hscale hw
      _ = (d : ℝ) * (2 * (100 / 99 : ℝ)) *
          (Book.Ch02.geometricWeight s 2 n *
            (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
              (Q.scale - (n : ℤ)) a (geom.referenceMatrix abar hS) + 1)) := by
        ring
  calc
    Book.Ch02.LambdaSq Q s (.finite 2) a = ∑' n : ℕ, w n * B n := hLambda_eq
    _ ≤ ∑' n : ℕ, C * (w n * (M n + 1)) :=
      hsumB.tsum_le_tsum hterm (hsumR.mul_left C)
    _ = C * (∑' n : ℕ, w n * (M n + 1)) := hsumR.tsum_mul_left C
    _ = C * ((Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (geom.referenceMatrix abar hS)) ^ 2 + 1) := by
      rw [Book.Ch02.tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
        Q a (geom.referenceMatrix abar hS) hs]

/-- The inverse finite `q = 2` lower ellipticity row is controlled directly by
the homogenization error normalized against the rounded reference matrix. -/
theorem lambdaSq_finite_two_inv_le_printOrderRoundedReferenceError
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) {s : ℝ} (hs : 0 < s) :
    (Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹ ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        ((Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (geom.referenceMatrix abar hS)) ^ 2 + 1) := by
  let S : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (n : ℤ)) a
  let M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (n : ℤ)) a (geom.referenceMatrix abar hS)
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 2 n
  let C : ℝ := (d : ℝ) * (2 * (100 / 99 : ℝ))
  have hlambda_eq : (Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹ =
      ∑' n : ℕ, w n * S n := by
    have h := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 2 a
      (by norm_num : (0 : ℝ) < 2) (by nlinarith only [hs] : 0 ≤ s * (2 : ℝ))
    simpa [w, S, Real.rpow_one, Real.rpow_neg_one] using h
  have hsumS : Summable (fun n : ℕ => w n * S n) := by
    have h := Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a hs
      (by norm_num : (0 : ℝ) < 2)
    simpa [w, S, Real.rpow_one] using h
  have hsumR : Summable (fun n : ℕ => w n * (M n + 1)) := by
    have hsumM : Summable (fun n : ℕ => w n * M n) := by
      simpa [w, M] using
        Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
          Q a (geom.referenceMatrix abar hS) hs
    have hsumW : Summable w := by
      simpa [w, Book.Ch02.geometricWeight_eq_old] using
        HCPolySupport.summable_geometricWeight (s := s) (q := 2)
          (by nlinarith only [hs] : 0 < s * (2 : ℝ))
    have hsumAdd := hsumM.add hsumW
    simpa [mul_add, w, M] using hsumAdd
  have hterm : ∀ n : ℕ, w n * S n ≤ C * (w n * (M n + 1)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hscale :=
      maxDescendantSigmaStarInvMatrixNormAtScale_le_commonRoundedResponse
        (geom := geom) (Q := Q) (k := Q.scale - (n : ℤ))
        (sub_le_self Q.scale hn)
        a abar hS
    have hw : 0 ≤ w n := by
      simpa [w, Book.Ch02.geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) n
          (by nlinarith only [hs] : 0 ≤ s * (2 : ℝ))
    dsimp only [C, S, M, w] at hscale ⊢
    calc
      Book.Ch02.geometricWeight s 2 n *
          Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a ≤
        Book.Ch02.geometricWeight s 2 n *
          ((d : ℝ) * (2 * (100 / 99 : ℝ)) *
            (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
              (Q.scale - (n : ℤ)) a (geom.referenceMatrix abar hS) + 1)) :=
        mul_le_mul_of_nonneg_left hscale hw
      _ = (d : ℝ) * (2 * (100 / 99 : ℝ)) *
          (Book.Ch02.geometricWeight s 2 n *
            (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
              (Q.scale - (n : ℤ)) a (geom.referenceMatrix abar hS) + 1)) := by
        ring
  calc
    (Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹ = ∑' n : ℕ, w n * S n := hlambda_eq
    _ ≤ ∑' n : ℕ, C * (w n * (M n + 1)) :=
      hsumS.tsum_le_tsum hterm (hsumR.mul_left C)
    _ = C * (∑' n : ℕ, w n * (M n + 1)) := hsumR.tsum_mul_left C
    _ = C * ((Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (geom.referenceMatrix abar hS)) ^ 2 + 1) := by
      rw [Book.Ch02.tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
        Q a (geom.referenceMatrix abar hS) hs]

/-- A rounded weak-error bound by one gives a dimension-only finite `q = 2`
ellipticity window. -/
theorem roundedGenerationWeakError_le_one_finiteTwoEllipticity
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRounded : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d))
    {s : ℝ} (hs : 0 < s) {k : ℤ}
    (herror : geom.spatialWeakError a abar hS s k ≤ 1) :
    Book.Ch02.LambdaSq (originCube d k) s (.finite 2) aRounded ≤
        5 * (d : ℝ) ∧
      (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) aRounded)⁻¹ ≤
        5 * (d : ℝ) := by
  let E := geom.spatialWeakError a abar hS s k
  have hE : 0 ≤ E := geom.spatialWeakError_nonneg a abar hS s k
  have hE_sq : E ^ 2 + 1 ≤ 2 := by
    nlinarith only [hE, herror]
  have hupper := LambdaSq_finite_two_le_printOrderRoundedReferenceError
    (geom := geom) (originCube d k) aRounded abar hS hs
  have hlower := lambdaSq_finite_two_inv_le_printOrderRoundedReferenceError
    (geom := geom) (originCube d k) aRounded abar hS hs
  rw [homogenizationErrorOnCube_eq_roundedGenerationSpatialWeakError
    a abar hS aRounded hRounded s k] at hupper hlower
  have hnumeric : (d : ℝ) * (2 * (100 / 99 : ℝ)) * 2 ≤ 5 * (d : ℝ) := by
    have hd : (0 : ℝ) ≤ d := by positivity
    nlinarith only [hd]
  constructor
  · calc
      Book.Ch02.LambdaSq (originCube d k) s (.finite 2) aRounded ≤
          (d : ℝ) * (2 * (100 / 99 : ℝ)) * (E ^ 2 + 1) := hupper
      _ ≤ (d : ℝ) * (2 * (100 / 99 : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hE_sq (by positivity)
      _ ≤ 5 * (d : ℝ) := hnumeric
  · calc
      (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) aRounded)⁻¹ ≤
          (d : ℝ) * (2 * (100 / 99 : ℝ)) * (E ^ 2 + 1) := hlower
      _ ≤ (d : ℝ) * (2 * (100 / 99 : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hE_sq (by positivity)
      _ ≤ 5 * (d : ℝ) := hnumeric

end RoundedFiniteEnergyInternal

end

end HighContrast
end HCPolySupport

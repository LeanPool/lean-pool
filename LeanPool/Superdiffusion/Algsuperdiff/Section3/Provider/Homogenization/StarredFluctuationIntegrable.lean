/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.FullBlockNormBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-!
# StarredFluctuationIntegrable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Integrability of the starred fluctuation observable at the coefficient cutoff law

The Step-3 corridor observable

`starredFluctuationOperatorNormSq 𝐁(σ_L) 𝐂 (cubeSet □_n) a
   = ‖𝐁^{1/2}(𝐀_*^{-1}(□_n;a) - 𝐑𝐂𝐑)𝐁^{1/2}‖²`

(`starredFluctuationOperatorNormSq` in `VarianceBridge.lean`) is integrable at
the genuine coefficient cutoff law `Cutoff.coefficientCutoffLaw M L`, for every
deterministic centering `𝐂` and every cube.  That is the item recorded as `M7`;
on delivery it discharges the `Integrable` binder carried by the two proved
publics
`coefficientCutoffLaw_sq_sigmaBar_mul_starInverseVarianceAtScale_add_le` and
`exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound` of
`VarianceClosure.lean`, whose unconditional restatements are the last two
declarations of this module.

This module makes no source-node status claim; every declaration below is a
local `Provider` helper.

## The two halves

**(i) The measurable half.**  `starredFluctuationOperatorNormSq B ·` is a
*continuous* function of the full coarse block matrix `toFullBlockMat
(coarseBlockMatrix U a.toFun)`: reflection is the entry permutation
`Matrix.submatrix Sum.swap Sum.swap` (`toFullBlockMat_blockReflect`), the
centering is a constant, and the two-sided `CFC.sqrt B` conjugation and the squared
Euclidean operator norm are continuous.  Composing with
`Ch04.RestrictionLawCarrier.aemeasurable_coarseFullBlockMatrix_cubeSet` gives
a.e. measurability at any restriction law, in particular at
`Cutoff.coefficientCutoffLaw M L`, a carrier by
`Cutoff.coefficientCutoffLaw_lawCarrier`.

**(ii) The gauge instance and the domination.**  `cutoffComparatorNormalizer M
L` is *definitionally* `Ch02.constantFullBlockMatrix
(Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))`
(`cutoffComparatorNormalizer` in `VarianceCarrierSeam.lean`), whose `CFC.sqrt` is
the block diagonal `diag(√σ 𝟙, (√σ)^{-1} 𝟙)`.

`σ |Δ_lowerRight| + |Δ_lowerLeft| + |Δ_upperRight| + σ^{-1} |Δ_upperLeft|`,

the asymmetric weighting of the proved carrier bridges.  Each block is then
bounded *unconditionally*, at `a = Cutoff.coefficientCutoff M.nu L ω`:

* `|𝐀_lowerRight| ≤ 4dν^{-1}` -- the deterministic descendant envelope,
  `matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale`
  (`VarianceClosure.lean`) at depth `0`;
* `|𝐀_upperLeft| ≤ 4dν^{-1}E(ω)²` with `E :=
  Cutoff.coefficientCutoffCubeEllipticityUpper` -- the unconditional envelope
  `Cutoff.maxDescendantBMatrixNormCoeffFieldAtScale_le_cutoffEnvelope` (the
  ambient form of `Cutoff.maxDescendantBMatrixNormAtScale_le_cutoffEnvelope`),
  read on the `coarseBlockMatrix` carrier through the public Chapter 5 sup
  identity;
* `|𝐀_lowerLeft|, |𝐀_upperRight| ≤ 4dν^{-1}E(ω)` -- the sharp positive
  semidefinite off-diagonal bound
  (`matrixOperatorNorm_upperRight_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef`
  /
  `matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef`
  in `VarianceClosure.lean`) with the symmetry and positivity discharges of
  `coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField` and
  `coarseBlockMatrix_cubeSet_blockPosDef_of_aelocallyUniformlyEllipticField`;
* the four *centering* blocks are constants in `ω` -- the annealed block matrix
  is deterministic -- so their operator norms enter only as fixed additive
  constants.  No `σ` sandwich is used; the proved `SigmaBarAnchor` premises
  are therefore **not** bound here.

The result is a pointwise bound by `(a₀ + a₁E + a₂E²)²`, a degree-four
polynomial in `E` with constant coefficients, and every power of `E` is
integrable at the sample law
(`Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow`,
`Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow`, via
`Cutoff.integrable_cutoffLocalControl_pow` and
`Cutoff.coefficientCutoffCubeEllipticityUpper_le_majorant`). The transfer
between the sample carrier and the `RegCoeffField` carrier is
`Cutoff.coefficientCutoffLaw_eq_map` (`Cutoff/Law.lean`) with
`integrable_map_measure`, the pattern proved in
`Cutoff.integrable_LambdaSqCoeffField_pow_cutoffLaw`. -/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.HighContrast.EntryScale
open Algsuperdiff.Section3
open scoped MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Elementary norm facts -/

omit [NeZero d] in
/-- The Euclidean operator norm of a difference is below the sum of the two
operator norms. -/
private theorem matrixOperatorNorm_sub_le (X Y : Mat d) :
    Ch02.matrixOperatorNorm (X - Y) ≤
      Ch02.matrixOperatorNorm X + Ch02.matrixOperatorNorm Y := by
  have h :=
    Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub (X - Y) X
  have hrw : X - Y - X = -Y := by abel
  have hneg : Ch02.matrixOperatorNorm (-Y) = Ch02.matrixOperatorNorm Y := by
    change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (-Y)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Y‖
    rw [map_neg, norm_neg]
  rw [hrw, hneg] at h
  exact h

omit [NeZero d] in
/-- The squared Euclidean operator norm is continuous on `FullBlockMat d`. -/
private theorem continuous_norm_toEuclideanCLM_sq :
    Continuous fun X : FullBlockMat d =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ^ (2 : ℕ) := by
  let T : FullBlockMat d →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) :=
    { toFun := fun X => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X
      map_add' := fun A B =>
        map_add (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) A B
      map_smul' := fun r A =>
        map_smul (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) r A }
  exact (continuous_norm.comp T.continuous_of_finiteDimensional).pow 2

/-! ## The measurable half -/

omit [NeZero d] in
/-- The starred fluctuation matrix, written as a two-sided conjugation of an
affine function of the full coarse block matrix.  Reflection is the entry
permutation `Matrix.submatrix Sum.swap Sum.swap`. -/
theorem starredFluctuationMatrix_eq_conj_submatrix (B : FullBlockMat d)
    (C : BlockMat d) (U : Set (Vec d)) (a : RegCoeffField d) :
    starredFluctuationMatrix B C U a =
      CFC.sqrt B *
          ((toFullBlockMat (coarseBlockMatrix U a.toFun)).submatrix Sum.swap Sum.swap -
            toFullBlockMat (blockReflect C)) *
        CFC.sqrt B := by
  rw [starredFluctuationMatrix, starredInverseCoarseBlockMatrix,
    toFullBlockMat_blockReflect]

omit [NeZero d] in
/-- **The measurable half of `M7`.**  At every restriction law carrier the
starred fluctuation observable is a.e. measurable, for every normalizer, every
deterministic centering and every cube. -/
theorem aemeasurable_starredFluctuationOperatorNormSq
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (B : FullBlockMat d) (C : BlockMat d) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        starredFluctuationOperatorNormSq B C (cubeSet Q) a) P := by
  have hM := hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  have hg : Measurable fun X : FullBlockMat d =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (CFC.sqrt B *
              (X.submatrix Sum.swap Sum.swap - toFullBlockMat (blockReflect C)) *
            CFC.sqrt B)‖ ^ (2 : ℕ) := by
    refine (continuous_norm_toEuclideanCLM_sq.comp ?_).measurable
    exact
      (continuous_const.matrix_mul
          ((continuous_id.matrix_submatrix Sum.swap Sum.swap).sub
            continuous_const)).matrix_mul continuous_const
  refine (hg.comp_aemeasurable hM).congr ?_
  filter_upwards with a
  rw [Function.comp_apply, starredFluctuationOperatorNormSq,
    starredFluctuationMatrix_eq_conj_submatrix]

omit [NeZero d] in
/-- The measurable half at the genuine coefficient cutoff law. -/
theorem aemeasurable_starredFluctuationOperatorNormSq_coefficientCutoffLaw
    (M : ABKModel d) (L : ℤ) (B : FullBlockMat d) (C : BlockMat d)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        starredFluctuationOperatorNormSq B C (cubeSet Q) a)
      (Cutoff.coefficientCutoffLaw M L) :=
  aemeasurable_starredFluctuationOperatorNormSq
    (Cutoff.coefficientCutoffLaw_lawCarrier M L) B C Q

/-! ## The gauge instance -/

omit [NeZero d] in
/-- `scalarFullBlockSqrtDiag b b` in the `Sum.elim` normal form used by the proved
gauge bound. -/
private theorem scalarFullBlockSqrtDiag_eq_sum_elim (b : ℝ) :
    Ch05.Section56.scalarFullBlockSqrtDiag (d := d) b b =
      Sum.elim (fun _ : Fin d => Real.sqrt b) (fun _ : Fin d => (Real.sqrt b)⁻¹) := by
  funext alpha
  cases alpha <;> rfl

omit [NeZero d] in
/-- The continuous functional calculus square root of the comparator normalizer is
the two-scalar block gauge `diag(√σ 𝟙, (√σ)^{-1} 𝟙)`. -/
private theorem cfcSqrt_cutoffComparatorNormalizer_eq_diagonal (M : ABKModel d)
    (L : ℤ) :
    CFC.sqrt (cutoffComparatorNormalizer M L) =
      Matrix.diagonal
        (Sum.elim (fun _ : Fin d => Real.sqrt (Annealed.sigmaBar M L : ℝ))
          (fun _ : Fin d => (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹)) := by
  have hB : cutoffComparatorNormalizer M L =
      Ch02.constantFullBlockMatrix
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) := rfl
  have h : CFC.sqrt (cutoffComparatorNormalizer M L) =
      Matrix.diagonal
        (Ch05.Section56.scalarFullBlockSqrtDiag (d := d)
          (Annealed.sigmaBar M L : ℝ) (Annealed.sigmaBar M L : ℝ)) := by
    rw [hB]
    change Ch02.constantFullBlockMatrixSqrt
      (scalarMatrix (d := d) (Annealed.sigmaBar M L : ℝ)) = _
    exact Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
      (Annealed.sigmaBar M L).property
  rw [h, scalarFullBlockSqrtDiag_eq_sum_elim]

omit [NeZero d] in
/-- **The gauge instance at the comparator normalizer.**  Conjugating by
`𝐁(σ_L)^{1/2}` weights the four block operator norms of the reflected
difference by `σ_L, 1, 1, σ_L^{-1}`; since `blockReflect` swaps the diagonal
blocks, the weights land on `lowerRight, lowerLeft, upperRight, upperLeft` in
that order -- the asymmetric weighting of the proved carrier bridges
(`sq_mul_sq_matrixOperatorNorm_lowerRight_sub_le_starredFluctuationOperatorNormSq`
and `sq_matrixOperatorNorm_lowerLeft_sub_le_starredFluctuationOperatorNormSq` in
`VarianceClosure.lean`). -/
theorem norm_toEuclideanCLM_starredFluctuationMatrix_cutoffComparatorNormalizer_le
    (M : ABKModel d) (L : ℤ) (C : BlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (starredFluctuationMatrix (cutoffComparatorNormalizer M L) C U a)‖ ≤
      (Annealed.sigmaBar M L : ℝ) *
            Ch02.matrixOperatorNorm
              ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) +
          Ch02.matrixOperatorNorm
            ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) +
          Ch02.matrixOperatorNorm
            ((coarseBlockMatrix U a.toFun).upperRight - C.upperRight) +
        (Annealed.sigmaBar M L : ℝ)⁻¹ *
          Ch02.matrixOperatorNorm
            ((coarseBlockMatrix U a.toFun).upperLeft - C.upperLeft) := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hs0 : (0 : ℝ) < Real.sqrt (Annealed.sigmaBar M L : ℝ) := Real.sqrt_pos.mpr hsigma
  set Y : FullBlockMat d :=
    (toFullBlockMat (coarseBlockMatrix U a.toFun)).submatrix Sum.swap Sum.swap -
      toFullBlockMat (blockReflect C) with hY
  have hUL : (ofFullBlockMat Y).upperLeft =
      (coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight := by
    ext i j
    simp [hY, ofFullBlockMat, toFullBlockMat, blockReflect]
  have hUR : (ofFullBlockMat Y).upperRight =
      (coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft := by
    ext i j
    simp [hY, ofFullBlockMat, toFullBlockMat, blockReflect]
  have hLL : (ofFullBlockMat Y).lowerLeft =
      (coarseBlockMatrix U a.toFun).upperRight - C.upperRight := by
    ext i j
    simp [hY, ofFullBlockMat, toFullBlockMat, blockReflect]
  have hLR : (ofFullBlockMat Y).lowerRight =
      (coarseBlockMatrix U a.toFun).upperLeft - C.upperLeft := by
    ext i j
    simp [hY, ofFullBlockMat, toFullBlockMat, blockReflect]
  have hrepr : starredFluctuationMatrix (cutoffComparatorNormalizer M L) C U a =
      Matrix.diagonal
          (Sum.elim (fun _ : Fin d => Real.sqrt (Annealed.sigmaBar M L : ℝ))
            (fun _ : Fin d => (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹)) * Y *
        Matrix.diagonal
          (Sum.elim (fun _ : Fin d => Real.sqrt (Annealed.sigmaBar M L : ℝ))
            (fun _ : Fin d => (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹)) := by
    rw [starredFluctuationMatrix_eq_conj_submatrix,
      cfcSqrt_cutoffComparatorNormalizer_eq_diagonal, hY]
  have hgauge :=
    norm_toEuclideanCLM_diagonal_mul_mul_diagonal_le
      (Real.sqrt (Annealed.sigmaBar M L : ℝ))
      (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹ Y
  have hs2 : Real.sqrt (Annealed.sigmaBar M L : ℝ) ^ (2 : ℕ) =
      (Annealed.sigmaBar M L : ℝ) := Real.sq_sqrt hsigma.le
  have ht2 : (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹ ^ (2 : ℕ) =
      (Annealed.sigmaBar M L : ℝ)⁻¹ := by
    rw [inv_pow, hs2]
  have hst : |Real.sqrt (Annealed.sigmaBar M L : ℝ) *
      (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹| = 1 := by
    rw [mul_inv_cancel₀ hs0.ne', abs_one]
  rw [hUL, hUR, hLL, hLR, hs2, ht2, hst] at hgauge
  rw [hrepr]
  linarith

/-! ## The unconditional upper-left descendant envelope -/

/-- **The unconditional upper-left envelope.**  The Euclidean operator norm of
the upper-left coarse block -- the manuscript's `b` -- of *every* descendant of
`Q` at depth `j` is below `4dν^{-1}E(ω)²`, with
`E := Cutoff.coefficientCutoffCubeEllipticityUpper` the realised upper
ellipticity constant of the root cube.  Unlike the good-event, geometrically
weighted upper-left bound of `VarianceClosure.lean` this bound is depth-uniform
and carries no event; the price is the random envelope in place of `2σ_L`. -/
theorem matrixOperatorNorm_coarseBlockMatrix_upperLeft_le_cutoffEnvelope
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (j : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ))) :
    Ch02.matrixOperatorNorm
        (coarseBlockMatrix (cubeSet R)
          (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft ≤
      4 * (d : ℝ) * M.nu⁻¹ *
        Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ 2 := by
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hsup :=
    Ch05.Section52.maxDescendantBMatrixNorm_eq_sup_upperLeft_of_uniformEllipticity
      (Cutoff.coefficientCutoff_aelocallyUniformlyElliptic M L omega) Q hk
  have hmem :
      Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R)
            (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft ≤
        (descendantsAtScale Q (Q.scale - (j : ℤ))).sup'
          (descendantsAtScale_nonempty Q hk)
          (fun S => Ch02.matrixNorm
            (coarseBlockMatrix (cubeSet S)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft) :=
    Finset.le_sup'
      (fun S => Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet S)
          (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft) hR
  rw [← hsup] at hmem
  exact hmem.trans
    (Cutoff.maxDescendantBMatrixNormCoeffFieldAtScale_le_cutoffEnvelope M L omega Q j)

omit [NeZero d] in
/-- The realised upper ellipticity constant of a cell is nonnegative. -/
private theorem coefficientCutoffCubeEllipticityUpper_nonneg (M : ABKModel d)
    (m : ℤ) (omega : Cutoff.CutoffSample d) (R : TriadicCube d) :
    0 ≤ Cutoff.coefficientCutoffCubeEllipticityUpper M m omega R := by
  unfold Cutoff.coefficientCutoffCubeEllipticityUpper
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  positivity

/-! ## The samplewise polynomial domination -/

omit [NeZero d] in
/-- The scalar assembly of the samplewise envelope: the gauge bound, the four
triangle inequalities and the four block envelopes compose to a quadratic
polynomial in the ellipticity envelope `Ec`, with the deterministic centering
norms `c··` entering only the constant term. -/
private theorem le_quadratic_envelope_of_block_bounds
    {sg K Ec X dLR dLL dUR dUL nLR nLL nUR nUL cLR cLL cUR cUL : ℝ} (hsg : 0 < sg)
    (hX : X ≤ sg * dLR + dLL + dUR + sg⁻¹ * dUL)
    (hsubLR : dLR ≤ nLR + cLR) (hsubLL : dLL ≤ nLL + cLL)
    (hsubUR : dUR ≤ nUR + cUR) (hsubUL : dUL ≤ nUL + cUL)
    (hLR : nLR ≤ K) (hLL : nLL ≤ K * Ec) (hUR : nUR ≤ K * Ec)
    (hUL : nUL ≤ K * Ec ^ (2 : ℕ)) :
    X ≤ (sg * (K + cLR) + cLL + cUR + sg⁻¹ * cUL) + 2 * K * Ec ^ (1 : ℕ) +
      sg⁻¹ * K * Ec ^ (2 : ℕ) := by
  have hsginv : (0 : ℝ) < sg⁻¹ := inv_pos.mpr hsg
  have h1 : sg * dLR ≤ sg * (K + cLR) :=
    mul_le_mul_of_nonneg_left (by linarith) hsg.le
  have h2 : sg⁻¹ * dUL ≤ sg⁻¹ * (K * Ec ^ (2 : ℕ) + cUL) :=
    mul_le_mul_of_nonneg_left (by linarith) hsginv.le
  have h3 : sg⁻¹ * (K * Ec ^ (2 : ℕ) + cUL) =
      sg⁻¹ * K * Ec ^ (2 : ℕ) + sg⁻¹ * cUL := by ring
  have h4 : Ec ^ (1 : ℕ) = Ec := pow_one Ec
  linarith

/-- **The samplewise envelope.**  On every cutoff sample the starred
fluctuation norm at the comparator normalizer, on the origin cube of the
centering scale, is below an explicit quadratic polynomial in the realised
upper ellipticity constant of that cube, with coefficients built from `σ_L`,
`4dν^{-1}` and the four block norms of the deterministic centering. -/
theorem norm_toEuclideanCLM_starredFluctuationMatrix_coefficientCutoff_le
    (M : ABKModel d) (L : ℤ) (C : BlockMat d) (Q : TriadicCube d)
    (omega : Cutoff.CutoffSample d) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (starredFluctuationMatrix (cutoffComparatorNormalizer M L) C (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu L omega))‖ ≤
      ((Annealed.sigmaBar M L : ℝ) * (4 * (d : ℝ) * M.nu⁻¹ +
              Ch02.matrixOperatorNorm C.lowerRight) +
            Ch02.matrixOperatorNorm C.lowerLeft +
            Ch02.matrixOperatorNorm C.upperRight +
            (Annealed.sigmaBar M L : ℝ)⁻¹ * Ch02.matrixOperatorNorm C.upperLeft) +
        2 * (4 * (d : ℝ) * M.nu⁻¹) *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (1 : ℕ) +
          (Annealed.sigmaBar M L : ℝ)⁻¹ * (4 * (d : ℝ) * M.nu⁻¹) *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (2 : ℕ) := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hK0 : (0 : ℝ) ≤ 4 * (d : ℝ) * M.nu⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le d))
      (inv_nonneg.mpr M.nu_pos.le)
  have hE0 : (0 : ℝ) ≤ Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q :=
    coefficientCutoffCubeEllipticityUpper_nonneg M L omega Q
  have hself : Q ∈ descendantsAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) := by
    simp [descendantsAtScale_self]
  have hlocal : Ch04.AELocallyUniformlyEllipticField
      (Cutoff.coefficientCutoff M.nu L omega) :=
    Cutoff.coefficientCutoff_aelocallyUniformlyElliptic M L omega
  have hblockLR :=
    matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
      M L omega Q 0 hself
  have hblockUL :=
    matrixOperatorNorm_coarseBlockMatrix_upperLeft_le_cutoffEnvelope M L omega Q 0 hself
  have hgeom :
      Real.sqrt
          (Ch02.matrixOperatorNorm
              (coarseBlockMatrix (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft *
            Ch02.matrixOperatorNorm
              (coarseBlockMatrix (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight) ≤
        4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q := by
    have hprod :
        Ch02.matrixOperatorNorm
            (coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft *
          Ch02.matrixOperatorNorm
            (coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight ≤
        (4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q) ^ (2 : ℕ) := by
      have := mul_le_mul hblockUL hblockLR (Ch02.matrixOperatorNorm_nonneg _)
        (mul_nonneg hK0 (pow_nonneg hE0 2))
      calc _ ≤ 4 * (d : ℝ) * M.nu⁻¹ *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (2 : ℕ) *
              (4 * (d : ℝ) * M.nu⁻¹) := this
        _ = (4 * (d : ℝ) * M.nu⁻¹ *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q) ^ (2 : ℕ) := by ring
    calc _ ≤ Real.sqrt ((4 * (d : ℝ) * M.nu⁻¹ *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q) ^ (2 : ℕ)) :=
          Real.sqrt_le_sqrt hprod
      _ = 4 * (d : ℝ) * M.nu⁻¹ *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q :=
          Real.sqrt_sq (mul_nonneg hK0 hE0)
  have hblockLL :
      Ch02.matrixOperatorNorm
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft ≤
        4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q :=
    (matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef
      (coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField Q hlocal)
      (coarseBlockMatrix_cubeSet_blockPosDef_of_uniformEllipticity Q
        hlocal)).trans hgeom
  have hblockUR :
      Ch02.matrixOperatorNorm
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu L omega).toFun).upperRight ≤
        4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q :=
    (matrixOperatorNorm_upperRight_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef
      (coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField Q hlocal)
      (coarseBlockMatrix_cubeSet_blockPosDef_of_uniformEllipticity Q
        hlocal)).trans hgeom
  have hsubLR := matrixOperatorNorm_sub_le
    (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight C.lowerRight
  have hsubLL := matrixOperatorNorm_sub_le
    (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft C.lowerLeft
  have hsubUR := matrixOperatorNorm_sub_le
    (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu L omega).toFun).upperRight C.upperRight
  have hsubUL := matrixOperatorNorm_sub_le
    (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft C.upperLeft
  have hgauge :=
    norm_toEuclideanCLM_starredFluctuationMatrix_cutoffComparatorNormalizer_le M L C
      (cubeSet Q) (Cutoff.coefficientCutoff M.nu L omega)
  exact le_quadratic_envelope_of_block_bounds hsigma hgauge hsubLR hsubLL hsubUR hsubUL
    hblockLR hblockLL hblockUR hblockUL

/-! ## Integrability at the coefficient cutoff law -/

/-- **`M7`.**  The Step-3 corridor observable is integrable at the genuine
coefficient cutoff law, for every deterministic centering and every cube. -/
theorem integrable_starredFluctuationOperatorNormSq_coefficientCutoffLaw
    (M : ABKModel d) (L : ℤ) (C : BlockMat d) (Q : TriadicCube d) :
    Integrable
      (fun a : RegCoeffField d =>
        starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L) C
          (cubeSet Q) a)
      (Cutoff.coefficientCutoffLaw M L) := by
  set a0 : ℝ :=
    (Annealed.sigmaBar M L : ℝ) * (4 * (d : ℝ) * M.nu⁻¹ +
          Ch02.matrixOperatorNorm C.lowerRight) +
        Ch02.matrixOperatorNorm C.lowerLeft +
        Ch02.matrixOperatorNorm C.upperRight +
      (Annealed.sigmaBar M L : ℝ)⁻¹ * Ch02.matrixOperatorNorm C.upperLeft with ha0
  set a1 : ℝ := 2 * (4 * (d : ℝ) * M.nu⁻¹) with ha1
  set a2 : ℝ := (Annealed.sigmaBar M L : ℝ)⁻¹ * (4 * (d : ℝ) * M.nu⁻¹) with ha2
  have hmeas :=
    aemeasurable_starredFluctuationOperatorNormSq_coefficientCutoffLaw M L
      (cutoffComparatorNormalizer M L) C Q
  have hpow : ∀ p : ℕ, Integrable
      (fun omega : Cutoff.CutoffSample d =>
        Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ p)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    fun p => Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L Q p
  have hdom : Integrable
      (fun omega : Cutoff.CutoffSample d =>
        a0 ^ (2 : ℕ) +
              2 * a0 * a1 *
                Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (1 : ℕ) +
            (a1 ^ (2 : ℕ) + 2 * a0 * a2) *
              Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (2 : ℕ) +
          2 * a1 * a2 *
              Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (3 : ℕ) +
            a2 ^ (2 : ℕ) *
              Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (4 : ℕ))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((((integrable_const (a0 ^ (2 : ℕ))).add ((hpow 1).const_mul (2 * a0 * a1))).add
      ((hpow 2).const_mul (a1 ^ (2 : ℕ) + 2 * a0 * a2))).add
        ((hpow 3).const_mul (2 * a1 * a2))).add ((hpow 4).const_mul (a2 ^ (2 : ℕ)))
  rw [Cutoff.coefficientCutoffLaw_eq_map M L] at hmeas ⊢
  refine (integrable_map_measure hmeas.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable).mpr ?_
  refine Integrable.mono' hdom
    ((hmeas.comp_aemeasurable
      (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable)).aestronglyMeasurable ?_
  filter_upwards with omega
  have hchain :=
    norm_toEuclideanCLM_starredFluctuationMatrix_coefficientCutoff_le M L C Q omega
  have hsq :=
    pow_le_pow_left₀ (norm_nonneg
      (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        (starredFluctuationMatrix (cutoffComparatorNormalizer M L) C (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu L omega)))) hchain 2
  have hexpand :
      (a0 +
          a1 * Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (1 : ℕ) +
          a2 * Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (2 : ℕ)) ^
          (2 : ℕ) =
        a0 ^ (2 : ℕ) +
              2 * a0 * a1 *
                Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (1 : ℕ) +
            (a1 ^ (2 : ℕ) + 2 * a0 * a2) *
              Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (2 : ℕ) +
          2 * a1 * a2 *
              Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (3 : ℕ) +
            a2 ^ (2 : ℕ) *
              Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ (4 : ℕ) := by
    ring
  have hnonneg : (0 : ℝ) ≤
      starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L) C (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega) := by
    rw [starredFluctuationOperatorNormSq]
    positivity
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    starredFluctuationOperatorNormSq, ← hexpand]
  exact hsq.trans_eq (by rw [ha0, ha1, ha2])

/-! ## The unconditional restatements -/

/-- **`(e.var.bound.astar.withS)` at the genuine cutoff law, unconditionally.**
This is
`exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound`
(`VarianceClosure.lean`) with its `Integrable` binder discharged; every other
binder and the conclusion are byte-identical.  The caveats recorded there are
unchanged: the amplitude is the lane's two-term `δ`, strictly larger than the
printed `δ₁`, so this partially supports and does not realize the printed
display. -/
theorem exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound' :
    ∃ Chom Cvar : ℝ, 64 ≤ Chom ∧
      2 * ((Cutoff.cutoffRelativeNormalizationShift d : ℝ) + 1) ≤ Chom ∧
      1 ≤ Cvar ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (IndependentSums.gammaSigma 2) (IndependentSums.gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∀ L : ℤ,
            (L : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon| →
            ∀ n : ℤ, n ∈ Set.Icc L m →
              (Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n +
                  starInverseKappaVarianceAtScale M L n ≤
                2 * Cvar *
                    ((E : ℝ) ^ 2 * M.gamma +
                      Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
                    (((E : ℝ) ^ 2 * M.gamma +
                        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
                      Real.rpow 3 (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))) := by
  obtain ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, hbound⟩ :=
    exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound (d := d)
  refine ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, ?_⟩
  intro M m E hLower epsilon hepsilon hgamma L hseparation n hn
  exact hbound M m E hLower epsilon hepsilon hgamma L hseparation n hn
    (integrable_starredFluctuationOperatorNormSq_coefficientCutoffLaw M L
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
      (originCube d n))

end

end Algsuperdiff.Section3.Provider.Homogenization

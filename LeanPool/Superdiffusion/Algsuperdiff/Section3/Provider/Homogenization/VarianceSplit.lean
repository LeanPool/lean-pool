/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineGoodEvent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineIntegerDownscale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.RealStationaryTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.KappaZero
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# VarianceSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The variance split of Step 1 of the corrected combine proposition

ABK26.  Step 1 of `p.combine.under.S` leaves the two deterministic field blocks
of the good-event display
(`CombineGoodEvent.exists_cutoffGoodEvent_cutoffResponseJ_le_preVarianceSplitDisplay`)

* `σ_L · ⨍_{R} |σ_*^{-1}(□_m)(q + κ(□_m)p) - σ_*^{-1}(R)(q + κ(R)p)|²`  and
* `σ_L · |σ_*^{-1}(□_m)(q + κ(□_m)p) - p|²`,

and converts them into the two variance blocks of `e.initial.JL.bound`.  This
module carries the deterministic and the annealed halves of that conversion, on
the proved carriers.

## What is proved

1. *The block reading of the comparison vector*.  The `Provider.Besov.Carriers`
   vector `coarseScaleSeparation` is the lower half of the coarse block matrix
   `𝐀(Q;a)` at the block load `(-p, q)`, minus `p`.  The sign is forced by
   `𝐀_{lowerLeft} = -(σ_*^{-1}κ)` (`Ch02.blockMatrixOfCoarseMatrices`).  This
   gives an ellipticity-witness-free carrier `coarseBlockScaleSeparation`,
   which is what can be integrated against a coefficient law.
2. *The two-term load split*.  With the Euclidean matrix operator norm -- the
   manuscript's `|A|` of -- the coarse-matrix variation is at most
   `2|q|²|Δσ_*^{-1}|² + 2|p|²|Δ(σ_*^{-1}κ)|²`.
3. *The three-term deterministic-centering split* and the printed constant `6 =
   2·3`.
4. *The annealed half*.  (The carrier law bundles no integrability and Lean's
   Bochner `∫` of a non-integrable integrand is `0`, so the identity "centering
   = mean" is honest exactly where the entries are integrable — the same scope
   in which the manuscript's `var[·]` is defined.) Real-translation
   stationarity collapses the printed `⨍_{z ∈ 3ⁿℤᵈ ∩ □_m}` onto the single
   origin cube at scale `n`, and the result is the printed display
   `6|q|²(var[σ_*^{-1}(□_m)] + var[σ_*^{-1}(□_n)] + |σ_*^{-1}(□_m) -
   σ_*^{-1}(□_n)|²)
    + 6|p|²(var[σ_*^{-1}κ(□_m)] + var[σ_*^{-1}κ(□_n)])`. The `κ` mean gap is
      *absent* rather than dropped: `e.annealed.khom.zero` (proved as
      `Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero`)
      makes both annealed lower-left blocks vanish.
5. *The `e.pq.normed` weights*.  At the manuscript loads `p = σ_L^{-1/2}e`, `q
   = σ_L^{1/2}e` with `|e|² = 1` one has `|q|² = σ_L` and `|p|² = σ_L^{-1}`,
   so multiplying by the display's prefactor `σ_L` produces exactly the
   `σ_L²` weight on the `σ_*^{-1}` variances and the weight `1` on the
   `σ_*^{-1}κ` variances of `e.initial.JL.bound`.
6. *Sample measurability* of both good-event observables at the genuine cutoff
   sample law, and the reduction of their `IntegrableOn` over the good event to
   one a.e. bound.

## What is NOT proved here (reported, not bound)

* The printed sandwich `σ_{L,*}^{-1}(□_m) ≤ 2 σ_L^{-1}` is not used anywhere
  below and is not supplied here; nothing in this file needs it.
* The third block (`vecNormSq (coarseScaleSeparation ...)`) is converted here
  only up to the deterministic residual `(σ_L σ_{L,*}^{-1}(□_m) - 1)²`.  The
  residual is bounded by `4 δ₁²` by combining the proved Step-2 downscale bound
  (`coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le`,
  `CombineIntegerDownscale.lean`) with the `n → ∞` limit supplied by
  `Annealed.sigmaBar_characterization`
  (`Annealed/RunningDiffusivity/Characterization.lean`); that anchor lemma is
  not in this file.  The printed closure, which cites only the sandwich
  `σ_{L,*}(□_m) ≤ σ_L ≤ 2 σ_{L,*}(□_m)`, does not close the residual —.  The
  residual is displayed explicitly, never bound.
* The corridor sum over `L ≤ n ≤ m`, the reabsorption of `1/2 E[J(□_m)]`, and
  the passage from `E[1_G · X]` to `E[X]` are not performed here; the last needs
  integrability of the two observables on the whole space, not only on `G`.
* The two `IntegrableOn` clauses are reduced to a single a.e. bound over the
  good event; no proved statement produces that bound.  The clause is a
  conditional A obligation in the convention of `VarianceBridge.lean` and of
  the integrated form of `VarianceCarrierSeam.lean`.

This module makes no source-node status claim; every declaration is a local
Provider result.

## Main results

* `sq_matrixOperatorNorm_sub_le_three_mul`
* `coarseBlockScaleSeparation`
* `coarseBlockMatrixVariationSq`
* `coarseScaleSeparation_eq_coarseBlockScaleSeparation`
* `coarseMatrixVariationSq_eq_coarseBlockMatrixVariationSq`
* `coarseBlockScaleSeparation_sub`
* `coarseBlockMatrixVariationSq_le_two_mul_add_two_mul`
* `coarseBlockMatrixVariationSq_le_six_mul`
* `vecNormSq_coarseBlockScaleSeparation_le_three_mul`
* `starInverseCenteredFluctuationSq`
* `starInverseKappaCenteredFluctuationSq`
* `starInverseVarianceAtScale`
* `starInverseKappaVarianceAtScale`
* `integral_coarseBlockObservable_cubeSet_eq_originCube`
* `aestronglyMeasurable_starInverseCenteredFluctuationSq`
* `aestronglyMeasurable_starInverseKappaCenteredFluctuationSq`
* `coefficientCutoffLaw_integral_starInverseCenteredFluctuationSq_eq`
* `coefficientCutoffLaw_integral_starInverseKappaCenteredFluctuationSq_eq`
* `coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le`
* `coefficientCutoffLaw_annealedLowerRightGap_eq`
* `coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le`
* `coefficientCutoffLaw_sigmaBar_mul_vecNormSq_coarseBlockScaleSeparation_le`
* `aemeasurable_coarseBlockScaleSeparation`
* `aemeasurable_coarseBlockMatrixVariationSq`
* `aemeasurable_coarseMatrixVariationCorridor`
* `aemeasurable_coarseScaleSeparationSq`
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Besov
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Elementary matrix and vector helpers -/

/-- The Chapter 2 Euclidean matrix operator norm is symmetric in a difference. -/
private theorem matrixOperatorNorm_sub_comm (X Y : Mat d) :
    Ch02.matrixOperatorNorm (X - Y) = Ch02.matrixOperatorNorm (Y - X) := by
  have h : Y - X = -(X - Y) := by abel
  show ‖X - Y‖ = ‖Y - X‖
  rw [h, norm_neg]

/-- Triangle inequality for the Chapter 2 Euclidean matrix operator norm, in the
three-point form. -/
private theorem matrixOperatorNorm_sub_le_add (X Y Z : Mat d) :
    Ch02.matrixOperatorNorm (X - Z) ≤
      Ch02.matrixOperatorNorm (X - Y) + Ch02.matrixOperatorNorm (Y - Z) := by
  have h :=
    Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
      (X - Z) (X - Y)
  have hrw : X - Z - (X - Y) = Y - Z := by abel
  rw [hrw] at h
  linarith

/-- **The three-term deterministic-centering split, matrix form.**  This is the
squared triangle inequality behind the constant `3`; combined with the two-term
load split it produces the printed `6 = 2 · 3`. -/
theorem sq_matrixOperatorNorm_sub_le_three_mul (X Y Z W : Mat d) :
    Ch02.matrixOperatorNorm (X - W) ^ 2 ≤
      3 * (Ch02.matrixOperatorNorm (X - Y) ^ 2 + Ch02.matrixOperatorNorm (Y - Z) ^ 2 +
        Ch02.matrixOperatorNorm (Z - W) ^ 2) := by
  have h1 := matrixOperatorNorm_sub_le_add X Y W
  have h2 := matrixOperatorNorm_sub_le_add Y Z W
  have hXY := Ch02.matrixOperatorNorm_nonneg (X - Y)
  have hYZ := Ch02.matrixOperatorNorm_nonneg (Y - Z)
  have hZW := Ch02.matrixOperatorNorm_nonneg (Z - W)
  have hXW := Ch02.matrixOperatorNorm_nonneg (X - W)
  nlinarith [sq_nonneg (Ch02.matrixOperatorNorm (X - Y) - Ch02.matrixOperatorNorm (Y - Z)),
    sq_nonneg (Ch02.matrixOperatorNorm (Y - Z) - Ch02.matrixOperatorNorm (Z - W)),
    sq_nonneg (Ch02.matrixOperatorNorm (X - Y) - Ch02.matrixOperatorNorm (Z - W))]

/-- Three-term Euclidean split of a squared vector length, at the sharp
constant `3`. -/
private theorem vecNormSq_add_three_le (x y z : Vec d) :
    vecNormSq (x + y + z) ≤ 3 * (vecNormSq x + vecNormSq y + vecNormSq z) := by
  have hcalc : ∑ i, (x i + y i + z i) ^ 2 ≤ ∑ i, 3 * (x i ^ 2 + y i ^ 2 + z i ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    nlinarith [sq_nonneg (x i - y i), sq_nonneg (y i - z i), sq_nonneg (x i - z i)]
  calc
    vecNormSq (x + y + z) = ∑ i, (x i + y i + z i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i, 3 * (x i ^ 2 + y i ^ 2 + z i ^ 2) := hcalc
    _ = 3 * (vecNormSq x + vecNormSq y + vecNormSq z) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp [vecNormSq, vecDot, pow_two]

/-! ## The block reading of the comparison vector -/

/-- The comparison vector, written from the **coarse block matrix** of the cube
instead of the Chapter 2 coarse matrices: the lower half of `𝐀(Q;a)` at the
block load `(-p, q)`, minus `p`.

This carrier takes no ellipticity witness, so it is the form in which the
observable can be integrated against a coefficient law. -/
def coarseBlockScaleSeparation (Q : TriadicCube d) (p q : Vec d)
    (a : RegCoeffField d) : Vec d :=
  matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q -
    matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p - p

/-- The coarse-matrix variation on the block carrier. -/
def coarseBlockMatrixVariationSq (Q : TriadicCube d) (p q : Vec d)
    (a : RegCoeffField d) (R : TriadicCube d) : ℝ :=
  vecNormSq (coarseBlockScaleSeparation Q p q a - coarseBlockScaleSeparation R p q a)

variable [NeZero d]

/-- **The block-vector reading of the comparison vector.**  The
`Provider.Besov.Carriers` vector `σ_*^{-1}(Q)(q + κ(Q)p) - p` is the lower half
of the coarse block matrix of the cube evaluated at the block load `(-p, q)`,
minus `p`.

The sign is forced by `𝐀_{lowerLeft} = -(σ_*^{-1}κ)`
(`Ch02.blockMatrixOfCoarseMatrices`): the block load carries `-p`, not `p`. -/
theorem coarseScaleSeparation_eq_coarseBlockScaleSeparation (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) :
    coarseScaleSeparation a ha Q p q = coarseBlockScaleSeparation Q p q a := by
  have hblock :=
    Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      ha Q
  unfold coarseBlockScaleSeparation coarseScaleSeparation
  rw [hblock]
  have hlr :
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)).lowerRight =
        Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) := rfl
  have hll :
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)).lowerLeft =
        -(Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) *
            Ch02.kappaCoarse (Ch02.cubeDomain Q)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)) := rfl
  rw [hlr, hll, neg_matVecMul, matVecMul_add, matVecMul_mul]
  abel

/-- The coarse-matrix variation of `Provider.Besov.LargeScaleSplit` on the block
carrier. -/
theorem coarseMatrixVariationSq_eq_coarseBlockMatrixVariationSq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d)
    (R : TriadicCube d) :
    coarseMatrixVariationSq a ha Q p q R = coarseBlockMatrixVariationSq Q p q a R := by
  unfold coarseMatrixVariationSq coarseBlockMatrixVariationSq
  rw [coarseScaleSeparation_eq_coarseBlockScaleSeparation a ha Q p q,
    coarseScaleSeparation_eq_coarseBlockScaleSeparation a ha R p q]

omit [NeZero d] in
/-- **The two channels of the coarse-matrix variation.**  The difference of the two
comparison vectors is the `σ_*^{-1}` channel applied to `q` minus the
lower-left channel applied to `p`; the constant `-p` cancels, so this is
literally the vector printed. -/
theorem coarseBlockScaleSeparation_sub (Q R : TriadicCube d) (p q : Vec d)
    (a : RegCoeffField d) :
    coarseBlockScaleSeparation Q p q a - coarseBlockScaleSeparation R p q a =
      matVecMul ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
          (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) q -
        matVecMul ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft -
          (coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft) p := by
  unfold coarseBlockScaleSeparation
  rw [sub_matVecMul, sub_matVecMul]
  abel

/-! ## The two-term load split -/

omit [NeZero d] in
/-- **The load split.**  The squared coarse-matrix variation is at most `2|q|²`
times the squared operator norm of the `σ_*^{-1}` variation plus `2|p|²` times
the squared operator norm of the `σ_*^{-1}κ` variation.

The matrix norm is the Euclidean operator norm, which is the manuscript's `|A|`.
-/
theorem coarseBlockMatrixVariationSq_le_two_mul_add_two_mul (Q R : TriadicCube d)
    (p q : Vec d) (a : RegCoeffField d) :
    coarseBlockMatrixVariationSq Q p q a R ≤
      2 * Ch02.matrixOperatorNorm ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
            (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) ^ 2 * vecNormSq q +
        2 * Ch02.matrixOperatorNorm ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft -
            (coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft) ^ 2 * vecNormSq p := by
  unfold coarseBlockMatrixVariationSq
  rw [coarseBlockScaleSeparation_sub]
  refine le_trans (vecNormSq_sub_le _ _) ?_
  have h1 :=
    Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
        (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) q
  have h2 :=
    Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft -
        (coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft) p
  linarith

omit [NeZero d] in
/-- **The printed constant `6`.**  Composing the two-term load split with the
three-term deterministic-centering split at two arbitrary deterministic
centerings `C` (for `Q`) and `C'` (for `R`) gives the printed `6|q|²(.) +
6|p|²(.)`.  Nothing is assumed about `C` and `C'`. -/
theorem coarseBlockMatrixVariationSq_le_six_mul (Q R : TriadicCube d) (p q : Vec d)
    (a : RegCoeffField d) (C C' : BlockMat d) :
    coarseBlockMatrixVariationSq Q p q a R ≤
      6 * vecNormSq q *
          (Ch02.matrixOperatorNorm
              ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight - C.lowerRight) ^ 2 +
            Ch02.matrixOperatorNorm (C.lowerRight - C'.lowerRight) ^ 2 +
            Ch02.matrixOperatorNorm
              ((coarseBlockMatrix (cubeSet R) a.toFun).lowerRight - C'.lowerRight) ^ 2) +
        6 * vecNormSq p *
          (Ch02.matrixOperatorNorm
              ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) ^ 2 +
            Ch02.matrixOperatorNorm (C.lowerLeft - C'.lowerLeft) ^ 2 +
            Ch02.matrixOperatorNorm
              ((coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft - C'.lowerLeft) ^ 2) := by
  have hbase := coarseBlockMatrixVariationSq_le_two_mul_add_two_mul Q R p q a
  have hlr :=
    sq_matrixOperatorNorm_sub_le_three_mul
      (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight C.lowerRight C'.lowerRight
      (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight
  have hll :=
    sq_matrixOperatorNorm_sub_le_three_mul
      (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft C.lowerLeft C'.lowerLeft
      (coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft
  rw [matrixOperatorNorm_sub_comm C'.lowerRight (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight]
    at hlr
  rw [matrixOperatorNorm_sub_comm C'.lowerLeft (coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft]
    at hll
  have hqn : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hpn : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  nlinarith [hbase, mul_le_mul_of_nonneg_right hlr hqn, mul_le_mul_of_nonneg_right hll hpn]

omit [NeZero d] in
/-- **The third good-event block.**  With `q = σ p` the comparison vector at the
parent cube splits into the centred `σ_*^{-1}` fluctuation, the centred
`σ_*^{-1}κ` fluctuation, and the deterministic residual `(σ · c - 1) p`, where
`c` is the scalar of the centering's lower-right block.  The residual is
displayed, never bound in this file: it is bounded by `4 δ₁²` through the
proved Step-2 downscale bound in the `n → ∞` limit of
`Annealed.sigmaBar_characterization` (the anchor lemma, not in this file —).

The two conditions on `C` are exactly what the genuine cutoff law supplies at
the annealed centering: `hC` is the scalarity of the annealed inverse-star block
(`Provider.Homogenization.coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one`)
and `hCll` is `e.annealed.khom.zero`
(`Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero`). -/
theorem vecNormSq_coarseBlockScaleSeparation_le_three_mul (Q : TriadicCube d)
    (a : RegCoeffField d) (C : BlockMat d) {sigma c : ℝ} {p q : Vec d}
    (hpq : q = sigma • p) (hC : C.lowerRight = c • (1 : Mat d)) (hCll : C.lowerLeft = 0) :
    vecNormSq (coarseBlockScaleSeparation Q p q a) ≤
      3 * (sigma ^ 2 *
            Ch02.matrixOperatorNorm
              ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight - C.lowerRight) ^ 2 *
            vecNormSq p +
          (sigma * c - 1) ^ 2 * vecNormSq p +
          Ch02.matrixOperatorNorm
              ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) ^ 2 *
            vecNormSq p) := by
  have hsplit :
      coarseBlockScaleSeparation Q p q a =
        sigma • matVecMul ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight - C.lowerRight) p +
            (sigma * c - 1) • p +
          -matVecMul ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) p := by
    unfold coarseBlockScaleSeparation
    rw [hpq, matVecMul_smul, sub_matVecMul, sub_matVecMul, hC, hCll]
    have hone : matVecMul (c • (1 : Mat d)) p = c • p := by
      funext i
      simp [matVecMul, Matrix.smul_apply, Matrix.one_apply, mul_comm]
    rw [hone, smul_sub, smul_smul]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      matVecMul, Matrix.zero_apply, zero_mul, Finset.sum_const_zero]
    ring
  rw [hsplit]
  refine le_trans (vecNormSq_add_three_le _ _ _) ?_
  have hsm1 : vecNormSq (sigma •
      matVecMul ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight - C.lowerRight) p) =
      sigma ^ 2 *
        vecNormSq (matVecMul
          ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight - C.lowerRight) p) :=
    vecNormSq_smul _ _
  have hsm2 : vecNormSq ((sigma * c - 1) • p) = (sigma * c - 1) ^ 2 * vecNormSq p :=
    vecNormSq_smul _ _
  have hneg : vecNormSq (-matVecMul
        ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) p) =
      vecNormSq (matVecMul
        ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) p) := by
    have hrw : (-matVecMul ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) p) =
        (-1 : ℝ) • matVecMul
          ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) p := by
      funext i; simp
    rw [hrw, vecNormSq_smul]
    ring
  rw [hsm1, hsm2, hneg]
  have hb1 := Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight - C.lowerRight) p
  have hb2 := Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft - C.lowerLeft) p
  nlinarith [hb1, hb2, sq_nonneg sigma]

/-! ## The variance carriers at the genuine cutoff law -/

/-- `|σ_*^{-1}(R;a) - σ_{L,*}^{-1}(□_n)|²`: the squared operator-norm
fluctuation of the inverse-star coarse block of `R` about the **annealed** block
at scale `n`.  The centering is the entrywise expectation
(`Ch04.annealedBlockMatrix_lowerRight_apply` is `rfl`), so the integral of this
quantity at `R = □_n` is the manuscript's true variance
`var[σ_{L,*}^{-1}(□_n)]`. -/
def starInverseCenteredFluctuationSq (M : ABKModel d) (L n : ℤ) (R : TriadicCube d)
    (a : RegCoeffField d) : ℝ :=
  Ch02.matrixOperatorNorm ((coarseBlockMatrix (cubeSet R) a.toFun).lowerRight -
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2

/-- `|(σ_*^{-1}κ)(R;a) - E[(σ_*^{-1}κ)(□_n)]|²`, written on the lower-left block.
Since `𝐀_{lowerLeft} = -(σ_*^{-1}κ)` and the centering is the expectation of the
same block, this is the manuscript's `var`-integrand for
`σ_{L,*}^{-1}(□_n) κ_L(□_n)`. -/
def starInverseKappaCenteredFluctuationSq (M : ABKModel d) (L n : ℤ) (R : TriadicCube d)
    (a : RegCoeffField d) : ℝ :=
  Ch02.matrixOperatorNorm ((coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft -
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerLeft) ^ 2

/-- The manuscript variance `var[σ_{L,*}^{-1}(□_n)]`. -/
def starInverseVarianceAtScale (M : ABKModel d) (L n : ℤ) : ℝ :=
  ∫ a, starInverseCenteredFluctuationSq M L n (originCube d n) a
    ∂(Cutoff.coefficientCutoffLaw M L)

/-- The manuscript variance `var[σ_{L,*}^{-1}(□_n) κ_L(□_n)]`. -/
def starInverseKappaVarianceAtScale (M : ABKModel d) (L n : ℤ) : ℝ :=
  ∫ a, starInverseKappaCenteredFluctuationSq M L n (originCube d n) a
    ∂(Cutoff.coefficientCutoffLaw M L)

/-! ## Stationary collapse of the printed `⨍_z` -/

omit [NeZero d] in
/-- **Scale-free stationary transfer for a generic coarse-block functional.**
Under real-translation invariance, every real functional of the coarse block
matrix on a descendant of an origin cube has the same expectation as the same
functional on the origin cube at the descendant's scale.  This is the generic
form of the entrywise
`Provider.Annealed.integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_mem_descendantsAtScale`;
both consume the same public real-translation transfer. -/
theorem integral_coarseBlockObservable_cubeSet_eq_originCube
    {P : Ch04.RestrictionCoeffLaw d} (hstat : Provider.Annealed.IsStationaryRealR P)
    (F : BlockMat d → ℝ) {n k : ℤ} (hnk : n ≤ k)
    (hmeas : AEStronglyMeasurable
      (fun a : RegCoeffField d => F (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun)) P)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d k) n) :
    ∫ a, F (coarseBlockMatrix (cubeSet R) a.toFun) ∂P =
      ∫ a, F (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) ∂P := by
  have hscale : R.scale = n := Ch04.scale_eq_of_mem_descendantsAtScale_originCube hnk hR
  have hcov :
      ∀ (V : Set (Vec d)) (z : Vec d) (b : CoeffField d),
        F (coarseBlockMatrix (translateSet z V) b) =
          F (coarseBlockMatrix V (translateCoeffField z b)) := by
    intro V z b
    exact congrArg F (coarseBlockMatrix_translateSet_eq_translateCoeffField z V b)
  calc
    ∫ a, F (coarseBlockMatrix (cubeSet R) a.toFun) ∂P
        = ∫ a, F (coarseBlockMatrix
            (translateSet (triadicCubeShift R) (cubeSet (originCube d R.scale))) a.toFun) ∂P := by
          rw [cubeSet_eq_translateSet_originCube_of_triadicCube R]
    _ = ∫ a, F (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun) ∂P := by
          rw [hscale]
          exact Provider.Annealed.integral_comp_toFun_translation_transfer_real (P := P)
            (X := fun U b => F (coarseBlockMatrix U b)) hstat hmeas hcov (triadicCubeShift R)
    _ = ∫ a, F (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) ∂P := by
          rw [hscale]

omit [NeZero d] in
/-- Depth form of the descendant index set below an origin cube. -/
private theorem descendantsAtDepth_originCube_eq {n k : ℤ} (hnk : n ≤ k) :
    descendantsAtDepth (originCube d k) (Int.toNat (k - n)) =
      descendantsAtScale (originCube d k) n :=
  (descendantsAtScale_eq_descendantsAtDepth (originCube d k) (k := n) hnk).symm

omit [NeZero d] in
/-- A.e. strong measurability of the operator-norm fluctuation of the
inverse-star coarse block, at any carrier law. -/
theorem aestronglyMeasurable_starInverseCenteredFluctuationSq
    (M : ABKModel d) (L n : ℤ) (R : TriadicCube d) :
    AEStronglyMeasurable (starInverseCenteredFluctuationSq M L n R)
      (Cutoff.coefficientCutoffLaw M L) := by
  have hP : Ch04.RestrictionLawCarrier (Cutoff.coefficientCutoffLaw M L) :=
    Cutoff.coefficientCutoffLaw_lawCarrier M L
  have hblock := hP.aemeasurable_coarseSigmaStarInv_cubeSet R
  exact (((hblock.sub aemeasurable_const).norm).pow_const 2).aestronglyMeasurable

omit [NeZero d] in
/-- A.e. strong measurability of the operator-norm fluctuation of the lower-left
coarse block, at any carrier law. -/
theorem aestronglyMeasurable_starInverseKappaCenteredFluctuationSq
    (M : ABKModel d) (L n : ℤ) (R : TriadicCube d) :
    AEStronglyMeasurable (starInverseKappaCenteredFluctuationSq M L n R)
      (Cutoff.coefficientCutoffLaw M L) := by
  have hP : Ch04.RestrictionLawCarrier (Cutoff.coefficientCutoffLaw M L) :=
    Cutoff.coefficientCutoffLaw_lawCarrier M L
  have hblock := hP.aemeasurable_coarseBlockMatrix_lowerLeft_cubeSet R
  exact (((hblock.sub aemeasurable_const).norm).pow_const 2).aestronglyMeasurable

omit [NeZero d] in
/-- **Stationary collapse of the `σ_*^{-1}` variance.**  Every descendant of
`□_k` at scale `n` carries the same expectation as the origin cube at scale `n`,
so the printed `⨍_{z ∈ 3ⁿℤᵈ ∩ □_m}` disappears on taking expectations. -/
theorem coefficientCutoffLaw_integral_starInverseCenteredFluctuationSq_eq
    (M : ABKModel d) (L : ℤ) {n k : ℤ} (hnk : n ≤ k) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d k) n) :
    ∫ a, starInverseCenteredFluctuationSq M L n R a ∂(Cutoff.coefficientCutoffLaw M L) =
      starInverseVarianceAtScale M L n :=
  integral_coarseBlockObservable_cubeSet_eq_originCube
    (fun z => Cutoff.coefficientCutoffLaw_stationary_real M L z)
    (fun A => Ch02.matrixOperatorNorm (A.lowerRight -
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2)
    hnk (aestronglyMeasurable_starInverseCenteredFluctuationSq M L n (originCube d n)) hR

omit [NeZero d] in
/-- **Stationary collapse of the `σ_*^{-1}κ` variance.** -/
theorem coefficientCutoffLaw_integral_starInverseKappaCenteredFluctuationSq_eq
    (M : ABKModel d) (L : ℤ) {n k : ℤ} (hnk : n ≤ k) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d k) n) :
    ∫ a, starInverseKappaCenteredFluctuationSq M L n R a ∂(Cutoff.coefficientCutoffLaw M L) =
      starInverseKappaVarianceAtScale M L n :=
  integral_coarseBlockObservable_cubeSet_eq_originCube
    (fun z => Cutoff.coefficientCutoffLaw_stationary_real M L z)
    (fun A => Ch02.matrixOperatorNorm (A.lowerLeft -
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerLeft) ^ 2)
    hnk (aestronglyMeasurable_starInverseKappaCenteredFluctuationSq M L n (originCube d n)) hR

/-! ## The annealed variance display -/

/-- The six-constant split at the two annealed centerings of the genuine cutoff
law.  The `κ` mean gap term of the generic split disappears because both annealed
lower-left blocks vanish (`e.annealed.khom.zero`). -/
private theorem coarseBlockMatrixVariationSq_le_annealedCentered (M : ABKModel d)
    (L n m : ℤ) (p q : Vec d) (a : RegCoeffField d) (R : TriadicCube d) :
    coarseBlockMatrixVariationSq (originCube d m) p q a R ≤
      6 * vecNormSq q *
          (starInverseCenteredFluctuationSq M L m (originCube d m) a +
            Ch02.matrixOperatorNorm
              ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight -
                (Ch04.annealedBlockMatrixAtScale
                  (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2 +
            starInverseCenteredFluctuationSq M L n R a) +
        6 * vecNormSq p *
          (starInverseKappaCenteredFluctuationSq M L m (originCube d m) a +
            starInverseKappaCenteredFluctuationSq M L n R a) := by
  have hsix := coarseBlockMatrixVariationSq_le_six_mul (originCube d m) R p q a
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m)
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
  have hzm : (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerLeft =
      0 :=
    Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero M L
      (originCube d m)
  have hzn : (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerLeft =
      0 :=
    Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero M L
      (originCube d n)
  have hkappaGap : Ch02.matrixOperatorNorm
      ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerLeft -
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerLeft) ^ 2 =
      0 := by
    rw [hzm, hzn, sub_zero]
    show ‖(0 : Mat d)‖ ^ 2 = 0
    simp
  rw [hkappaGap] at hsix
  unfold starInverseCenteredFluctuationSq starInverseKappaCenteredFluctuationSq
  nlinarith [hsix, vecNormSq_nonneg p]

omit [NeZero d] in
/-- The exact expectation of the two-block right-hand side of the split.  The
four values are supplied by the caller so that the equation can be applied with
the stationary collapses already performed. -/
private theorem integral_two_block_eq {P : Measure (RegCoeffField d)}
    [IsFiniteMeasure P] (hprob : P.real Set.univ = 1) (c1 c2 gap v1 v3 w1 w3 : ℝ)
    (f1 f3 g1 g3 : RegCoeffField d → ℝ)
    (hf1 : Integrable f1 P) (hf3 : Integrable f3 P)
    (hg1 : Integrable g1 P) (hg3 : Integrable g3 P)
    (e1 : ∫ a, f1 a ∂P = v1) (e3 : ∫ a, f3 a ∂P = v3)
    (eg1 : ∫ a, g1 a ∂P = w1) (eg3 : ∫ a, g3 a ∂P = w3) :
    ∫ a, (c1 * (f1 a + gap + f3 a) + c2 * (g1 a + g3 a)) ∂P =
      c1 * (v1 + gap + v3) + c2 * (w1 + w3) := by
  have h1 : ∫ a, (c1 * (f1 a + gap + f3 a) + c2 * (g1 a + g3 a)) ∂P =
      (∫ a, c1 * (f1 a + gap + f3 a) ∂P) + ∫ a, c2 * (g1 a + g3 a) ∂P :=
    integral_add (((hf1.add (integrable_const gap)).add hf3).const_mul c1)
      ((hg1.add hg3).const_mul c2)
  have h2 : ∫ a, c1 * (f1 a + gap + f3 a) ∂P = c1 * ∫ a, (f1 a + gap + f3 a) ∂P :=
    integral_const_mul _ _
  have h3 : ∫ a, c2 * (g1 a + g3 a) ∂P = c2 * ∫ a, (g1 a + g3 a) ∂P :=
    integral_const_mul _ _
  have h4 : ∫ a, (f1 a + gap + f3 a) ∂P = (∫ a, (f1 a + gap) ∂P) + ∫ a, f3 a ∂P :=
    integral_add (hf1.add (integrable_const gap)) hf3
  have h5 : ∫ a, (f1 a + gap) ∂P = (∫ a, f1 a ∂P) + ∫ _a, gap ∂P :=
    integral_add hf1 (integrable_const gap)
  have h6 : ∫ a, (g1 a + g3 a) ∂P = (∫ a, g1 a ∂P) + ∫ a, g3 a ∂P :=
    integral_add hg1 hg3
  have h7 : ∫ _a : RegCoeffField d, gap ∂P = gap := by
    rw [integral_const, hprob, one_smul]
  rw [h1, h2, h3, h4, h5, h6, h7, e1, e3, eg1, eg3]

/-- **The variance split, at the genuine coefficient cutoff law.**  The expectation
of the printed `⨍_z` block is below the printed `6|q|²(var + var + |mean gap|²)
+ 6|p|²(var + var)`.

The `κ` mean gap does not appear because both annealed lower-left blocks vanish
(`e.annealed.khom.zero`, proved as
`Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero`).

The five integrability clauses are conditional A obligations on the caller's
own observables, in the convention of
`integral_starredFluctuationOperatorNormSq_le_two_descendantsAverage_add_eight_blockJTraceAverageSq_of_integrable`
(`Provider/Homogenization/VarianceBridge.lean`) — whose own docstring
records that its integrability is supplied by a source-specific moment
argument, discharged there at its own use site, whereas nothing yet discharges
these. -/
theorem coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le
    (M : ABKModel d) (L : ℤ) {n m : ℤ} (hnm : n ≤ m) (p q : Vec d)
    (hLHS : Integrable (fun a => descendantsAverage (originCube d m) (Int.toNat (m - n))
        (coarseBlockMatrixVariationSq (originCube d m) p q a))
      (Cutoff.coefficientCutoffLaw M L))
    (hQlr : Integrable (starInverseCenteredFluctuationSq M L m (originCube d m))
      (Cutoff.coefficientCutoffLaw M L))
    (hQll : Integrable (starInverseKappaCenteredFluctuationSq M L m (originCube d m))
      (Cutoff.coefficientCutoffLaw M L))
    (hRlr : ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
      Integrable (starInverseCenteredFluctuationSq M L n R) (Cutoff.coefficientCutoffLaw M L))
    (hRll : ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
      Integrable (starInverseKappaCenteredFluctuationSq M L n R)
        (Cutoff.coefficientCutoffLaw M L)) :
    ∫ a, descendantsAverage (originCube d m) (Int.toNat (m - n))
        (coarseBlockMatrixVariationSq (originCube d m) p q a)
        ∂(Cutoff.coefficientCutoffLaw M L) ≤
      6 * vecNormSq q *
          (starInverseVarianceAtScale M L m +
            Ch02.matrixOperatorNorm
              ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight -
                (Ch04.annealedBlockMatrixAtScale
                  (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2 +
            starInverseVarianceAtScale M L n) +
        6 * vecNormSq p *
          (starInverseKappaVarianceAtScale M L m + starInverseKappaVarianceAtScale M L n) := by
  classical
  have hRlrAvg : Integrable
      (fun a => descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => starInverseCenteredFluctuationSq M L n R a))
      (Cutoff.coefficientCutoffLaw M L) :=
    Ch04.integrable_descendantsAverage hRlr
  have hRllAvg : Integrable
      (fun a => descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => starInverseKappaCenteredFluctuationSq M L n R a))
      (Cutoff.coefficientCutoffLaw M L) :=
    Ch04.integrable_descendantsAverage hRll
  have hRHSint : Integrable
      (fun a => 6 * vecNormSq q *
            (starInverseCenteredFluctuationSq M L m (originCube d m) a +
              Ch02.matrixOperatorNorm
                ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight -
                  (Ch04.annealedBlockMatrixAtScale
                    (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2 +
              descendantsAverage (originCube d m) (Int.toNat (m - n))
                (fun R => starInverseCenteredFluctuationSq M L n R a)) +
          6 * vecNormSq p *
            (starInverseKappaCenteredFluctuationSq M L m (originCube d m) a +
              descendantsAverage (originCube d m) (Int.toNat (m - n))
                (fun R => starInverseKappaCenteredFluctuationSq M L n R a)))
      (Cutoff.coefficientCutoffLaw M L) :=
    (((hQlr.add (integrable_const _)).add hRlrAvg).const_mul _).add
      ((hQll.add hRllAvg).const_mul _)
  have hpoint : ∀ a : RegCoeffField d,
      descendantsAverage (originCube d m) (Int.toNat (m - n))
          (coarseBlockMatrixVariationSq (originCube d m) p q a) ≤
        6 * vecNormSq q *
            (starInverseCenteredFluctuationSq M L m (originCube d m) a +
              Ch02.matrixOperatorNorm
                ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight -
                  (Ch04.annealedBlockMatrixAtScale
                    (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2 +
              descendantsAverage (originCube d m) (Int.toNat (m - n))
                (fun R => starInverseCenteredFluctuationSq M L n R a)) +
          6 * vecNormSq p *
            (starInverseKappaCenteredFluctuationSq M L m (originCube d m) a +
              descendantsAverage (originCube d m) (Int.toNat (m - n))
                (fun R => starInverseKappaCenteredFluctuationSq M L n R a)) := by
    intro a
    refine le_trans (descendantsAverage_le_descendantsAverage _ _
      (fun R _hR => coarseBlockMatrixVariationSq_le_annealedCentered M L n m p q a R))
      (le_of_eq ?_)
    simp only [descendantsAverage_add, descendantsAverage_mul_left,
      descendantsAverage_const]
  refine le_trans (integral_mono hLHS hRHSint hpoint) (le_of_eq ?_)
  refine integral_two_block_eq (P := Cutoff.coefficientCutoffLaw M L) probReal_univ _ _ _ _ _ _ _
    _ _ _ _ hQlr hRlrAvg hQll hRllAvg rfl ?_ rfl ?_
  · rw [Ch04.integral_descendantsAverage_eq_descendantsAverage_integral hRlr,
      Ch05.Section53.JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants _ _ (fun R hRmem =>
        coefficientCutoffLaw_integral_starInverseCenteredFluctuationSq_eq M L hnm
          (by rwa [descendantsAtDepth_originCube_eq hnm] at hRmem)),
      descendantsAverage_const]
  · rw [Ch04.integral_descendantsAverage_eq_descendantsAverage_integral hRll,
      Ch05.Section53.JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants _ _ (fun R hRmem =>
        coefficientCutoffLaw_integral_starInverseKappaCenteredFluctuationSq_eq M L hnm
          (by rwa [descendantsAtDepth_originCube_eq hnm] at hRmem)),
      descendantsAverage_const]

/-- **The printed mean gap.**  At the genuine cutoff law both annealed inverse-star
blocks are scalar matrices, so the operator-norm gap appearing in the display
above is the squared scalar difference `|σ_{L,*}^{-1}(□_m) -
σ_{L,*}^{-1}(□_n)|²` printed -- exactly the object bounded by Step 2
(`e.means.downscale.by.defect`, proved as
`coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le`). -/
theorem coefficientCutoffLaw_annealedLowerRightGap_eq (M : ABKModel d) (L m n : ℤ) :
    Ch02.matrixOperatorNorm
        ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight -
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2 =
      (annealedSigmaStarInvScalarAtScale M L m -
        annealedSigmaStarInvScalarAtScale M L n) ^ 2 := by
  have hm : (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight =
      annealedSigmaStarInvScalarAtScale M L m • (1 : Mat d) :=
    coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one M L m
  have hn : (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerRight =
      annealedSigmaStarInvScalarAtScale M L n • (1 : Mat d) :=
    coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one M L n
  rw [hm, hn, ← sub_smul, Ch02.matrixOperatorNorm_smul_one_eq_abs, sq_abs]

/-! ## The `e.pq.normed` weights -/

omit [NeZero d] in
/-- `|q|² = σ_L` at the manuscript dual load, for a unit direction. -/
private theorem vecNormSq_sqrtLoad (sigma : Observable.PositiveScalar) (x : Vec d) :
    vecNormSq (Observable.sqrtLoad sigma x) = (sigma : ℝ) * vecNormSq x := by
  rw [Observable.sqrtLoad, vecNormSq_smul, Real.sq_sqrt sigma.2.le]

omit [NeZero d] in
/-- `|p|² = σ_L^{-1}` at the manuscript primal load, for a unit direction. -/
private theorem vecNormSq_inverseSqrtLoad (sigma : Observable.PositiveScalar) (x : Vec d) :
    vecNormSq (Observable.inverseSqrtLoad sigma x) = (sigma : ℝ)⁻¹ * vecNormSq x := by
  rw [Observable.inverseSqrtLoad, vecNormSq_smul, ← Real.sqrt_inv,
    Real.sq_sqrt (inv_nonneg.mpr sigma.2.le)]

/-- **The second block of `e.initial.JL.bound`.**  At the manuscript loads of
`e.pq.normed` and a unit direction, the display's prefactor `σ_L` times the
expectation of the `⨍_z` block is below

`6 σ_L² (var[σ_{L,*}^{-1}(□_m)] + |σ_{L,*}^{-1}(□_m) - σ_{L,*}^{-1}(□_n)|²
          + var[σ_{L,*}^{-1}(□_n)])
 + 6 (var[σ_{L,*}^{-1}κ_L(□_m)] + var[σ_{L,*}^{-1}κ_L(□_n)])`,

which is exactly the printed weighting: `σ_L²` on the inverse-star variances and
`1` on the `σ_*^{-1}κ` variances.  The mean gap is displayed in the operator norm
of the difference of the two annealed lower-right blocks; on the genuine law
those blocks are scalar, so it is the printed scalar gap.

The five integrability clauses are conditional A obligations; see
`coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le`. -/
theorem coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le
    (M : ABKModel d) (L : ℤ) {n m : ℤ} (hnm : n ≤ m) {e : Vec d} (he : vecNormSq e = 1)
    (hLHS : Integrable (fun a => descendantsAverage (originCube d m) (Int.toNat (m - n))
        (coarseBlockMatrixVariationSq (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a))
      (Cutoff.coefficientCutoffLaw M L))
    (hQlr : Integrable (starInverseCenteredFluctuationSq M L m (originCube d m))
      (Cutoff.coefficientCutoffLaw M L))
    (hQll : Integrable (starInverseKappaCenteredFluctuationSq M L m (originCube d m))
      (Cutoff.coefficientCutoffLaw M L))
    (hRlr : ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
      Integrable (starInverseCenteredFluctuationSq M L n R) (Cutoff.coefficientCutoffLaw M L))
    (hRll : ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
      Integrable (starInverseKappaCenteredFluctuationSq M L n R)
        (Cutoff.coefficientCutoffLaw M L)) :
    (Annealed.sigmaBar M L : ℝ) *
        ∫ a, descendantsAverage (originCube d m) (Int.toNat (m - n))
          (coarseBlockMatrixVariationSq (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a)
          ∂(Cutoff.coefficientCutoffLaw M L) ≤
      6 * (Annealed.sigmaBar M L : ℝ) ^ 2 *
          (starInverseVarianceAtScale M L m +
            Ch02.matrixOperatorNorm
              ((Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight -
                (Ch04.annealedBlockMatrixAtScale
                  (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2 +
            starInverseVarianceAtScale M L n) +
        6 * (starInverseKappaVarianceAtScale M L m + starInverseKappaVarianceAtScale M L n) := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).2
  have hbase :=
    coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le M L hnm
      (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
      (Observable.sqrtLoad (Annealed.sigmaBar M L) e) hLHS hQlr hQll hRlr hRll
  rw [vecNormSq_sqrtLoad, vecNormSq_inverseSqrtLoad, he, mul_one, mul_one] at hbase
  have hstep := mul_le_mul_of_nonneg_left hbase hsigma.le
  refine hstep.trans (le_of_eq ?_)
  have hinv : (Annealed.sigmaBar M L : ℝ) * ((Annealed.sigmaBar M L : ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hsigma)
  field_simp

/-- **The third block of `e.initial.JL.bound`, at the genuine cutoff law.**  At the
manuscript loads and a unit direction, the display's prefactor `σ_L` times the
squared comparison vector at the parent cube is below

`3 σ_L² |σ_*^{-1}(□_m) - σ_{L,*}^{-1}(□_m)|² + 3 (σ_L σ_{L,*}^{-1}(□_m) - 1)²
 + 3 |σ_*^{-1}κ_L(□_m) - E[σ_*^{-1}κ_L(□_m)]|²`,

sample by sample.  The first and third terms are the two `var` integrands of
`e.initial.JL.bound` in the printed units; the middle term is the deterministic
residual, which is displayed, never bound in this file — it is bounded by `4
δ₁²` through the proved Step-2 downscale bound in the `n → ∞` limit of
`Annealed.sigmaBar_characterization` (the anchor lemma, not in this file). -/
theorem coefficientCutoffLaw_sigmaBar_mul_vecNormSq_coarseBlockScaleSeparation_le
    (M : ABKModel d) (L m : ℤ) {e : Vec d} (he : vecNormSq e = 1) (a : RegCoeffField d) :
    (Annealed.sigmaBar M L : ℝ) *
        vecNormSq (coarseBlockScaleSeparation (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a) ≤
      3 * ((Annealed.sigmaBar M L : ℝ) ^ 2 *
            starInverseCenteredFluctuationSq M L m (originCube d m) a +
          ((Annealed.sigmaBar M L : ℝ) * annealedSigmaStarInvScalarAtScale M L m - 1) ^ 2 +
          starInverseKappaCenteredFluctuationSq M L m (originCube d m) a) := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).2
  have hne : Real.sqrt ((Annealed.sigmaBar M L : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hsigma)
  have hpq : Observable.sqrtLoad (Annealed.sigmaBar M L) e =
      (Annealed.sigmaBar M L : ℝ) • Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e := by
    rw [Observable.sqrtLoad, Observable.inverseSqrtLoad, smul_smul]
    congr 1
    field_simp
    exact Real.sq_sqrt hsigma.le
  have hC : (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerRight =
      annealedSigmaStarInvScalarAtScale M L m • (1 : Mat d) :=
    coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one M L m
  have hCll : (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m).lowerLeft =
      0 :=
    Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero M L
      (originCube d m)
  have hbase := vecNormSq_coarseBlockScaleSeparation_le_three_mul (originCube d m) a
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) m) hpq hC hCll
  rw [vecNormSq_inverseSqrtLoad, he, mul_one] at hbase
  have hstep := mul_le_mul_of_nonneg_left hbase hsigma.le
  refine hstep.trans (le_of_eq ?_)
  unfold starInverseCenteredFluctuationSq starInverseKappaCenteredFluctuationSq
  field_simp

/-! ## Sample measurability and the integrability report -/

omit [NeZero d] in
private theorem aemeasurable_finsetSum_apply {P : Measure (RegCoeffField d)} {iota : Type*}
    (s : Finset iota) (G : iota → RegCoeffField d → ℝ)
    (hG : ∀ i ∈ s, AEMeasurable (G i) P) :
    AEMeasurable (fun a => ∑ i ∈ s, G i a) P := by
  classical
  have h : AEMeasurable (∑ i ∈ s, G i) P := Finset.aemeasurable_sum _ hG
  convert h using 1
  ext a
  simp

omit [NeZero d] in
private theorem aemeasurable_matVecMul_of {P : Measure (RegCoeffField d)}
    {A : RegCoeffField d → Mat d} (hA : AEMeasurable A P) (x : Vec d) :
    AEMeasurable (fun a => matVecMul (A a) x) P := by
  rw [aemeasurable_pi_iff]
  intro i
  have hentry : ∀ a : RegCoeffField d, matVecMul (A a) x i = ∑ j, A a i j * x j :=
    fun _ => rfl
  simp only [hentry]
  exact aemeasurable_finsetSum_apply _ (fun j a => A a i j * x j) fun j _hj =>
    (aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hA i) j).mul aemeasurable_const

omit [NeZero d] in
private theorem aemeasurable_vecNormSq_of {P : Measure (RegCoeffField d)}
    {v : RegCoeffField d → Vec d} (hv : AEMeasurable v P) :
    AEMeasurable (fun a => vecNormSq (v a)) P := by
  have hentry : ∀ a : RegCoeffField d, vecNormSq (v a) = ∑ i, v a i * v a i := fun _ => rfl
  simp only [hentry]
  exact aemeasurable_finsetSum_apply _ (fun i a => v a i * v a i) fun i _hi =>
    (aemeasurable_pi_iff.mp hv i).mul (aemeasurable_pi_iff.mp hv i)

omit [NeZero d] in
/-- The block comparison vector is a.e.-measurable at every carrier law. -/
theorem aemeasurable_coarseBlockScaleSeparation {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (fun a => coarseBlockScaleSeparation Q p q a) P := by
  have h1 := aemeasurable_matVecMul_of (hP.aemeasurable_coarseSigmaStarInv_cubeSet Q) q
  have h2 := aemeasurable_matVecMul_of (hP.aemeasurable_coarseBlockMatrix_lowerLeft_cubeSet Q) p
  exact (h1.sub h2).sub aemeasurable_const

omit [NeZero d] in
/-- The squared coarse-matrix variation is a.e.-measurable at every carrier
law. -/
theorem aemeasurable_coarseBlockMatrixVariationSq {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (fun a => coarseBlockMatrixVariationSq Q p q a R) P :=
  aemeasurable_vecNormSq_of
    ((aemeasurable_coarseBlockScaleSeparation hP Q p q).sub
      (aemeasurable_coarseBlockScaleSeparation hP R p q))

omit [NeZero d] in
private theorem aemeasurable_comp_coefficientCutoff (M : ABKModel d) (L : ℤ)
    {F : RegCoeffField d → ℝ} (hF : AEMeasurable F (Cutoff.coefficientCutoffLaw M L)) :
    AEMeasurable (fun omega => F (Cutoff.coefficientCutoff M.nu L omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmap : AEMeasurable F
      (Measure.map (Cutoff.coefficientCutoff M.nu L) (Cutoff.cutoffSampleLaw M).toMeasure) := by
    simpa only [Cutoff.coefficientCutoffLaw_eq_map] using hF
  simpa only [Function.comp_def] using
    hmap.comp_measurable (Cutoff.measurable_coefficientCutoff M.nu L)

/-- **Sample measurability of the corridor coarse-matrix-variation block.** This is
the observable of the second block of the good-event display
(`CombineGoodEvent.exists_cutoffGoodEvent_cutoffResponseJ_le_preVarianceSplitDisplay`),
written at the proved carriers.  Nothing in the repository supplied it; the
route is the block reading of §1 together with the four `RestrictionLawCarrier`
a.e.-measurability lemmas for the coarse blocks and the pushforward
`Cutoff.coefficientCutoffLaw_eq_map`. -/
theorem aemeasurable_coarseMatrixVariationCorridor (M : ABKModel d) (m L : ℤ) (e : Vec d) :
    AEMeasurable
      (fun omega => ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (coarseMatrixVariationSq (Cutoff.coefficientCutoff M.nu L omega)
            (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
            (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  have hP : Ch04.RestrictionLawCarrier (Cutoff.coefficientCutoffLaw M L) :=
    Cutoff.coefficientCutoffLaw_lawCarrier M L
  have hrewrite : ∀ omega : Cutoff.CutoffSample d,
      (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (coarseMatrixVariationSq (Cutoff.coefficientCutoff M.nu L omega)
              (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
              (originCube d m)
              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M L) e))) =
        (fun a : RegCoeffField d => ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (coarseBlockMatrixVariationSq (originCube d m)
              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a))
          (Cutoff.coefficientCutoff M.nu L omega) := by
    intro omega
    refine Finset.sum_congr rfl fun n _hn => ?_
    refine congrArg (fun t => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * t) ?_
    refine Ch05.Section53.JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants _ _ fun R _hR => ?_
    exact coarseMatrixVariationSq_eq_coarseBlockMatrixVariationSq _ _ _ _ _ R
  simp only [hrewrite]
  refine aemeasurable_comp_coefficientCutoff M L
    (F := fun a : RegCoeffField d => ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      descendantsAverage (originCube d m) (Int.toNat (m - n))
        (coarseBlockMatrixVariationSq (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a)) ?_
  refine aemeasurable_finsetSum_apply _ _ fun n _hn => AEMeasurable.const_mul ?_ _
  have hterms : ∀ a : RegCoeffField d,
      descendantsAverage (originCube d m) (Int.toNat (m - n))
          (coarseBlockMatrixVariationSq (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a) =
        ((descendantsAtDepth (originCube d m) (Int.toNat (m - n))).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
            coarseBlockMatrixVariationSq (originCube d m)
              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a R := fun _ => rfl
  simp only [hterms]
  refine AEMeasurable.const_mul ?_ _
  exact aemeasurable_finsetSum_apply _ _ fun R _hR =>
    aemeasurable_coarseBlockMatrixVariationSq hP _ R _ _

/-- **Sample measurability of the coarse scale-separation block.**  The observable
of the third block of the good-event display, at the proved carriers. -/
theorem aemeasurable_coarseScaleSeparationSq (M : ABKModel d) (m L : ℤ) (e : Vec d) :
    AEMeasurable
      (fun omega => vecNormSq (coarseScaleSeparation (Cutoff.coefficientCutoff M.nu L omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
        (originCube d m)
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M L) e)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hP : Ch04.RestrictionLawCarrier (Cutoff.coefficientCutoffLaw M L) :=
    Cutoff.coefficientCutoffLaw_lawCarrier M L
  have hrewrite : ∀ omega : Cutoff.CutoffSample d,
      vecNormSq (coarseScaleSeparation (Cutoff.coefficientCutoff M.nu L omega)
          (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
          (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)) =
        (fun a : RegCoeffField d => vecNormSq (coarseBlockScaleSeparation (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a))
          (Cutoff.coefficientCutoff M.nu L omega) := by
    intro omega
    exact congrArg vecNormSq
      (coarseScaleSeparation_eq_coarseBlockScaleSeparation _ _ _ _ _)
  simp only [hrewrite]
  exact aemeasurable_comp_coefficientCutoff M L
    (F := fun a : RegCoeffField d => vecNormSq (coarseBlockScaleSeparation (originCube d m)
      (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
      (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a))
    (aemeasurable_vecNormSq_of (aemeasurable_coarseBlockScaleSeparation hP _ _ _))

end

end Algsuperdiff.Section3.Provider.Homogenization

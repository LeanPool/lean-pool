/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.SigmaBarAnchor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Bounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section52.FluctuationBridge
public import LeanPool.HighContrastHomogenization.Support.HighContrast.EntryScale.BadMaximal.P1
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.QuadraticStability.CauchySchwarz

/-!
# VarianceClosure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The carrier bridge and the descendant envelopes of the variance closure

ABK26.  This module carries item (2) and the two missing inputs of item (3) of
the depgraph record for node `p.combine.corrected`, the finite good-event Besov step.

## Part A: the carrier bridge (item (2))

Two proved carriers had no seam between them.

* The **variance-split carriers** of `VarianceSplit.lean` are squared Euclidean
  operator norms of two *single blocks* of the coarse block matrix, centred at
  the annealed block matrix:
  `starInverseCenteredFluctuationSq      = |σ_*^{-1}(R;a) - σ_{L,*}^{-1}(□_n)|²`
  `starInverseKappaCenteredFluctuationSq = |(σ_*^{-1}κ)(R;a) - E[(σ_*^{-1}κ)(□_n)]|²`
  (`starInverseCenteredFluctuationSq` and
  `starInverseKappaCenteredFluctuationSq` in `VarianceSplit.lean`).
* The **Step-3 corridor carrier** of `CombineFiniteCarrierTransport.lean` is the
  squared Euclidean operator norm of the *full* `2d × 2d` starred fluctuation
  matrix `𝐁^{1/2}(𝐀_*^{-1}(U;a) - 𝐑𝐂𝐑)𝐁^{1/2}`
  (`starredFluctuationOperatorNormSq`, `VarianceBridge.lean`).

The manuscript passes between them by conjugating with the diagonal gauge
`diag(λ^{1/2}𝟙, λ^{-1/2}𝟙)` at `λ = σ_L` and reading off the two displayed
entries of the conjugated matrix.  Here that passage is exact: the conjugated
matrix's *rows* are computed at the two block loads `(e,0)` and `(0,e)`,

`Δ (e,0) = (σ · Δ_{lowerRight} e , Δ_{upperRight} e)`,
`Δ (0,e) = (Δ_{lowerLeft} e , σ^{-1} · Δ_{upperLeft} e)`,

and the two single-block operator norms are recovered by
`ContinuousLinearMap.opNorm_le_bound`.  Only the two displayed halves are used;
the companion halves are discarded by positivity, exactly as in the printed
proof.  The results are

`σ² |Δ_{lowerRight}|² ≤ starredFluctuationOperatorNormSq 𝐁(σ) 𝐂 U a`  and
`|Δ_{lowerLeft}|²     ≤ starredFluctuationOperatorNormSq 𝐁(σ) 𝐂 U a`,

with `|·|` the Chapter 2 Euclidean matrix operator norm — the manuscript's
`|A|`.  The asymmetric weighting (`σ²` on the first, `1` on the
second) is forced by the gauge and is exactly the printed weighting of
`(e.initial.JL.bound)` and of `(e.var.bound.astar.withS)`.

Composed with the proved corridor variance bound, Part A delivers the printed
**left side** of the Step-3 display `(e.var.bound.astar.withS)` at the genuine
cutoff law:

`σ_L² var[σ_{L,*}^{-1}(□_n)] + var[σ_{L,*}^{-1}(□_n)κ_L(□_n)]
   ≤ 2 C_var δ (δ + 3^{-d(n-L)})`,

where `δ` is the corridor's own two-term amplitude `δ = E²γ +
exp(-2E^{-3}γ^{-1})`.

## Part B: the two descendant envelopes (the missing inputs of item (3))

The `hK` producer (3) needs a uniform a.e. bound on the good event for
`CombineExpectation.coarseMatrixVariationBlock` and
`CombineExpectation.coarseScaleSeparationBlock`.  Both reduce, through
`VarianceSplit.coarseScaleSeparation_eq_coarseBlockScaleSeparation`,
`VarianceSplit.coarseBlockScaleSeparation_sub` and the triangle inequality, to
uniform bounds on

`Ch02.matrixOperatorNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight` and
`Ch02.matrixOperatorNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerLeft`

over the descendants `R` of `originCube d m`.  Both are supplied here.

* The `σ_*^{-1}` channel is **deterministic**: `≤ 4dν^{-1}` at every descendant
  of every cube, with no event and no random envelope
  (`matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale`).
* The `σ_*^{-1}κ` channel is **event-dependent**, and of its three pieces only
  one is supplied here: the sharp positive semidefinite off-diagonal block bound
  `|A_{lowerLeft}| ≤ √(|A_{upperLeft}|·|A_{lowerRight}|)`
  (`matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef`).
  Combined with a single-term extraction from the finite-exponent upper
  multiscale ellipticity and with the good-event clause `Λ_{1/4,1}(□_m) ≤
  2σ_L` --- which is what `CombineBadEvent.mem_observationScaleBadEvent_iff`
  reads off the complement of `observationScaleBadEvent M L m` --- it gives
  `c_{1/4,1}3^{-j/4} · |(σ_*^{-1}κ)(R)| ≤ √(2σ_L · 4dν^{-1})`
  for every descendant `R` of `□_m` at depth `j`, off the bad event.  Since
  `c_{1/4,1}3^{-j/4}` is bounded below on `j ≤ m - L`, this is the
  `K(d, σ_L, m - L, ν)` shape the producer asks for.  That composite is not
  assembled in this module.
  The deterministic route for this channel does **not** terminate in a
  *deterministic constant*:
  `Cutoff.maxDescendantBMatrixNormAtScale_le_cutoffEnvelope` bounds the
  upper-left block by `4dν^{-1}(coefficientCutoffCubeEllipticityUpper M L
  omega Q)²`, whose envelope `Cutoff.coefficientCutoffCubeEntryBound = ν +
  cutoffLocalControl …` (`Cutoff/CoefficientFamily.lean`) is a genuinely
  unbounded random variable.  This is why the good event is needed for the `κ`
  channel and not for the other.  It does terminate in an *integrable random*
  envelope, which is a different question and is exactly what item (4) needs;
  see below.

## What is NOT proved here

* Item (3) is **not** closed.  What remains is the mechanical assembly of the
  two envelopes above into the two a.e. bounds, over the corridor sum
  `∑_{n∈[L,m]} 3^{-(m-n)}` and the descendant averages at depth `(m-n).toNat`:
  the depth-uniform weight `min_{j ≤ (m-L).toNat} c_{1/4,1}3^{-j/4}`, the
  triangle inequality on `coarseBlockScaleSeparation`, and
  `descendantsAverage_le_descendantsAverage`.  No new mathematical input is
  needed; the two statements to produce are the a.e. bounds, on the good event
  `(observationScaleBadEvent M L m)ᶜ`, for the corridor sum and for
  `vecNormSq (coarseScaleSeparation …)`, whose measurability halves are
  `VarianceSplit.aemeasurable_coarseMatrixVariationCorridor` and
  `VarianceSplit.aemeasurable_coarseScaleSeparationSq`.
* Item (4), global integrability of the two observables at the genuine law, is
  **not** performed here — but it is **reachable**, by a transcription and not
  a theorem.  With `E(ω):= Cutoff.coefficientCutoffCubeEllipticityUpper M L ω
  (originCube d m)` the route is four proved steps, three of them in this file:
  (1) `Cutoff.maxDescendantBMatrixNormAtScale_le_cutoffEnvelope` —
  **unconditional**, depth-uniform, no event and no geometric weight — through
  the `hmem` step and its coefficient-field twin
  `Cutoff.maxDescendantBMatrixNormCoeffFieldAtScale_le_cutoffEnvelope`,
  gives `|b(R;ω)| ≤ 4dν^{-1}E(ω)²` at every descendant `R` of `□_m`, every
  depth, every `ω`; (2) the sharp `lowerLeft` bound below; (3) the
  deterministic `lowerRight` envelope below; hence (4) `|(σ_*^{-1}κ)(R;ω)| ≤
  4dν^{-1}E(ω)` on the **whole** sample space, and every natural power of `E`
  is integrable at `(Cutoff.cutoffSampleLaw M).toMeasure`
  (`Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow`, from
  `Cutoff.integrable_cutoffLocalControl_pow` and
  `Cutoff.coefficientCutoffCubeEllipticityUpper_le_majorant`).  Both target
  observables are already integrated against that exact measure
  (`coarseMatrixVariationBlock`, `coarseScaleSeparationBlock` and
  `exists_integral_cutoffResponseJ_centralChild_le_expectationDisplay` in
  `CombineExpectation.lean`); a `RegCoeffField`-side carrier that needs a
  transfer has the proved pattern `Cutoff.coefficientCutoffLaw_eq_map`
  (`Cutoff/Law.lean`) with `integrable_map_measure` and `Integrable.mono'`, as
  in `Cutoff.integrable_LambdaSqCoeffField_pow_cutoffLaw`, and the corridor
  weight `∑_{n∈[L,m]}3^{-(m-n)}` is a finite deterministic factor.  What is to
  be produced is `Integrable (CombineExpectation.coarseScaleSeparationBlock M m
  L e) (Cutoff.cutoffSampleLaw M).toMeasure` and its
  `coarseMatrixVariationBlock` twin.  The event-dependent route of Part B
  performs steps (1)--(3) and then *discards* the unconditional
  envelope in favour of the `Λ²` extraction plus the good event.  What remains
  true is the item-**(3)**-scoped observation: item (3) asks for a
  **deterministic** constant `K`, and the deterministic route for the `κ`
  channel does not produce one, because the step-(1) envelope is the random
  `E(ω)`.  Integrable is not bounded; the two items ask different questions.
* Items (5), (6) and (7) — the corridor summation, the anchor wiring, and the
  `+Cδ₁²` absorption — are not performed.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Section3
open scoped MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The diagonal gauge -/

omit [NeZero d] in
/-- **Re-derivation of the seam's first gauge lemma.**  The continuous
functional-calculus square root of the constant full block matrix of the
isotropic comparator `σ𝟙` is the diagonal multiplier
`diag(σ^{1/2}𝟙, σ^{-1/2}𝟙)`.

This is a verbatim re-derivation of the `private`
`Provider.Homogenization.cfcSqrt_isotropicComparator_eq_diagonal`
(`VarianceCarrierSeam.lean`); the re-derivation is forced by that lemma's
visibility and is disclosed in the module docstring. -/
private theorem cfcSqrt_isotropicComparatorMatrix_eq_diagonal
    (sigma : Observable.PositiveScalar) :
    CFC.sqrt (Ch02.constantFullBlockMatrix
        (Observable.isotropicComparatorMatrix (d := d) sigma)) =
      Matrix.diagonal
        (Ch05.Section56.scalarFullBlockSqrtDiag (d := d)
          (sigma : ℝ) (sigma : ℝ)) := by
  change Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) (sigma : ℝ)) = _
  exact
    Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
      sigma.property

omit [NeZero d] in
/-- Entries of a two-sided diagonal conjugation. -/
private theorem diagonal_mul_mul_diagonal_apply (r : BlockCoord d → ℝ)
    (X : FullBlockMat d) (alpha beta : BlockCoord d) :
    (Matrix.diagonal r * X * Matrix.diagonal r) alpha beta =
      r alpha * X alpha beta * r beta := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
    Finset.sum_ite_eq', mul_comm, mul_left_comm]

omit [NeZero d] in
/-- **The conjugated matrix, entrywise.**  At the isotropic comparator
normalizer the starred fluctuation matrix is the diagonal gauge conjugation of
the reflected difference `𝐑(𝐀(U;a) - 𝐂)𝐑`. -/
private theorem starredFluctuationMatrix_isotropicComparatorMatrix_apply
    (sigma : Observable.PositiveScalar) (C : BlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) (alpha beta : BlockCoord d) :
    starredFluctuationMatrix
        (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
        C U a alpha beta =
      Ch05.Section56.scalarFullBlockSqrtDiag (d := d) (sigma : ℝ) (sigma : ℝ) alpha *
        ((toFullBlockMat (starredInverseCoarseBlockMatrix U a) -
          toFullBlockMat (blockReflect C)) alpha beta) *
        Ch05.Section56.scalarFullBlockSqrtDiag (d := d) (sigma : ℝ) (sigma : ℝ) beta := by
  unfold starredFluctuationMatrix
  rw [cfcSqrt_isotropicComparatorMatrix_eq_diagonal]
  exact diagonal_mul_mul_diagonal_apply _ _ alpha beta

/-! ## The two row readings -/

omit [NeZero d] in
/-- **Primal row reading.**  The upper half of `Δ(e,0)` is
`σ · (𝐀_{lowerRight} - 𝐂_{lowerRight})e`. -/
private theorem mulVec_starredFluctuationMatrix_primalLoad_inl
    (sigma : Observable.PositiveScalar) (C : BlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) (e : Vec d) (i : Fin d) :
    Matrix.mulVec
        (starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a)
        (toFullBlockVec (e, (0 : Vec d))) (Sum.inl i) =
      (sigma : ℝ) *
        matVecMul ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) e i := by
  have hsq : Real.sqrt (sigma : ℝ) * Real.sqrt (sigma : ℝ) = (sigma : ℝ) :=
    Real.mul_self_sqrt sigma.property.le
  have hterm : ∀ j : Fin d,
      starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a (Sum.inl i) (Sum.inl j) *
        toFullBlockVec (e, (0 : Vec d)) (Sum.inl j) =
      (sigma : ℝ) *
        (((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) i j * e j) := by
    intro j
    rw [starredFluctuationMatrix_isotropicComparatorMatrix_apply]
    change Real.sqrt (sigma : ℝ) *
        (((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) i j) *
        Real.sqrt (sigma : ℝ) * e j = _
    calc Real.sqrt (sigma : ℝ) *
          (((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) i j) *
          Real.sqrt (sigma : ℝ) * e j
        = (Real.sqrt (sigma : ℝ) * Real.sqrt (sigma : ℝ)) *
            (((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) i j * e j) := by
          ring
      _ = _ := by rw [hsq]
  have hzero : ∀ j : Fin d,
      starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a (Sum.inl i) (Sum.inr j) *
        toFullBlockVec (e, (0 : Vec d)) (Sum.inr j) = 0 := by
    intro j
    change _ * (0 : ℝ) = 0
    ring
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Finset.sum_congr rfl (fun j _ => hterm j),
    Finset.sum_congr rfl (fun j _ => hzero j)]
  simp only [Finset.sum_const_zero, add_zero, ← Finset.mul_sum]
  rfl

omit [NeZero d] in
/-- **Dual row reading.**  The upper half of `Δ(0,e)` is
`(𝐀_{lowerLeft} - 𝐂_{lowerLeft})e`, with no gauge weight: the two gauge
factors `σ^{1/2}` and `σ^{-1/2}` cancel on the off-diagonal block. -/
private theorem mulVec_starredFluctuationMatrix_dualLoad_inl
    (sigma : Observable.PositiveScalar) (C : BlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) (e : Vec d) (i : Fin d) :
    Matrix.mulVec
        (starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a)
        (toFullBlockVec ((0 : Vec d), e)) (Sum.inl i) =
      matVecMul ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) e i := by
  have hne : Real.sqrt (sigma : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr sigma.property)
  have hterm : ∀ j : Fin d,
      starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a (Sum.inl i) (Sum.inr j) *
        toFullBlockVec ((0 : Vec d), e) (Sum.inr j) =
      ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) i j * e j := by
    intro j
    rw [starredFluctuationMatrix_isotropicComparatorMatrix_apply]
    change Real.sqrt (sigma : ℝ) *
        (((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) i j) *
        (Real.sqrt (sigma : ℝ))⁻¹ * e j = _
    field_simp
  have hzero : ∀ j : Fin d,
      starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a (Sum.inl i) (Sum.inl j) *
        toFullBlockVec ((0 : Vec d), e) (Sum.inl j) = 0 := by
    intro j
    change _ * (0 : ℝ) = 0
    ring
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Finset.sum_congr rfl (fun j _ => hzero j),
    Finset.sum_congr rfl (fun j _ => hterm j)]
  simp only [Finset.sum_const_zero, zero_add]
  rfl

/-! ## The operator-norm transfer -/

omit [NeZero d] in
private theorem vecNormSq_eq_sum_sq (x : Vec d) :
    vecNormSq x = ∑ i, (x i) ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

omit [NeZero d] in
private theorem norm_sq_toLp_blockCoord (v : FullBlockVec d) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (BlockCoord d))‖ ^ 2 =
      ∑ alpha, (v alpha) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

omit [NeZero d] in
/-- Coordinate form of `ContinuousLinearMap.le_opNorm` on the doubled Euclidean
space.  Re-derivation of the CoarseGraining-private
`fullBlockMat_mulVec_norm_sq_le_operatorNorm_sq`
(`Section54/VarianceBoundGoodScale/NormalizedBlocks.lean`). -/
private theorem sum_sq_mulVec_le (X : FullBlockMat d) (v : FullBlockVec d) :
    ∑ alpha, (Matrix.mulVec X v alpha) ^ 2 ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X‖ ^ 2 *
        ∑ alpha, (v alpha) ^ 2 := by
  have hap :
      Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X
          (WithLp.toLp 2 v : EuclideanSpace ℝ (BlockCoord d)) =
        (WithLp.toLp 2 (Matrix.mulVec X v) : EuclideanSpace ℝ (BlockCoord d)) := by
    simp [Matrix.toEuclideanCLM_toLp]
  have hle :=
    (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) X).le_opNorm
      (WithLp.toLp 2 v : EuclideanSpace ℝ (BlockCoord d))
  rw [hap] at hle
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [mul_pow, norm_sq_toLp_blockCoord, norm_sq_toLp_blockCoord] at hsq
  exact hsq

omit [NeZero d] in
/-- **Converse of `Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq`.**
A uniform vector bound produces the operator-norm bound. -/
private theorem matrixOperatorNorm_le_of_vecNormSq_matVecMul_le {N : Mat d} {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ x : Vec d, vecNormSq (matVecMul N x) ≤ K ^ 2 * vecNormSq x) :
    Ch02.matrixOperatorNorm N ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK ?_
  intro x
  set xi : Vec d := x.ofLp with hxi
  have hx : x = (WithLp.toLp 2 xi : EuclideanSpace ℝ (Fin d)) := by
    simp [hxi]
  have hnorm : vecNormSq xi = ‖x‖ ^ 2 := by
    rw [← Ch02.vecNorm_sq_eq_vecNormSq]
    simp [Ch02.vecNorm, hxi]
  have hsq :
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) N x‖ ^ 2 ≤ (K * ‖x‖) ^ 2 := by
    have hvalue :
        ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) N x‖ ^ 2 =
          vecNormSq (matVecMul N xi) := by
      rw [← Ch02.vecNorm_sq_eq_vecNormSq, hx]
      simp [Ch02.vecNorm, Matrix.toEuclideanCLM_toLp, matVecMul, Matrix.mulVec,
        dotProduct]
    rw [hvalue, mul_pow, ← hnorm]
    exact h xi
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg x))).mp hsq

/-! ## The carrier bridge -/

omit [NeZero d] in
/-- **The carrier bridge, lower-right channel.**  At the isotropic comparator
normalizer `𝐁(σ)`, the squared Euclidean operator norm of the `σ_*^{-1}`
channel of `𝐀(U;a) - 𝐂`, weighted by `σ²`, is below the squared operator norm
of the full starred fluctuation matrix.

The weight `σ²` is the exact gauge weight of the manuscript's conjugation: the
load `(e,0)` reads the lower-right block twice through `σ^{1/2}`. -/
theorem sq_mul_sq_matrixOperatorNorm_lowerRight_sub_le_starredFluctuationOperatorNormSq
    (sigma : Observable.PositiveScalar) (C : BlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) :
    (sigma : ℝ) ^ 2 *
        Ch02.matrixOperatorNorm
          ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) ^ 2 ≤
      starredFluctuationOperatorNormSq
        (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
        C U a := by
  set S : ℝ :=
    starredFluctuationOperatorNormSq
      (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
      C U a with hS
  have hS0 : 0 ≤ S := by
    rw [hS, starredFluctuationOperatorNormSq]
    positivity
  have hsigma : (0 : ℝ) < (sigma : ℝ) := sigma.property
  have hstep : ∀ e : Vec d,
      (sigma : ℝ) ^ 2 *
          vecNormSq
            (matVecMul ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) e) ≤
        S * vecNormSq e := by
    intro e
    have hraw :=
      sum_sq_mulVec_le
        (starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a)
        (toFullBlockVec (e, (0 : Vec d)))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hraw
    have hupper : ∀ i : Fin d,
        (Matrix.mulVec
            (starredFluctuationMatrix
              (Ch02.constantFullBlockMatrix
                (Observable.isotropicComparatorMatrix sigma)) C U a)
            (toFullBlockVec (e, (0 : Vec d))) (Sum.inl i)) ^ 2 =
          (sigma : ℝ) ^ 2 *
            (matVecMul
              ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) e i) ^ 2 := by
      intro i
      rw [mulVec_starredFluctuationMatrix_primalLoad_inl]
      ring
    have hlower : ∀ i : Fin d,
        (0 : ℝ) ≤
          (Matrix.mulVec
            (starredFluctuationMatrix
              (Ch02.constantFullBlockMatrix
                (Observable.isotropicComparatorMatrix sigma)) C U a)
            (toFullBlockVec (e, (0 : Vec d))) (Sum.inr i)) ^ 2 := fun i => sq_nonneg _
    have hloadl : ∀ i : Fin d,
        (toFullBlockVec (e, (0 : Vec d)) (Sum.inl i)) ^ 2 = (e i) ^ 2 := fun _ => rfl
    have hloadr : ∀ i : Fin d,
        (toFullBlockVec (e, (0 : Vec d)) (Sum.inr i)) ^ 2 = 0 := by
      intro i
      change (0 : ℝ) ^ 2 = 0
      ring
    rw [Finset.sum_congr rfl (fun i _ => hupper i),
      Finset.sum_congr rfl (fun i _ => hloadl i),
      Finset.sum_congr rfl (fun i _ => hloadr i)] at hraw
    rw [← Finset.mul_sum] at hraw
    simp only [Finset.sum_const_zero, add_zero] at hraw
    rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
    have hnn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hlower i)
    have hSeq :
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (starredFluctuationMatrix
            (Ch02.constantFullBlockMatrix
              (Observable.isotropicComparatorMatrix sigma)) C U a)‖ ^ 2 = S := by
      rw [hS, starredFluctuationOperatorNormSq]
    rw [hSeq] at hraw
    linarith
  have hK : (0 : ℝ) ≤ Real.sqrt S / (sigma : ℝ) :=
    div_nonneg (Real.sqrt_nonneg S) hsigma.le
  have hKsq : (Real.sqrt S / (sigma : ℝ)) ^ 2 = S / (sigma : ℝ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hS0]
  have hbound :
      Ch02.matrixOperatorNorm
        ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) ≤
          Real.sqrt S / (sigma : ℝ) := by
    refine matrixOperatorNorm_le_of_vecNormSq_matVecMul_le hK ?_
    intro x
    have hx := hstep x
    rw [hKsq]
    have hpos : (0 : ℝ) < (sigma : ℝ) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [hx]
  have hsq :=
    pow_le_pow_left₀
      (Ch02.matrixOperatorNorm_nonneg
        ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight)) hbound 2
  rw [hKsq] at hsq
  have hpos : (0 : ℝ) < (sigma : ℝ) ^ 2 := by positivity
  calc
    (sigma : ℝ) ^ 2 *
        Ch02.matrixOperatorNorm
          ((coarseBlockMatrix U a.toFun).lowerRight - C.lowerRight) ^ 2
        ≤ (sigma : ℝ) ^ 2 * (S / (sigma : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hpos.le
    _ = S := by field_simp

omit [NeZero d] in
/-- **The carrier bridge, lower-left channel.**  The `σ_*^{-1}κ` channel of
`𝐀(U;a) - 𝐂` carries **no** gauge weight: the load `(0,e)` reads the
off-diagonal block once through `σ^{-1/2}` and once through `σ^{1/2}`.  This is
the printed asymmetry of `(e.initial.JL.bound)` -- weight `σ_L²` on the
`σ_*^{-1}` variances, weight `1` on the `σ_*^{-1}κ` variances. -/
theorem sq_matrixOperatorNorm_lowerLeft_sub_le_starredFluctuationOperatorNormSq
    (sigma : Observable.PositiveScalar) (C : BlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) :
    Ch02.matrixOperatorNorm
        ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) ^ 2 ≤
      starredFluctuationOperatorNormSq
        (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
        C U a := by
  set S : ℝ :=
    starredFluctuationOperatorNormSq
      (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
      C U a with hS
  have hS0 : 0 ≤ S := by
    rw [hS, starredFluctuationOperatorNormSq]
    positivity
  have hstep : ∀ e : Vec d,
      vecNormSq
          (matVecMul ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) e) ≤
        S * vecNormSq e := by
    intro e
    have hraw :=
      sum_sq_mulVec_le
        (starredFluctuationMatrix
          (Ch02.constantFullBlockMatrix (Observable.isotropicComparatorMatrix sigma))
          C U a)
        (toFullBlockVec ((0 : Vec d), e))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hraw
    have hupper : ∀ i : Fin d,
        (Matrix.mulVec
            (starredFluctuationMatrix
              (Ch02.constantFullBlockMatrix
                (Observable.isotropicComparatorMatrix sigma)) C U a)
            (toFullBlockVec ((0 : Vec d), e)) (Sum.inl i)) ^ 2 =
          (matVecMul
            ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) e i) ^ 2 := by
      intro i
      rw [mulVec_starredFluctuationMatrix_dualLoad_inl]
    have hlower : ∀ i : Fin d,
        (0 : ℝ) ≤
          (Matrix.mulVec
            (starredFluctuationMatrix
              (Ch02.constantFullBlockMatrix
                (Observable.isotropicComparatorMatrix sigma)) C U a)
            (toFullBlockVec ((0 : Vec d), e)) (Sum.inr i)) ^ 2 := fun i => sq_nonneg _
    have hloadl : ∀ i : Fin d,
        (toFullBlockVec ((0 : Vec d), e) (Sum.inl i)) ^ 2 = 0 := by
      intro i
      change (0 : ℝ) ^ 2 = 0
      ring
    have hloadr : ∀ i : Fin d,
        (toFullBlockVec ((0 : Vec d), e) (Sum.inr i)) ^ 2 = (e i) ^ 2 := fun _ => rfl
    rw [Finset.sum_congr rfl (fun i _ => hupper i),
      Finset.sum_congr rfl (fun i _ => hloadl i),
      Finset.sum_congr rfl (fun i _ => hloadr i)] at hraw
    simp only [Finset.sum_const_zero, zero_add] at hraw
    rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
    have hnn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hlower i)
    have hSeq :
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (starredFluctuationMatrix
            (Ch02.constantFullBlockMatrix
              (Observable.isotropicComparatorMatrix sigma)) C U a)‖ ^ 2 = S := by
      rw [hS, starredFluctuationOperatorNormSq]
    rw [hSeq] at hraw
    linarith
  have hbound :
      Ch02.matrixOperatorNorm
        ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft) ≤ Real.sqrt S := by
    refine matrixOperatorNorm_le_of_vecNormSq_matVecMul_le (Real.sqrt_nonneg S) ?_
    intro x
    rw [Real.sq_sqrt hS0]
    exact hstep x
  have hsq :=
    pow_le_pow_left₀
      (Ch02.matrixOperatorNorm_nonneg
        ((coarseBlockMatrix U a.toFun).lowerLeft - C.lowerLeft)) hbound 2
  rwa [Real.sq_sqrt hS0] at hsq

/-! ## The genuine-law instances -/

omit [NeZero d] in
/-- **The `σ_*^{-1}` variance carrier under the corridor observable.**  The
variance-split integrand `|σ_*^{-1}(R;a) - σ_{L,*}^{-1}(□_n)|²`, weighted by the
printed `σ_L²`, is below the Step-3 corridor observable at the same centering
scale, sample by sample and at every cube. -/
theorem coefficientCutoffLaw_sq_sigmaBar_mul_starInverseCenteredFluctuationSq_le
    (M : ABKModel d) (L n : ℤ) (R : TriadicCube d) (a : RegCoeffField d) :
    (Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseCenteredFluctuationSq M L n R a ≤
      starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
        (cubeSet R) a :=
  sq_mul_sq_matrixOperatorNorm_lowerRight_sub_le_starredFluctuationOperatorNormSq
    (Annealed.sigmaBar M L) _ _ _

omit [NeZero d] in
/-- **The `σ_*^{-1}κ` variance carrier under the corridor observable.**  Same
statement for the lower-left channel, at weight `1`. -/
theorem coefficientCutoffLaw_starInverseKappaCenteredFluctuationSq_le
    (M : ABKModel d) (L n : ℤ) (R : TriadicCube d) (a : RegCoeffField d) :
    starInverseKappaCenteredFluctuationSq M L n R a ≤
      starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
        (cubeSet R) a :=
  sq_matrixOperatorNorm_lowerLeft_sub_le_starredFluctuationOperatorNormSq
    (Annealed.sigmaBar M L) _ _ _

omit [NeZero d] in
/-- **The left side of `(e.var.bound.astar.withS)` under the corridor observable**.
The printed combination `σ_L² var[σ_{L,*}^{-1}(□_n)] +
var[σ_{L,*}^{-1}(□_n)κ_L(□_n)]` is at most twice the expectation of the Step-3
corridor observable.

The `Integrable` clause is a conditional A obligation in the convention of
`integral_starredFluctuationNormSq_le_descendantAndResponseBounds`;
see the module docstring. -/
theorem coefficientCutoffLaw_sq_sigmaBar_mul_starInverseVarianceAtScale_add_le
    (M : ABKModel d) (L n : ℤ)
    (hint : Integrable
      (fun a => starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
        (cubeSet (originCube d n)) a) (Cutoff.coefficientCutoffLaw M L)) :
    (Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n +
        starInverseKappaVarianceAtScale M L n ≤
      2 * ∫ a, starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
        (cubeSet (originCube d n)) a ∂(Cutoff.coefficientCutoffLaw M L) := by
  have hlr :
      (Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n ≤
        ∫ a, starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (cubeSet (originCube d n)) a ∂(Cutoff.coefficientCutoffLaw M L) := by
    rw [starInverseVarianceAtScale, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => ?_) hint
      (Filter.Eventually.of_forall fun a =>
        coefficientCutoffLaw_sq_sigmaBar_mul_starInverseCenteredFluctuationSq_le
          M L n (originCube d n) a)
    have hcarrier : (0 : ℝ) ≤ starInverseCenteredFluctuationSq M L n (originCube d n) a := by
      rw [starInverseCenteredFluctuationSq]
      positivity
    have hsigma : (0 : ℝ) ≤ (Annealed.sigmaBar M L : ℝ) ^ 2 := sq_nonneg _
    exact mul_nonneg hsigma hcarrier
  have hll :
      starInverseKappaVarianceAtScale M L n ≤
        ∫ a, starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (cubeSet (originCube d n)) a ∂(Cutoff.coefficientCutoffLaw M L) := by
    rw [starInverseKappaVarianceAtScale]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => ?_) hint
      (Filter.Eventually.of_forall fun a =>
        coefficientCutoffLaw_starInverseKappaCenteredFluctuationSq_le
          M L n (originCube d n) a)
    rw [starInverseKappaCenteredFluctuationSq]
    positivity
  linarith

/-! ## The Step-3 display `(e.var.bound.astar.withS)` -/

/-- **`(e.var.bound.astar.withS)`, at the genuine coefficient cutoff law.**
Composing the carrier bridge with the proved Step-3 corridor variance bound
`exists_coefficientCutoff_finiteCorridor_starredFluctuationVariance_bound`
(`CombineFiniteCarrierTransport.lean`) gives the printed left side

`σ_L² var[σ_{L,*}^{-1}(□_n)] + var[σ_{L,*}^{-1}(□_n)κ_L(□_n)]`

below `2 C_var δ (δ + 3^{-d(n-L)})`, where `δ` is the corridor's own two-term
amplitude `E²γ + exp(-2E^{-3}γ^{-1})`.  The printed constant `C` is `2 C_var`.

This **partially supports** and does **not** realize the printed display: `δ`
is *strictly larger* than the printed `δ₁ := C E²γ`, so the conclusion is a
weaker form; the `Integrable` clause remains open; and this theorem has, as
proved, no Lean consumer.  What it does complete is the *left-hand half* — it
is the first proved statement whose left side is literally the printed variance
sum, the proved transport form carrying the starred integral there instead.

The last, `Integrable`, is the conditional obligation described there:
without it the proved corridor bound is vacuous, since a non-integrable Bochner
integral is `0`.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_coefficientCutoff_finiteCorridor_starInverseVariance_withS_bound :
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
              Integrable
                (fun a => starredFluctuationOperatorNormSq
                  (cutoffComparatorNormalizer M L)
                  (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
                  (cubeSet (originCube d n)) a) (Cutoff.coefficientCutoffLaw M L) →
                (Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L n +
                    starInverseKappaVarianceAtScale M L n ≤
                  2 * Cvar *
                      ((E : ℝ) ^ 2 * M.gamma +
                        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
                      (((E : ℝ) ^ 2 * M.gamma +
                          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
                        Real.rpow 3 (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))) := by
  obtain ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, hcorridor⟩ :=
    exists_coefficientCutoff_finiteCorridor_starredFluctuationVariance_bound d
  refine ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, ?_⟩
  intro M m E hLower epsilon hepsilon hgamma L hseparation n hn hint
  have hraw := hcorridor M m E hLower epsilon hepsilon hgamma L hseparation n hn
  have hCn :
      Ch04.scalarAnnealedBlockMatrixAtScale
          (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L)
          (Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L)
          (n - L - (Cutoff.cutoffRelativeNormalizationShift d : ℤ)) =
        Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n :=
    scalarAnnealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center_eq M L n
  have hstep :
      ∫ a, starredFluctuationOperatorNormSq (cutoffComparatorNormalizer M L)
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
          (cubeSet (originCube d n)) a ∂(Cutoff.coefficientCutoffLaw M L) ≤
        Cvar *
            ((E : ℝ) ^ 2 * M.gamma +
              Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
            (((E : ℝ) ^ 2 * M.gamma +
                Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
              Real.rpow 3 (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))) := by
    rw [← hCn]
    exact hraw
  have hbridge :=
    coefficientCutoffLaw_sq_sigmaBar_mul_starInverseVarianceAtScale_add_le M L n hint
  linarith

/-! ## Two inputs of the `hK` producer -/

open Ch05.Section52 in
/-- **The deterministic descendant envelope of the `σ_*^{-1}` channel.**  For
the genuine coefficient cutoff, the Euclidean operator norm of the lower-right
coarse block is at most `4dν^{-1}` at *every* descendant of *every* cube, with
no event and no random envelope: the bound is the molecular coercivity alone.

This is
`Cutoff.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_le_cutoffCoercivity`
(the ambient form of
`Cutoff.maxDescendantSigmaStarInvMatrixNormAtScale_le_cutoffCoercivity`) read
on the `coarseBlockMatrix` carrier through the *public* CoarseGraining
`Ch05.Section52` sup identity for the lower-right block
(identifying the descendant inverse-ellipticity maximum with the lower-right-block supremum),
applied below.  It is the `σ_*^{-1}` half of the `hK` producer (3); the `κ`
half is not supplied (see the module docstring). -/
theorem matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (j : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ))) :
    Ch02.matrixOperatorNorm
        (coarseBlockMatrix (cubeSet R)
          (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight ≤
      4 * (d : ℝ) * M.nu⁻¹ := by
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hsup :=
    maxDescendantSigmaStarInvMatrixNormCoeffField_eq_sup_lowerRight
      (Cutoff.coefficientCutoff_aelocallyUniformlyElliptic M L omega) Q hk
  have hmem :
      Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R)
            (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight ≤
        (descendantsAtScale Q (Q.scale - (j : ℤ))).sup'
          (descendantsAtScale_nonempty Q hk)
          (fun S => Ch02.matrixNorm
            (coarseBlockMatrix (cubeSet S)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight) :=
    Finset.le_sup'
      (fun S => Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet S)
          (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight) hR
  rw [← hsup] at hmem
  exact hmem.trans
    (Cutoff.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_le_cutoffCoercivity
      M L omega Q j)

/-! ## The positive semidefinite off-diagonal block bound -/

omit [NeZero d] in
/-- Transposition preserves the Euclidean operator norm of a real matrix. -/
private theorem matrixOperatorNorm_matTranspose (A : Mat d) :
    Ch02.matrixOperatorNorm (matTranspose A) = Ch02.matrixOperatorNorm A := by
  have h : matTranspose A = star A := by
    ext i j
    simp [matTranspose, Matrix.transpose_apply, Matrix.star_apply, star_trivial]
  unfold Ch02.matrixOperatorNorm
  rw [h, map_star]
  exact norm_star (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A)

omit [NeZero d] in
/-- The quadratic form of a positive definite block matrix is nonnegative,
including at zero. -/
private theorem blockQuadratic_nonneg_of_blockPosDef {A : BlockMat d}
    (hA : Ch02.BlockPosDef A) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  by_cases hX : X = 0
  · subst hX
    simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_right]
  · exact (hA X hX).le

omit [NeZero d] in
/-- The off-diagonal bilinear form of a symmetric positive definite doubled
block matrix is bounded by the geometric mean of the two diagonal operator
norms. -/
private theorem abs_vecDot_upperRight_le_sqrt_diag_mul_vecNorm {A : BlockMat d}
    (hSymm : IsSymmetricBlockMat A) (hPos : Ch02.BlockPosDef A) (x y : Vec d) :
    |vecDot x (matVecMul A.upperRight y)| ≤
      Real.sqrt
          (Ch02.matrixOperatorNorm A.upperLeft * Ch02.matrixOperatorNorm A.lowerRight) *
        (Ch02.vecNorm x * Ch02.vecNorm y) := by
  set X : BlockVec d := (x, (0 : Vec d)) with hXdef
  set Y : BlockVec d := ((0 : Vec d), y) with hYdef
  have hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul A Z) :=
    fun Z => blockQuadratic_nonneg_of_blockPosDef hPos Z
  have hcs :=
    abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat hSymm hpsd X Y
  have hX : blockVecDot X (blockMatVecMul A X) ≤
      Ch02.matrixOperatorNorm A.upperLeft * vecNormSq x := by
    simpa [hXdef, blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left,
      vecDot_zero_right] using
      ((le_abs_self (vecDot x (matVecMul A.upperLeft x))).trans
        (Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq A.upperLeft x))
  have hY : blockVecDot Y (blockMatVecMul A Y) ≤
      Ch02.matrixOperatorNorm A.lowerRight * vecNormSq y := by
    simpa [hYdef, blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left,
      vecDot_zero_right] using
      ((le_abs_self (vecDot y (matVecMul A.lowerRight y))).trans
        (Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq A.lowerRight y))
  have hX0 : 0 ≤ blockVecDot X (blockMatVecMul A X) := hpsd X
  have hY0 : 0 ≤ blockVecDot Y (blockMatVecMul A Y) := hpsd Y
  have hB0 : 0 ≤ Ch02.matrixOperatorNorm A.upperLeft := Ch02.matrixOperatorNorm_nonneg _
  have hS0 : 0 ≤ Ch02.matrixOperatorNorm A.lowerRight := Ch02.matrixOperatorNorm_nonneg _
  have hnx0 : 0 ≤ vecNormSq x := vecNormSq_nonneg _
  have hprod :
      blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) ≤
        (Ch02.matrixOperatorNorm A.upperLeft * vecNormSq x) *
          (Ch02.matrixOperatorNorm A.lowerRight * vecNormSq y) :=
    mul_le_mul hX hY hY0 (mul_nonneg hB0 hnx0)
  have hcs_sq : |blockVecDot X (blockMatVecMul A Y)| ^ 2 ≤
      blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) := by
    calc
      |blockVecDot X (blockMatVecMul A Y)| ^ 2 ≤
          (Real.sqrt (blockVecDot X (blockMatVecMul A X)) *
            Real.sqrt (blockVecDot Y (blockMatVecMul A Y))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) := by
        rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
  have hsq : |vecDot x (matVecMul A.upperRight y)| ^ 2 ≤
      (Real.sqrt
          (Ch02.matrixOperatorNorm A.upperLeft * Ch02.matrixOperatorNorm A.lowerRight) *
        (Ch02.vecNorm x * Ch02.vecNorm y)) ^ 2 := by
    calc
      |vecDot x (matVecMul A.upperRight y)| ^ 2 =
          |blockVecDot X (blockMatVecMul A Y)| ^ 2 := by
        simp [hXdef, hYdef, blockMatVecMul, blockVecDot, matVecMul_zero,
          vecDot_zero_left]
      _ ≤ (Ch02.matrixOperatorNorm A.upperLeft * vecNormSq x) *
            (Ch02.matrixOperatorNorm A.lowerRight * vecNormSq y) := hcs_sq.trans hprod
      _ = (Real.sqrt
              (Ch02.matrixOperatorNorm A.upperLeft *
                Ch02.matrixOperatorNorm A.lowerRight) *
            (Ch02.vecNorm x * Ch02.vecNorm y)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hB0 hS0),
          ← Ch02.vecNorm_sq_eq_vecNormSq x, ← Ch02.vecNorm_sq_eq_vecNormSq y]
        ring
  exact (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Ch02.vecNorm_nonneg _) (Ch02.vecNorm_nonneg _)))).mp hsq

omit [NeZero d] in
/-- **Positive block Cauchy--Schwarz, upper-right block.**  For a symmetric
positive definite doubled block matrix the upper-right block has operator norm
at most the geometric mean of the two diagonal block norms. -/
theorem matrixOperatorNorm_upperRight_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef
    {A : BlockMat d} (hSymm : IsSymmetricBlockMat A) (hPos : Ch02.BlockPosDef A) :
    Ch02.matrixOperatorNorm A.upperRight ≤
      Real.sqrt
        (Ch02.matrixOperatorNorm A.upperLeft * Ch02.matrixOperatorNorm A.lowerRight) := by
  set c : ℝ :=
    Real.sqrt
      (Ch02.matrixOperatorNorm A.upperLeft * Ch02.matrixOperatorNorm A.lowerRight) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  refine matrixOperatorNorm_le_of_vecNormSq_matVecMul_le hc0 ?_
  intro y
  have hbil :=
    abs_vecDot_upperRight_le_sqrt_diag_mul_vecNorm hSymm hPos
      (matVecMul A.upperRight y) y
  have hself : vecNormSq (matVecMul A.upperRight y) ≤
      c * (Ch02.vecNorm (matVecMul A.upperRight y) * Ch02.vecNorm y) := by
    rw [show vecDot (matVecMul A.upperRight y) (matVecMul A.upperRight y) =
        vecNormSq (matVecMul A.upperRight y) from rfl,
      abs_of_nonneg (vecNormSq_nonneg _)] at hbil
    simpa [hc] using hbil
  have hvec : Ch02.vecNorm (matVecMul A.upperRight y) ≤ c * Ch02.vecNorm y := by
    by_cases hz : Ch02.vecNorm (matVecMul A.upperRight y) = 0
    · rw [hz]
      exact mul_nonneg hc0 (Ch02.vecNorm_nonneg _)
    · have hz0 : 0 < Ch02.vecNorm (matVecMul A.upperRight y) :=
        lt_of_le_of_ne (Ch02.vecNorm_nonneg _) (Ne.symm hz)
      rw [← Ch02.vecNorm_sq_eq_vecNormSq] at hself
      nlinarith [hself]
  have hsq :=
    pow_le_pow_left₀ (Ch02.vecNorm_nonneg (matVecMul A.upperRight y)) hvec 2
  rwa [Ch02.vecNorm_sq_eq_vecNormSq, mul_pow, Ch02.vecNorm_sq_eq_vecNormSq] at hsq

omit [NeZero d] in
/-- **Positive block Cauchy--Schwarz, lower-left block.**  This is the exact
statement asked for (3), in its sharp form `|A_{lowerLeft}|² ≤ |A_{upperLeft}|
· |A_{lowerRight}|`. -/
theorem matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef
    {A : BlockMat d} (hSymm : IsSymmetricBlockMat A) (hPos : Ch02.BlockPosDef A) :
    Ch02.matrixOperatorNorm A.lowerLeft ≤
      Real.sqrt
        (Ch02.matrixOperatorNorm A.upperLeft * Ch02.matrixOperatorNorm A.lowerRight) := by
  have htranspose : matTranspose A.upperRight = A.lowerLeft := by
    ext i j
    simpa [matTranspose, Matrix.transpose_apply, blockMatEntry] using
      (hSymm (Sum.inr i) (Sum.inl j)).symm
  rw [← htranspose, matrixOperatorNorm_matTranspose]
  exact matrixOperatorNorm_upperRight_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef
    hSymm hPos

end

end Algsuperdiff.Section3.Provider.Homogenization

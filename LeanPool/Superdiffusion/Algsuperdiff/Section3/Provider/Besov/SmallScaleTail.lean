/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.LargeScaleSplit

/-!
# SmallScaleTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The small-scale tail of the Section 3.5 negative-norm lemma

This module establishes the deterministic estimates behind the small-scale part
of the multiscale sum that occurs in the proof of `l.Besov.norms`.  Nothing
about the left-hand side of `e.Besov.norms.gradient`, and nothing about the
status of the lemma, is asserted here.

Fix a cube `Q = \cu_m` and a scale `n < L_0`.  At such a
scale the manuscript makes no use of the response defect: it bounds the
descendant averages `(\nabla v)_{z+\cu_n}` directly by the energy of the
maximizer, pays the multiscale ellipticity weight `3^{2s(m-n)}`, and then sums
the resulting geometric series over the bi-infinite range `n < L_0`.

## Formalization readings

1. *The bi-infinite tail.*  ABK26 sums over `n` from `-\infty` to `L_0-1`.
   That range is enumerated here by `n = L_0 - 1 - i` with `i : \N`, and the
   sum is the unconditional `tsum` of the nonnegative summand.  Summability is
   proved, not assumed; a finite-range corollary over `Finset.range N` is also
   supplied, so a consumer that produces only finite partial sums can use the
   same right-hand side.
2. *The energy carrier.*  `\| \s^{1/2} \nabla v \|^2_{\underline L^2(\cu_m)}`
   is written as the cube average of the Chapter 2 quadratic energy integrand
   of the canonical maximizer, which is literally
   `\fint_{\cu_m} \nabla v \cdot \s \nabla v`.  Its identification with
   `2 J(\cu_m,p,q;\a)` is `e.Jenergyv.nosymm` and is proved here.
3. *The manuscript constant `C`.*  ABK26 prints an unspecified `C`.  The
   explicit values carried below are `2\sqrt 2` for both terms: `\sqrt 2` from
   the pointwise Euclidean inequality `|x-y|^2 \le 2(|x|^2+|y|^2)` used for
   the triangle step, and `2` from the geometric tail `\rho/(1-\rho) \le 2`,
   valid for both discounts `\rho = 3^{-(1-s)}` and `\rho = 3^{-1}` -- the
   first because `s \le 1/2`, the second unconditionally.
4. *The exponent carrier.*  As in `PerScaleDefect.lean`, the manuscript's
   `r \in [1,\infty]` is `Ch02.MultiscaleExponent` together with
   `IsAdmissible`, and no exponent is pinned.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open HCPolySupport.Book.Ch05.Section53

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The energy carrier `\| \s^{1/2}\nabla v \|_{\underline L^2(\cu_m)}` -/

/-- The manuscript quantity `\| \s^{1/2} \nabla v \|^2_{\underline L^2(\cu_m)}`,
written literally as the cube average of the Chapter 2 quadratic energy
integrand `\nabla v \cdot \s \nabla v` of the canonical maximizer on `Q`. -/
def maximizerEnergyL2NormSq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) : ℝ :=
  cubeAverage Q
    (Ch02.variationEnergyIntegrand (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
      (JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q))

/-- **`e.Jenergyv.nosymm` on this carrier.**  The squared energy norm of the
canonical maximizer gradient is twice the Chapter 4 response observable of the
cube.  This is the cube instance of the identity for the Chapter 4 dependent
family; the node's quantifier over every admissible bounded Lipschitz `U` is
untouched, and the mathematics is upstream
(`responseJOnCube_eq_cubeAverage_topHalfEnergy` in CoarseGraining). -/
theorem maximizerEnergyL2NormSq_eq_two_mul_restrictionResponseJObservableCubeSet
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    maximizerEnergyL2NormSq a ha Q p q =
      2 * Ch04.restrictionResponseJObservableCubeSet Q p q a := by
  have hhalf :
      cubeAverage Q
          (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q) =
        (1 / 2 : ℝ) * maximizerEnergyL2NormSq a ha Q p q := by
    rw [maximizerEnergyL2NormSq, ← cubeAverage_const_mul]
    rfl
  have h :=
    JUpperBoundWeakNorms.responseJOnCube_eq_cubeAverage_topHalfEnergy Q
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q
  rw [JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      a ha Q p q, hhalf] at h
  linarith [h]

theorem maximizerEnergyL2NormSq_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) :
    0 ≤ maximizerEnergyL2NormSq a ha Q p q := by
  rw [maximizerEnergyL2NormSq_eq_two_mul_restrictionResponseJObservableCubeSet a ha Q p q,
    ← JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      a ha Q p q]
  have := Ch02.responseJ_nonneg (Ch02.cubeDomain Q)
    ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q
  linarith

/-- The manuscript quantity `\| \s^{1/2} \nabla v \|_{\underline L^2(\cu_m)}`. -/
def maximizerEnergyL2Norm (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) : ℝ :=
  Real.sqrt (maximizerEnergyL2NormSq a ha Q p q)

omit [NeZero d] in
theorem maximizerEnergyL2Norm_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) :
    0 ≤ maximizerEnergyL2Norm a ha Q p q :=
  Real.sqrt_nonneg _

theorem sq_maximizerEnergyL2Norm (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) :
    maximizerEnergyL2Norm a ha Q p q ^ 2 = maximizerEnergyL2NormSq a ha Q p q :=
  Real.sq_sqrt (maximizerEnergyL2NormSq_nonneg a ha Q p q)

/-! ## The one-scale energy bound -/

omit [NeZero d] in
/-- Nonnegativity of a cube average from an a.e. bound on the cube. -/
private theorem cubeAverage_nonneg_of_ae_nonneg {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : ∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ f x) :
    0 ≤ cubeAverage Q f := by
  unfold cubeAverage
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q)))
    (integral_nonneg_of_ae hf)

omit [NeZero d] in
/-- Nonnegativity of the parent half-energy average on a descendant cube. -/
private theorem cubeAverage_topHalfEnergy_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    0 ≤
      cubeAverage R
        (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q) := by
  have hle : volumeMeasureOn (cubeSet R) ≤ volumeMeasureOn (cubeSet Q) := by
    simpa [volumeMeasureOn] using
      Measure.restrict_mono_set volume (cubeSet_subset_of_mem_descendantsAtDepth hR)
  exact cubeAverage_nonneg_of_ae_nonneg
    ((JUpperBoundWeakNorms.topHalfEnergyDensityOnCube_ae_nonneg_cubeSet Q
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q).filter_mono
      (ae_mono hle))

/-- The one-cube form of `e.energymaps.nonsymm` for the restriction of the parent
maximizer to a descendant cube: the squared gradient average on the descendant
is at most its coarse `|\s_*^{-1}|` times the parent energy average over that
descendant. -/
private theorem vecNormSq_gradientAverage_le_coarseSigmaStarInv (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun) ≤
      Ch02.coarseSigmaStarInvMatrixNorm R
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
        (2 *
          cubeAverage R
            (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q)) := by
  have hraw :=
    Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
      (Ch02.cubeDomain R)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
      (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
        a ha Q hR p q)
  have havg :
      Ch02.averageGradient (Ch02.cubeDomain R)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
          (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
            a ha Q hR p q) =
        Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun := by
    have h1 :
        Ch02.averageGradient (Ch02.cubeDomain R)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
            (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
              a ha Q hR p q) =
          cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q) := by
      funext i
      rw [Ch02.averageGradient, Ch02.averageVec,
        JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
      simp [cubeAverageVec,
        JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube_grad]
    have h2 :
        Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun =
          cubeAverageVec R
            (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q) := by
      simpa [JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube,
        JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube] using!
        Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
          a ha hR p q
    rw [h1, h2]
  have henergy :
      Ch02.variationEnergyValue (Ch02.cubeDomain R)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
          (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
            a ha Q hR p q) =
        2 *
          cubeAverage R
            (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q) := by
    rw [Ch02.variationEnergyValue,
      JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    have hpointwise :
        Ch02.variationEnergyIntegrand (Ch02.cubeDomain R)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
            (JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube
              a ha Q hR p q) =
          fun x =>
            2 *
              JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                p q x := by
      funext x
      simp [Ch02.variationEnergyIntegrand,
        JUpperBoundWeakNorms.parentResponseSolutionOnDependentFamilyRestrictedToCube_grad,
        JUpperBoundWeakNorms.topHalfEnergyDensityOnCube,
        JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube]
    rw [hpointwise, cubeAverage_const_mul]
  rw [havg, henergy] at hraw
  exact hraw

/-- **The first inequality.**  The descendant average of the squared gradient
averages of the parent maximizer is at most the largest coarse `|\s_*^{-1}|`
over those descendants times the squared energy norm.

This is `e.energymaps.nonsymm` applied on each descendant cube to the
restriction of the parent maximizer, followed by the additivity of the energy
average over the partition. -/
theorem descendantsAverage_gradientAverageSq_le_maxSigmaStarInv
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    descendantsAverage Q j
        (fun R =>
          vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun)) ≤
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
        maximizerEnergyL2NormSq a ha Q p q := by
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun) ≤
        (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) * 2) *
          cubeAverage R
            (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q) := by
    intro R hR
    have hbase := vecNormSq_gradientAverage_le_coarseSigmaStarInv a ha Q hR p q
    have hcoarse :
        Ch02.coarseSigmaStarInvMatrixNorm R
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) ≤
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) :=
      Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantNorm_atScale
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (mem_descendantsAtScale_of_mem_descendantsAtDepth hR)
    have hE0 := cubeAverage_topHalfEnergy_nonneg a ha Q hR p q
    nlinarith [hbase, hcoarse, hE0]
  have hEsum :
      descendantsAverage Q j
          (fun R =>
            cubeAverage R
              (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q)) =
        Ch02.responseJ (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q :=
    JUpperBoundWeakNorms.descendantsAverage_topHalfEnergy_eq_responseJ
      Q ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) j p q
  calc
    descendantsAverage Q j
        (fun R =>
          vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun))
        ≤ descendantsAverage Q j
            (fun R =>
              (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) * 2) *
                cubeAverage R
                  (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
                    ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                    p q)) :=
          descendantsAverage_le_descendantsAverage Q j hpoint
    _ = (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) * 2) *
          descendantsAverage Q j
            (fun R =>
              cubeAverage R
                (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q
                  ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                  p q)) :=
          descendantsAverage_smul Q j _ _
    _ = Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
          maximizerEnergyL2NormSq a ha Q p q := by
          rw [hEsum,
            maximizerEnergyL2NormSq_eq_two_mul_restrictionResponseJObservableCubeSet a ha Q p q,
            JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
              a ha Q p q]
          ring

/-- **The one-scale energy bound, at an arbitrary admissible exponent `r \in
[1,\infty]`.** -/
theorem descendantsAverage_gradientAverageSq_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (j : ℕ)
    {s : ℝ} (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible)
    (p q : Vec d) :
    descendantsAverage Q j
        (fun R =>
          vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun)) ≤
      (3 : ℝ) ^ (2 * s * (j : ℝ)) * (Ch04.lambdaSqCoeffField Q s r a)⁻¹ *
        maximizerEnergyL2NormSq a ha Q p q := by
  refine (descendantsAverage_gradientAverageSq_le_maxSigmaStarInv a ha Q j p q).trans ?_
  exact mul_le_mul_of_nonneg_right
    (maxDescendantSigmaStarInv_le_lambdaSqCoeffField_inv a ha Q j hs hr)
    (maximizerEnergyL2NormSq_nonneg a ha Q p q)

/-- The square-root form of the one-scale energy bound. -/
theorem sqrt_descendantsAverage_gradientAverageSq_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (j : ℕ)
    {s : ℝ} (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible)
    (p q : Vec d) :
    Real.sqrt
        (descendantsAverage Q j
          (fun R =>
            vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun))) ≤
      (3 : ℝ) ^ (s * (j : ℝ)) * Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
        maximizerEnergyL2Norm a ha Q p q := by
  have hlam0 : 0 ≤ (Ch04.lambdaSqCoeffField Q s r a)⁻¹ := by
    refine inv_nonneg.mpr ?_
    simp only [Ch04.lambdaSqCoeffField, dite_eq_left ha]
    exact Ch02.lambdaSq_nonneg Q _ hs hr
  set Y : ℝ :=
    (3 : ℝ) ^ (s * (j : ℝ)) * Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
      maximizerEnergyL2Norm a ha Q p q with hY
  have hY0 : 0 ≤ Y := by
    refine mul_nonneg (mul_nonneg ?_ (Real.sqrt_nonneg _)) (maximizerEnergyL2Norm_nonneg a ha Q p q)
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hpow : ((3 : ℝ) ^ (s * (j : ℝ))) ^ 2 = (3 : ℝ) ^ (2 * s * (j : ℝ)) := by
    calc
      ((3 : ℝ) ^ (s * (j : ℝ))) ^ 2 = (3 : ℝ) ^ (s * (j : ℝ) * 2) := by
        simpa [Real.rpow_natCast] using
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (s * (j : ℝ)) (2 : ℝ)).symm
      _ = (3 : ℝ) ^ (2 * s * (j : ℝ)) := by ring_nf
  have hYsq : Y ^ 2 =
      (3 : ℝ) ^ (2 * s * (j : ℝ)) * (Ch04.lambdaSqCoeffField Q s r a)⁻¹ *
        maximizerEnergyL2NormSq a ha Q p q := by
    rw [hY, mul_pow, mul_pow, Real.sq_sqrt hlam0, sq_maximizerEnergyL2Norm, hpow]
  calc
    Real.sqrt
        (descendantsAverage Q j
          (fun R =>
            vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun)))
        ≤ Real.sqrt (Y ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          rw [hYsq]
          exact descendantsAverage_gradientAverageSq_le a ha Q j hs hr p q
    _ = Y := Real.sqrt_sq hY0

/-! ## The triangle step -/

/-- **The triangle step.**  For a fixed depth, the root of the descendant average
of the deviation from the parent comparison vector is controlled by the
one-scale energy bound plus the length of the comparison vector itself. -/
theorem sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le_energy
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) {s : ℝ} (hs : 0 < s)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    Real.sqrt (descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q)) ≤
      Real.sqrt 2 *
          ((3 : ℝ) ^ (s * (j : ℝ)) * Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
            maximizerEnergyL2Norm a ha Q p q) +
        Real.sqrt 2 * Real.sqrt (vecNormSq (coarseScaleSeparation a ha Q p q)) := by
  set A : ℝ :=
    descendantsAverage Q j
      (fun R => vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun))
    with hA
  set B : ℝ := vecNormSq (coarseScaleSeparation a ha Q p q) with hB
  have hA0 : 0 ≤ A :=
    descendantsAverage_nonneg Q j _ fun R _ => vecNormSq_nonneg _
  have hB0 : 0 ≤ B := vecNormSq_nonneg _
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      parentCoarseScaleSeparationDeviationSq a ha Q p q R ≤
        2 * (vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun) +
          B) := by
    intro R _
    exact vecNormSq_sub_le _ _
  have havg : descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q) ≤
      2 * A + 2 * B := by
    calc
      descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q)
          ≤ descendantsAverage Q j
              (fun R =>
                2 * (vecNormSq
                    (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun) + B)) :=
            descendantsAverage_le_descendantsAverage Q j hpoint
      _ = 2 * descendantsAverage Q j
            (fun R =>
              vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun) +
                B) := descendantsAverage_smul Q j 2 _
      _ = 2 * (A + B) := by
            rw [descendantsAverage_add, descendantsAverage_const_eq]
      _ = 2 * A + 2 * B := by ring
  have hsqrtA :
      Real.sqrt A ≤
        (3 : ℝ) ^ (s * (j : ℝ)) * Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
          maximizerEnergyL2Norm a ha Q p q :=
    sqrt_descendantsAverage_gradientAverageSq_le a ha Q j hs hr p q
  calc
    Real.sqrt (descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q))
        ≤ Real.sqrt (2 * A + 2 * B) := Real.sqrt_le_sqrt havg
    _ ≤ Real.sqrt (2 * A) + Real.sqrt (2 * B) :=
          sqrt_add_le_add_sqrt_of_nonneg (by positivity) (by positivity)
    _ = Real.sqrt 2 * Real.sqrt A + Real.sqrt 2 * Real.sqrt B := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ Real.sqrt 2 *
            ((3 : ℝ) ^ (s * (j : ℝ)) * Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
              maximizerEnergyL2Norm a ha Q p q) +
          Real.sqrt 2 * Real.sqrt B :=
          add_le_add (mul_le_mul_of_nonneg_left hsqrtA (Real.sqrt_nonneg 2)) le_rfl

/-! ## The geometric tail -/

/-- Geometric tail sum with the manuscript's constant `2`: for `0 ≤ ρ` with `3ρ ≤
2`, the tail starting at `K+1` is at most `2ρ^K`.  Both discounts, namely
`3^{-(1-s)}` (for `s \le 1/2`) and `3^{-1}`, satisfy the hypothesis. -/
private theorem tsum_pow_shift_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : 3 * ρ ≤ 2) (K : ℕ) :
    ∑' i : ℕ, ρ ^ (K + 1 + i) ≤ 2 * ρ ^ K := by
  have hρ1 : ρ < 1 := by linarith
  have hone : (0 : ℝ) < 1 - ρ := by linarith
  have hsum : ∑' i : ℕ, ρ ^ (K + 1 + i) = ρ ^ (K + 1) * (1 - ρ)⁻¹ := by
    calc
      ∑' i : ℕ, ρ ^ (K + 1 + i) = ∑' i : ℕ, ρ ^ (K + 1) * ρ ^ i := by
        exact tsum_congr fun i => pow_add ρ (K + 1) i
      _ = ρ ^ (K + 1) * ∑' i : ℕ, ρ ^ i := tsum_mul_left
      _ = ρ ^ (K + 1) * (1 - ρ)⁻¹ := by rw [tsum_geometric_of_lt_one hρ0 hρ1]
  have hfrac : ρ * (1 - ρ)⁻¹ ≤ 2 := by
    rw [mul_inv_le_iff₀ hone]
    linarith
  have hK0 : 0 ≤ ρ ^ K := pow_nonneg hρ0 K
  calc
    ∑' i : ℕ, ρ ^ (K + 1 + i) = ρ ^ K * (ρ * (1 - ρ)⁻¹) := by
      rw [hsum, pow_succ]; ring
    _ ≤ ρ ^ K * 2 := mul_le_mul_of_nonneg_left hfrac hK0
    _ = 2 * ρ ^ K := by ring

/-- Summability of the shifted geometric series. -/
private theorem summable_pow_shift (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : 3 * ρ ≤ 2) (K : ℕ) :
    Summable fun i : ℕ => ρ ^ (K + 1 + i) := by
  have hρ1 : ρ < 1 := by linarith
  have := (summable_geometric_of_lt_one hρ0 hρ1).mul_left (ρ ^ (K + 1))
  refine this.congr ?_
  intro i
  exact (pow_add ρ (K + 1) i).symm

/-- The rpow discount at a natural depth is the natural power of the discount
at depth one.  `Real.rpow` is kept opaque to automation; the conversion is done
by hand here and nowhere else. -/
private theorem rpow_natDepth_eq_pow (t : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-t * (j : ℝ)) = ((3 : ℝ) ^ (-t)) ^ j := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

/-- Both manuscript discounts satisfy the geometric hypothesis on the printed
range `s \in (0,1/2]`. -/
private theorem three_mul_rpow_neg_le_two {t : ℝ} (ht : (1 : ℝ) / 2 ≤ t) :
    3 * (3 : ℝ) ^ (-t) ≤ 2 := by
  have hmono : (3 : ℝ) ^ (-t) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hhalf : (3 : ℝ) ^ (-((1 : ℝ) / 2)) = (Real.sqrt 3)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_eq_rpow]
  have hsqrt : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hpos : (0 : ℝ) < Real.sqrt 3 := by linarith
  have hinv : (Real.sqrt 3)⁻¹ ≤ 2 / 3 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith
  rw [hhalf] at hmono
  linarith [hmono.trans hinv]

/-! ## The bi-infinite tail -/

/-- The per-index majorant of the tail summand.  The scale `n = L_0-1-i` has depth
`m-n = K+1+i` with `K = m-L_0`, and the summand is bounded by the two geometric
terms. -/
private theorem smallScale_multiscaleTerm_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible)
    (p q : Vec d) (i : ℕ) :
    (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
        Real.sqrt
          (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      (Real.sqrt 2 *
            (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q)) *
          ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) +
        (Real.sqrt 2 *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) *
          ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i) := by
  have hidx : m - (L₀ - 1 - (i : ℤ)) = (((m - L₀).toNat + 1 + i : ℕ) : ℤ) := by
    have hK : ((m - L₀).toNat : ℤ) = m - L₀ := Int.toNat_of_nonneg (by omega)
    push_cast
    omega
  rw [hidx]
  simp only [Int.toNat_natCast, Int.cast_natCast]
  set j : ℕ := (m - L₀).toNat + 1 + i with hj
  set w : ℝ := (3 : ℝ) ^ (-((j : ℕ) : ℝ)) with hw
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have htri :=
    sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le_energy a ha
      (originCube d m) j hs hr p q
  have hstep := mul_le_mul_of_nonneg_left htri hw0
  refine hstep.trans_eq ?_
  have hw1 :
      w * (3 : ℝ) ^ (s * (j : ℝ)) = (3 : ℝ) ^ (-(1 - s) * (j : ℝ)) :=
    rpow_neg_mul_rpow_mul s _
  have hw2 : w = (3 : ℝ) ^ (-(1 : ℝ) * (j : ℝ)) := by
    rw [hw]
    congr 1
    ring
  have hpow1 : (3 : ℝ) ^ (-(1 - s) * (j : ℝ)) = ((3 : ℝ) ^ (-(1 - s))) ^ j :=
    rpow_natDepth_eq_pow (1 - s) j
  have hpow2 : (3 : ℝ) ^ (-(1 : ℝ) * (j : ℝ)) = ((3 : ℝ) ^ (-(1 : ℝ))) ^ j :=
    rpow_natDepth_eq_pow 1 j
  calc
    w *
        (Real.sqrt 2 *
              ((3 : ℝ) ^ (s * (j : ℝ)) *
                Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q) +
            Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)))
        = (Real.sqrt 2 *
              (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q)) *
              (w * (3 : ℝ) ^ (s * (j : ℝ))) +
            (Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) * w := by
          ring
    _ = (Real.sqrt 2 *
              (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q)) *
              ((3 : ℝ) ^ (-(1 - s))) ^ j +
            (Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) *
              ((3 : ℝ) ^ (-(1 : ℝ))) ^ j := by
          rw [hw1, hpow1, hw2, hpow2]

omit [NeZero d] in
/-- Nonnegativity of the tail summand. -/
private theorem smallScale_multiscaleTerm_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m L₀ : ℤ) (p q : Vec d) (i : ℕ) :
    0 ≤
      (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
        Real.sqrt
          (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) :=
  mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le (Real.sqrt_nonneg _)

/-- **Summability of the bi-infinite tail.** -/
theorem summable_smallScale_multiscaleTerm (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    Summable fun i : ℕ =>
      (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
        Real.sqrt
          (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
  have hρ₁ : 3 * (3 : ℝ) ^ (-(1 - s)) ≤ 2 := three_mul_rpow_neg_le_two (by linarith)
  have hρ₂ : 3 * (3 : ℝ) ^ (-(1 : ℝ)) ≤ 2 := three_mul_rpow_neg_le_two (by norm_num)
  have hg :
      Summable fun i : ℕ =>
        (Real.sqrt 2 *
              (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q)) *
            ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) +
          (Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) *
            ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i) :=
    ((summable_pow_shift ((3 : ℝ) ^ (-(1 - s)))
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hρ₁ ((m - L₀).toNat)).mul_left
        _).add
      ((summable_pow_shift ((3 : ℝ) ^ (-(1 : ℝ)))
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le hρ₂ ((m - L₀).toNat)).mul_left _)
  exact Summable.of_nonneg_of_le (smallScale_multiscaleTerm_nonneg a ha m L₀ p q)
    (smallScale_multiscaleTerm_le a ha hLm hs hr p q) hg

/-- **The small-scale tail.**  The bi-infinite multiscale sum over the scales `n <
L_0` is bounded by the low-scale tail term and the constant tail term of
`e.Besov.norms.gradient`, with the manuscript constant `C` given the explicit
value `2\sqrt 2` in both places. -/
theorem tsum_smallScale_multiscaleTerm_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    (∑' i : ℕ,
        (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
          Real.sqrt
            (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
              (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) ≤
      2 * Real.sqrt 2 *
          ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            maximizerEnergyL2Norm a ha (originCube d m) p q) +
        2 * Real.sqrt 2 *
          ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  have hK : (((m - L₀).toNat : ℕ) : ℤ) = m - L₀ := Int.toNat_of_nonneg (by omega)
  have hKR : (((m - L₀).toNat : ℕ) : ℝ) = ((m - L₀ : ℤ) : ℝ) := by exact_mod_cast hK
  have hρ₁0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - s)) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hρ₂0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hρ₁ : 3 * (3 : ℝ) ^ (-(1 - s)) ≤ 2 := three_mul_rpow_neg_le_two (by linarith)
  have hρ₂ : 3 * (3 : ℝ) ^ (-(1 : ℝ)) ≤ 2 := three_mul_rpow_neg_le_two (by norm_num)
  set C₁ : ℝ :=
    Real.sqrt 2 *
      (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
        maximizerEnergyL2Norm a ha (originCube d m) p q) with hC₁
  set C₂ : ℝ :=
    Real.sqrt 2 * Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) with hC₂
  have hC₁0 : 0 ≤ C₁ := by
    refine mul_nonneg (Real.sqrt_nonneg 2) (mul_nonneg (Real.sqrt_nonneg _) ?_)
    exact maximizerEnergyL2Norm_nonneg a ha (originCube d m) p q
  have hC₂0 : 0 ≤ C₂ := mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg _)
  have hs1 :=
    summable_pow_shift ((3 : ℝ) ^ (-(1 - s))) hρ₁0 hρ₁ ((m - L₀).toNat)
  have hs2' :=
    summable_pow_shift ((3 : ℝ) ^ (-(1 : ℝ))) hρ₂0 hρ₂ ((m - L₀).toNat)
  have hg : Summable fun i : ℕ =>
      C₁ * ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) +
        C₂ * ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i) :=
    (hs1.mul_left C₁).add (hs2'.mul_left C₂)
  have hf : Summable fun i : ℕ =>
      (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
        Real.sqrt
          (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) :=
    summable_smallScale_multiscaleTerm a ha hLm hs hs2 hr p q
  have hcmp :=
    Summable.tsum_le_tsum (smallScale_multiscaleTerm_le a ha hLm hs hr p q) hf hg
  refine hcmp.trans ?_
  rw [Summable.tsum_add (hs1.mul_left C₁) (hs2'.mul_left C₂), tsum_mul_left, tsum_mul_left]
  have hgeo1 :
      C₁ * ∑' i : ℕ, ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) ≤
        C₁ * (2 * ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat)) :=
    mul_le_mul_of_nonneg_left
      (tsum_pow_shift_le ((3 : ℝ) ^ (-(1 - s))) hρ₁0 hρ₁ ((m - L₀).toNat)) hC₁0
  have hgeo2 :
      C₂ * ∑' i : ℕ, ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i) ≤
        C₂ * (2 * ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat)) :=
    mul_le_mul_of_nonneg_left
      (tsum_pow_shift_le ((3 : ℝ) ^ (-(1 : ℝ))) hρ₂0 hρ₂ ((m - L₀).toNat)) hC₂0
  have hval1 : ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat) =
      (3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) := by
    rw [← rpow_natDepth_eq_pow (1 - s) ((m - L₀).toNat), hKR]
  have hval2 : ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat) =
      (3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) := by
    rw [← rpow_natDepth_eq_pow 1 ((m - L₀).toNat), hKR]
    congr 1
    ring
  calc
    C₁ * ∑' i : ℕ, ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) +
          C₂ * ∑' i : ℕ, ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i)
        ≤ C₁ * (2 * ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat)) +
            C₂ * (2 * ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat)) := add_le_add hgeo1 hgeo2
    _ = 2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q) +
          2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
          rw [hval1, hval2, hC₁, hC₂]
          ring

/-- **The finite-range form of the small-scale tail.**  Every partial sum of
the tail obeys the same bound, so a consumer that produces the multiscale sum
only over a finite range of scales can use the identical right-hand side. -/
theorem sum_range_smallScale_multiscaleTerm_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) (N : ℕ) :
    (∑ i ∈ Finset.range N,
        (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
          Real.sqrt
            (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
              (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) ≤
      2 * Real.sqrt 2 *
          ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            maximizerEnergyL2Norm a ha (originCube d m) p q) +
        2 * Real.sqrt 2 *
          ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  refine le_trans ?_ (tsum_smallScale_multiscaleTerm_le a ha hLm hs hs2 hr p q)
  exact Summable.sum_le_tsum (Finset.range N)
    (fun i _ => smallScale_multiscaleTerm_nonneg a ha m L₀ p q i)
    (summable_smallScale_multiscaleTerm a ha hLm hs hs2 hr p q)

end

end Algsuperdiff.Section3.Provider.Besov

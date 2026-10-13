/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RelativeNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdasUpper
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceBridge

/-!
# CombineFiniteTrace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Quantitative trace channel

The starred trace average is transported from the same-cutoff relative law to
physical cutoff samples.  Jensen reduces its square to the fourth moment of
the physical child error, and translation stationarity identifies every child
moment with the cutoff-scale origin moment.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch05.Section56
open _root_.HCPolySupport.IndependentSums
open scoped MatrixOrder

noncomputable section

open HCPolySupport.Book.Ch04
  renaming doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField →
    doubledResponseJ_eq_restrictionObservable


private theorem descendantsAverage_dilateCube_trace
    {d : ℕ} (k : ℤ) (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) :
    descendantsAverage (Book.Ch02.dilateCube k Q) j F =
      descendantsAverage Q j (fun R => F (Book.Ch02.dilateCube k R)) := by
  classical
  dsimp [descendantsAverage]
  rw [Book.Ch02.descendantsAtDepth_dilateCube]
  rw [Finset.card_image_of_injective _ (Book.Ch02.dilateCube_injective k)]
  rw [Finset.sum_image]
  intro R _hR S _hS hRS
  exact Book.Ch02.dilateCube_injective k hRS

private theorem sum_doubledResponseJ_constantIsotropic_le_normalizedBlockResponseMax_trace
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) :
    (∑ alpha : BlockCoord d,
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
          (fullBlockMatrixProbe
            (Book.Ch02.constantFullBlockMatrixInvSqrt
              (Observable.isotropicComparatorMatrix sigma)) alpha)
          (fullBlockMatrixProbe
            (Book.Ch02.constantFullBlockMatrixSqrt
              (Observable.isotropicComparatorMatrix sigma)) alpha)) ≤
      (Fintype.card (BlockCoord d) : ℝ) *
        Book.Ch02.normalizedBlockResponseMax Q F
          (Observable.isotropicComparatorMatrix sigma) := by
  classical
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  have hterm : ∀ alpha : BlockCoord d,
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
          (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
          (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha) ≤
        Book.Ch02.normalizedBlockResponseMax Q F a0 := by
    intro alpha
    let e : FullBlockVec d := Pi.single alpha 1
    have he : fullBlockVecNormSq e = 1 := by
      unfold fullBlockVecNormSq e
      rw [Fintype.sum_eq_single alpha]
      · simp
      · intro beta hbeta
        simp [hbeta]
    have hmem :
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
            (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
            (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha) ∈
          Book.Ch02.normalizedBlockResponseValueSet Q F a0 := by
      refine ⟨e, he, ?_⟩
      rfl
    unfold Book.Ch02.normalizedBlockResponseMax
    exact le_csSup
      (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
        F (Q := Q) (R := Q) (k := Q.scale) a0
          (by simp [descendantsAtScale_self])) hmem
  change
    (∑ alpha : BlockCoord d,
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
          (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
          (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha)) ≤
      (Fintype.card (BlockCoord d) : ℝ) *
        Book.Ch02.normalizedBlockResponseMax Q F a0
  calc
    _ ≤ ∑ _alpha : BlockCoord d,
        Book.Ch02.normalizedBlockResponseMax Q F a0 :=
      Finset.sum_le_sum fun alpha _halpha => hterm alpha
    _ = (Fintype.card (BlockCoord d) : ℝ) *
        Book.Ch02.normalizedBlockResponseMax Q F a0 := by simp

private theorem aemeasurable_starredBlockJTraceAverageSq_trace
    {d : ℕ} [NeZero d] {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : Book.Ch04.RestrictionLawCarrier P)
    (B : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    AEMeasurable (starredBlockJTraceAverageSq B Q j) P := by
  classical
  unfold starredBlockJTraceAverageSq starredBlockJTraceAverage
    blockJTraceAverageWithNormalizers
  apply AEMeasurable.pow_const
  apply Book.Ch04.aemeasurable_descendantsAverage
  intro R _hR
  apply Finset.aemeasurable_fun_sum Finset.univ
  intro alpha _halpha
  simpa only [Book.Ch04.blockJSetObservableBlockVec_cubeSet] using!
    Book.Ch04.aemeasurable_blockJSetObservableBlockVec_cubeSet hP R
      (fullBlockMatrixProbe (CFC.sqrt (B⁻¹)) alpha)
      (fullBlockMatrixProbe (CFC.sqrt B) alpha)

private theorem starredBlockJTraceAverage_relativeCutoffSample_eq_physicalDescendantsAverage_trace
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ)
    (omega : Cutoff.CutoffSample d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let h : ℤ := L + c
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    starredBlockJTraceAverage B (originCube d (n - h)) (n - L).toNat
        (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) =
      descendantsAverage (originCube d n) (n - L).toNat
        (fun R =>
          ∑ alpha : BlockCoord d,
            Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
              ((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
              (fullBlockMatrixProbe
                (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
              (fullBlockMatrixProbe
                (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha)) := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let Qphys : TriadicCube d := originCube d n
  let Qrel : TriadicCube d := originCube d (n - h)
  let j : ℕ := (n - L).toNat
  let aPhys : RegCoeffField d := Cutoff.coefficientCutoff M.nu L omega
  let haPhys : Book.Ch04.AELocallyUniformlyEllipticField aPhys :=
    Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
  let aRel : RegCoeffField d := dilateReg (-h) aPhys
  let haRel : Book.Ch04.AELocallyUniformlyEllipticField aRel :=
    Cutoff.aelocallyUniformlyEllipticField_dilateReg haPhys (-h)
  let Fphys : Book.Ch02.TriadicCoeffFamily d :=
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aPhys haPhys
  let Frel : Book.Ch02.TriadicCoeffFamily d :=
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aRel haRel
  let Fdil : Book.Ch02.TriadicCoeffFamily d :=
    Book.Ch02.TriadicCoeffFamily.dilate (-h) Fphys
  have hB : B.PosDef :=
    Book.Ch02.constantFullBlockMatrix_posDef_of_isEllipticMatrix
      (by
        simpa only [a0, Observable.isotropicComparatorMatrix] using
          isEllipticMatrix_scalarMatrix sigma.property)
  have hinv : CFC.sqrt (B⁻¹) = (CFC.sqrt B)⁻¹ :=
    (Matrix.PosSemidef.inv_sqrt hB.posSemidef).symm
  have htrace :
      starredBlockJTraceAverage B Qrel j aRel =
        descendantsAverage Qrel j
          (fun R =>
            ∑ alpha : BlockCoord d,
              Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (Frel.coeffOn R)
                (fullBlockMatrixProbe
                  (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
                (fullBlockMatrixProbe
                  (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha)) := by
    unfold starredBlockJTraceAverage blockJTraceAverageWithNormalizers
    rw [hinv]
    change descendantsAverage Qrel j
        (fun R =>
          ∑ alpha : BlockCoord d,
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe
                (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
              (fullBlockMatrixProbe
                (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha) aRel) = _
    congr 1
    funext R
    apply Finset.sum_congr rfl
    intro alpha _halpha
    exact
      (doubledResponseJ_eq_restrictionObservable
        haRel R
          (fullBlockMatrixProbe
            (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
          (fullBlockMatrixProbe
            (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha)).symm
  have hrelDil : Book.Ch02.TriadicCoeffFamily.AEEq Frel Fdil := by
    simpa only [Frel, Fdil, Fphys, aRel, haRel] using
      Cutoff.triadicCoeffFamily_dilateReg_aeeq_dilate haPhys (-h)
  have hQ : Book.Ch02.dilateCube (-h) Qphys = Qrel := by
    simp [Qphys, Qrel, Book.Ch02.dilateCube, originCube]
    omega
  change starredBlockJTraceAverage B Qrel j aRel =
    descendantsAverage Qphys j
      (fun R =>
        ∑ alpha : BlockCoord d,
          Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
            ((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
            (fullBlockMatrixProbe
              (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
            (fullBlockMatrixProbe
              (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha))
  rw [htrace, ← hQ, descendantsAverage_dilateCube_trace]
  congr 1
  funext R
  apply Finset.sum_congr rfl
  intro alpha _halpha
  let P : BlockVec d := fullBlockMatrixProbe
    (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha
  let Q : BlockVec d := fullBlockMatrixProbe
    (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha
  calc
    Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (-h) R))
        (Frel.coeffOn (Book.Ch02.dilateCube (-h) R)) P Q =
      Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (Book.Ch02.dilateCube (-h) R))
        (Fdil.coeffOn (Book.Ch02.dilateCube (-h) R)) P Q :=
      Book.Ch02.doubledResponseJ_eq_ofAEEq
        (hrelDil (Book.Ch02.dilateCube (-h) R)) P Q
    _ = Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
        (Fphys.coeffOn R) P Q :=
      Book.Ch02.doubledResponseJ_dilate
        ((Book.Ch02.TriadicCoeffFamily.isDilation_dilate (-h) Fphys) R) P Q
    _ = Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
        ((Cutoff.coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) P Q :=
      Book.Ch02.doubledResponseJ_eq_ofAEEq
        ((Cutoff.coefficientCutoff_canonicalFamily_aeeq M L omega) R) P Q

private theorem starredBlockJTraceAverageSq_relativeCutoffSample_le_childErrorFourthAverage_trace
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ)
    (omega : Cutoff.CutoffSample d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let h : ℤ := L + c
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    starredBlockJTraceAverageSq B (originCube d (n - h)) (n - L).toNat
        (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ≤
      (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
        descendantsAverage (originCube d n) (n - L).toNat
          (fun R =>
            Book.Ch02.HomogenizationErrorOnCube R (1 / 16) .infinity (.finite 2)
              (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
              (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) ^ 4) := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let Qphys : TriadicCube d := originCube d n
  let j : ℕ := (n - L).toNat
  let F := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let T : TriadicCube d → ℝ := fun R =>
    ∑ alpha : BlockCoord d,
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (F.coeffOn R)
        (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
        (fullBlockMatrixProbe (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha)
  let X : TriadicCube d → ℝ := fun R =>
    Book.Ch02.HomogenizationErrorOnCube R (1 / 16) .infinity (.finite 2) F a0
  have htransport :=
    starredBlockJTraceAverage_relativeCutoffSample_eq_physicalDescendantsAverage_trace
      M L n omega
  have hpoint : ∀ R ∈ descendantsAtDepth Qphys j,
      T R ^ 2 ≤ (Fintype.card (BlockCoord d) : ℝ) ^ 2 * X R ^ 4 := by
    intro R hR
    have hsum :=
      sum_doubledResponseJ_constantIsotropic_le_normalizedBlockResponseMax_trace
        R F sigma
    have hdepth :=
      ObservationScaleFiniteCoverInternal.maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
        R (by norm_num : (0 : ℝ) < 1 / 16) F a0 0
    have hdepth0 : Book.Ch02.normalizedBlockResponseMax R F a0 ≤ X R ^ 2 := by
      simpa [Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_self, X] using hdepth
    have hTnonneg : 0 ≤ T R := by
      dsimp only [T]
      exact Finset.sum_nonneg fun alpha _halpha =>
        Book.Ch02.doubledResponseJ_nonneg (Book.Ch02.cubeDomain R) (F.coeffOn R)
          (fullBlockMatrixProbe
            (Book.Ch02.constantFullBlockMatrixInvSqrt a0) alpha)
          (fullBlockMatrixProbe
            (Book.Ch02.constantFullBlockMatrixSqrt a0) alpha)
    have hcard : 0 ≤ (Fintype.card (BlockCoord d) : ℝ) := Nat.cast_nonneg _
    have hTX : T R ≤ (Fintype.card (BlockCoord d) : ℝ) * X R ^ 2 :=
      hsum.trans (mul_le_mul_of_nonneg_left hdepth0 hcard)
    nlinarith [sq_nonneg ((Fintype.card (BlockCoord d) : ℝ) * X R ^ 2 - T R)]
  have hjensen :
      (descendantsAverage Qphys j T) ^ 2 ≤
        descendantsAverage Qphys j (fun R => T R ^ 2) := by
    have h := sum_div_card_sq_le_sum_sq_div_card
      (α := ℝ) (s := descendantsAtDepth Qphys j) (f := T)
    simpa only [descendantsAverage, div_eq_mul_inv, mul_comm] using h
  have havg : descendantsAverage Qphys j (fun R => T R ^ 2) ≤
      descendantsAverage Qphys j
        (fun R => (Fintype.card (BlockCoord d) : ℝ) ^ 2 * X R ^ 4) :=
    descendantsAverage_le_descendantsAverage Qphys j hpoint
  have hfactor : descendantsAverage Qphys j
      (fun R => (Fintype.card (BlockCoord d) : ℝ) ^ 2 * X R ^ 4) =
      (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
        descendantsAverage Qphys j (fun R => X R ^ 4) :=
    descendantsAverage_mul_left Qphys j _ _
  dsimp only [starredBlockJTraceAverageSq]
  rw [show starredBlockJTraceAverage B (originCube d (n - h)) j
      (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) =
      descendantsAverage Qphys j T by
        simpa only [c, h, sigma, a0, B, Qphys, j, F, T] using htransport]
  simpa only [c, h, sigma, a0, B, Qphys, j, F, T, X] using
    hjensen.trans (havg.trans_eq hfactor)

private theorem cutoffError_four_integrable_and_le_of_twoTerm
    {d : ℕ} (M : ABKModel d) (L : ℤ) {A D : ℝ}
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨1 / 16, by norm_num⟩) A D) :
    let mu := (Cutoff.cutoffSampleLaw M).toMeasure
    let X0 : Cutoff.CutoffSample d → ℝ :=
      Observable.cutoffHomogenizationError M L ⟨1 / 16, by norm_num⟩
    Integrable (fun omega => X0 omega ^ (4 : ℕ)) mu ∧
      (∫ omega, X0 omega ^ (4 : ℕ) ∂mu) ≤
        8 *
          ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ)) := by
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let X0 : Cutoff.CutoffSample d → ℝ :=
    Observable.cutoffHomogenizationError M L ⟨1 / 16, by norm_num⟩
  obtain ⟨Y, Z, _hPsiY, _hPsiZ, hA, hD, hXmeas, hYmeas, hZmeas,
      hdom, hYtail, hZtail⟩ := hLower
  let Y0 : Cutoff.CutoffSample d → ℝ := fun omega => max 0 (Y omega)
  let Z0 : Cutoff.CutoffSample d → ℝ := fun omega => max 0 (Z omega)
  have hY0nonneg : ∀ omega, 0 ≤ Y0 omega := fun omega => le_max_left _ _
  have hZ0nonneg : ∀ omega, 0 ≤ Z0 omega := fun omega => le_max_left _ _
  have hY0meas : AEMeasurable Y0 mu :=
    (measurable_const.max hYmeas).aemeasurable
  have hZ0meas : AEMeasurable Z0 mu :=
    (measurable_const.max hZmeas).aemeasurable
  have hY0tail : IsBigOWith mu (gammaSigma 2) Y0 A := by
    simpa only [Y0] using Tail.isBigOWith_max_zero hA hYtail
  have hZ0tail : IsBigOWith mu (gammaSigma (1 / 2)) Z0 D := by
    simpa only [Z0] using Tail.isBigOWith_max_zero hD hZtail
  have hYfour : Integrable (fun omega => Y0 omega ^ (4 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 4)
      (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hZfour : Integrable (fun omega => Z0 omega ^ (4 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 4)
      (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hYbound : ∫ omega, Y0 omega ^ (4 : ℕ) ∂mu ≤
      (gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) := by
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 4)
        (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail)
  have hZbound : ∫ omega, Z0 omega ^ (4 : ℕ) ∂mu ≤
      (gammaMomentConst (1 / 2) *
        (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ) := by
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 4)
        (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail)
  have hXnonneg : ∀ omega, 0 ≤ X0 omega := fun omega => by
    simpa only [X0] using
      Observable.cutoffHomogenizationError_nonneg M L ⟨1 / 16, by norm_num⟩ omega
  have hXpoint : ∀ omega, X0 omega ^ (4 : ℕ) ≤
      8 * (Y0 omega ^ (4 : ℕ) + Z0 omega ^ (4 : ℕ)) := by
    intro omega
    have hYZ : X0 omega ≤ Y0 omega + Z0 omega :=
      (hdom omega).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
    have hp := pow_le_pow_left₀ (hXnonneg omega) hYZ 4
    have hadd := add_pow_le (hY0nonneg omega) (hZ0nonneg omega) 4
    norm_num at hadd ⊢
    exact hp.trans hadd
  have hXfour : Integrable (fun omega => X0 omega ^ (4 : ℕ)) mu := by
    refine Integrable.mono' ((hYfour.add hZfour).const_mul 8)
      ((hXmeas.pow_const 4).aestronglyMeasurable) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hXnonneg omega) 4)]
    exact hXpoint omega
  refine ⟨hXfour, ?_⟩
  calc
    (∫ omega, X0 omega ^ (4 : ℕ) ∂mu) ≤
        ∫ omega, 8 * (Y0 omega ^ (4 : ℕ) + Z0 omega ^ (4 : ℕ)) ∂mu :=
      integral_mono hXfour ((hYfour.add hZfour).const_mul 8) hXpoint
    _ = 8 * ((∫ omega, Y0 omega ^ (4 : ℕ) ∂mu) +
        ∫ omega, Z0 omega ^ (4 : ℕ) ∂mu) := by
      rw [integral_const_mul, integral_add hYfour hZfour]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hYbound hZbound) (by norm_num)

private theorem cellErrorFour_integral_eq
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ)
    (R : TriadicCube d) (hRscale : R.scale = L) :
    let mu := (Cutoff.cutoffSampleLaw M).toMeasure
    let a0 : Mat d :=
      Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
    (∫ omega,
        Book.Ch02.HomogenizationErrorOnCube R (1 / 16)
          .infinity (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) a0 ^ (4 : ℕ)
        ∂mu) =
      ∫ omega,
        Observable.cutoffHomogenizationError M L
          ⟨1 / 16, by norm_num⟩ omega ^ (4 : ℕ)
        ∂mu := by
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let a0 : Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let X0 : Cutoff.CutoffSample d → ℝ :=
    Observable.cutoffHomogenizationError M L ⟨1 / 16, by norm_num⟩
  let tau := Cutoff.translateCutoffSample (triadicCubeShift R)
  have hmap : Measure.map tau mu = mu := by
    simpa only [mu, tau] using
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift R)
  have horigin :=
    Observable.cutoffHomogenizationErrorAtComparatorScale_ae_eq_homogenizationErrorOnCube
      M L L ⟨1 / 16, by norm_num⟩
  have htau : MeasurePreserving tau mu mu :=
    ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift R), hmap⟩
  have htranslated := htau.quasiMeasurePreserving.ae_eq_comp horigin
  have heq :
      (fun omega =>
        Book.Ch02.HomogenizationErrorOnCube R (1 / 16)
          .infinity (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) a0 ^ (4 : ℕ)) =ᵐ[mu]
        fun omega => X0 (tau omega) ^ (4 : ℕ) := by
    filter_upwards [htranslated] with omega homega
    rw [BadEvents.homogenizationErrorOnCube_translateCutoffSample
      M L R (1 / 16) .infinity (.finite 2) a0 omega, hRscale]
    exact congrArg (fun x : ℝ => x ^ (4 : ℕ)) homega.symm
  calc
    _ = ∫ omega, X0 (tau omega) ^ (4 : ℕ) ∂mu := integral_congr_ae heq
    _ = ∫ omega, X0 omega ^ (4 : ℕ) ∂mu := by
      exact _root_.HCPolySupport.integral_comp_eq_of_map_eq
        (Cutoff.measurable_translateCutoffSample (triadicCubeShift R)) hmap
        (fun omega => X0 omega ^ (4 : ℕ))
        ((Observable.measurable_cutoffHomogenizationError
          M L ⟨1 / 16, by norm_num⟩).pow_const 4).aestronglyMeasurable

private theorem relativeStarredTraceAverage_integral_bound :
    ∀ {d : ℕ} (mu : Measure (Cutoff.CutoffSample d))
      (Qphys : TriadicCube d) (j : ℕ) (X0 : Cutoff.CutoffSample d → ℝ)
      (cellErrorFour : TriadicCube d → Cutoff.CutoffSample d → ℝ),
      (∀ R ∈ descendantsAtDepth Qphys j, Integrable (cellErrorFour R) mu) →
        (∀ R ∈ descendantsAtDepth Qphys j,
            ∫ (omega : Cutoff.CutoffSample d), cellErrorFour R omega ∂mu =
              ∫ (omega : Cutoff.CutoffSample d), X0 omega ^ (4 : ℕ) ∂mu) →
          ∫ (omega : Cutoff.CutoffSample d),
              descendantsAverage Qphys j fun (R : TriadicCube d) => cellErrorFour R omega ∂mu =
            ∫ (omega : Cutoff.CutoffSample d), X0 omega ^ (4 : ℕ) ∂mu := by
  intro d mu Qphys j X0 cellErrorFour hcell hcellIntegral
  have hcommute :
      (∫ omega, descendantsAverage Qphys j (fun R => cellErrorFour R omega) ∂mu) =
        descendantsAverage Qphys j
          (fun R => ∫ omega, cellErrorFour R omega ∂mu) := by
    let descendants : Finset (TriadicCube d) := descendantsAtDepth Qphys j
    calc
      _ = ∫ omega, (descendants.card : ℝ)⁻¹ *
            (∑ R ∈ descendants, cellErrorFour R omega) ∂mu := by rfl
      _ = (descendants.card : ℝ)⁻¹ *
            ∫ omega, ∑ R ∈ descendants, cellErrorFour R omega ∂mu := by
        rw [integral_const_mul]
      _ = (descendants.card : ℝ)⁻¹ *
            (∑ R ∈ descendants, ∫ omega, cellErrorFour R omega ∂mu) := by
        rw [integral_finsetSum descendants
          (fun R hR => hcell R (by simpa only [descendants] using hR))]
      _ = descendantsAverage Qphys j
            (fun R => ∫ omega, cellErrorFour R omega ∂mu) := by
        simp only [descendantsAverage, descendants]
  rw [hcommute]
  have hcongr : descendantsAverage Qphys j
      (fun R => ∫ omega, cellErrorFour R omega ∂mu) =
      descendantsAverage Qphys j
        (fun _ => ∫ omega, X0 omega ^ (4 : ℕ) ∂mu) := by
    unfold descendantsAverage
    change ((descendantsAtDepth Qphys j).card : ℝ)⁻¹ *
        (descendantsAtDepth Qphys j).sum
          (fun R => ∫ omega, cellErrorFour R omega ∂mu) =
      ((descendantsAtDepth Qphys j).card : ℝ)⁻¹ *
        (descendantsAtDepth Qphys j).sum
          (fun _ => ∫ omega, X0 omega ^ (4 : ℕ) ∂mu)
    congr 1
    apply Finset.sum_congr rfl
    intro R hR
    exact hcellIntegral R hR
  rw [hcongr, descendantsAverage_const_eq]

/-- Quantitative fourth-moment control of the starred trace channel at every
physical observation scale above the cutoff. -/
theorem eight_mul_integral_relativeStarredBlockJTraceAverageSq_le
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    {A D : ℝ}
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨1 / 16, by norm_num⟩) A D) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let h : ℤ := L + c
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let a0 : Mat d :=
      Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let Q : TriadicCube d := originCube d (n - h)
    let j : ℕ := (n - L).toNat
    let fourthBudget : ℝ :=
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
    Integrable (starredBlockJTraceAverageSq B Q j) P ∧
      8 * ∫ a, starredBlockJTraceAverageSq B Q j a ∂P ≤
        8 * ((Fintype.card (BlockCoord d) : ℝ) ^ 2 * fourthBudget) := by
  classical
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let a0 : Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let Qphys : TriadicCube d := originCube d n
  let Q : TriadicCube d := originCube d (n - h)
  let j : ℕ := (n - L).toNat
  let X0 : Cutoff.CutoffSample d → ℝ :=
    Observable.cutoffHomogenizationError M L ⟨1 / 16, by norm_num⟩
  let cellErrorFour : TriadicCube d → Cutoff.CutoffSample d → ℝ := fun R omega =>
    Book.Ch02.HomogenizationErrorOnCube R (1 / 16) .infinity (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) a0 ^ (4 : ℕ)
  let fourthBudget : ℝ :=
    8 *
      ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
  have hfour := cutoffError_four_integrable_and_le_of_twoTerm M L hLower
  have hXfour : Integrable (fun omega => X0 omega ^ (4 : ℕ)) mu := by
    simpa only [mu, X0] using hfour.1
  have hXfourBound : (∫ omega, X0 omega ^ (4 : ℕ) ∂mu) ≤ fourthBudget := by
    simpa only [mu, X0, fourthBudget] using hfour.2
  have hj : (j : ℤ) = n - L := by
    dsimp only [j]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hLn)
  have hcell : ∀ R ∈ descendantsAtDepth Qphys j,
      Integrable (cellErrorFour R) mu := by
    intro R hR
    have hRscale : R.scale = L := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hj]
      simp only [Qphys, originCube]
      ring
    let tau := Cutoff.translateCutoffSample (triadicCubeShift R)
    have htau : MeasurePreserving tau mu mu := by
      refine ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift R), ?_⟩
      simpa only [mu, tau] using
        Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift R)
    have htranslatedInt : Integrable (fun omega => X0 (tau omega) ^ (4 : ℕ)) mu := by
      simpa only [Function.comp_apply] using! htau.integrable_comp_of_integrable hXfour
    have horigin :=
      Observable.cutoffHomogenizationErrorAtComparatorScale_ae_eq_homogenizationErrorOnCube
        M L L ⟨1 / 16, by norm_num⟩
    have htranslated := htau.quasiMeasurePreserving.ae_eq_comp horigin
    refine htranslatedInt.congr ?_
    filter_upwards [htranslated] with omega homega
    dsimp only [cellErrorFour]
    rw [BadEvents.homogenizationErrorOnCube_translateCutoffSample
      M L R (1 / 16) .infinity (.finite 2) a0 omega, hRscale]
    exact congrArg (fun x : ℝ => x ^ (4 : ℕ)) homega
  have hcellIntegral : ∀ R ∈ descendantsAtDepth Qphys j,
      (∫ omega, cellErrorFour R omega ∂mu) =
        ∫ omega, X0 omega ^ (4 : ℕ) ∂mu := by
    intro R hR
    have hRscale : R.scale = L := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hj]
      simp only [Qphys, originCube]
      ring
    simpa only [mu, a0, cellErrorFour, X0] using
      cellErrorFour_integral_eq M L R hRscale
  have havgInt : Integrable
      (fun omega => descendantsAverage Qphys j (fun R => cellErrorFour R omega)) mu := by
    unfold descendantsAverage
    exact (integrable_finsetSum (descendantsAtDepth Qphys j) hcell).const_mul
      (((descendantsAtDepth Qphys j).card : ℝ)⁻¹)
  have havgIntegral := @relativeStarredTraceAverage_integral_bound (d) (mu) (Qphys) (j) (X0)
    (cellErrorFour) (hcell) (hcellIntegral)
  let J2 : RegCoeffField d → ℝ := starredBlockJTraceAverageSq B Q j
  let G : Cutoff.CutoffSample d → ℝ := fun omega =>
    (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
      descendantsAverage Qphys j (fun R => cellErrorFour R omega)
  have hGint : Integrable G mu := by
    simpa only [G] using havgInt.const_mul ((Fintype.card (BlockCoord d) : ℝ) ^ 2)
  have hJ2meas : AEMeasurable J2 P := by
    simpa only [J2, P] using
      aemeasurable_starredBlockJTraceAverageSq_trace
        (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L) B Q j
  have hrelLaw : P = Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L) := by
    simpa only [P, h] using Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg M L
  have hJ2MapMeas : AEStronglyMeasurable J2
      (Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L)) := by
    simpa only [← hrelLaw] using hJ2meas.aestronglyMeasurable
  have hJ2coeffMeas : AEStronglyMeasurable (J2 ∘ dilateReg (-h))
      (Cutoff.coefficientCutoffLaw M L) :=
    hJ2MapMeas.comp_quasiMeasurePreserving
      ((measurable_dilateReg (d := d) (-h)).quasiMeasurePreserving
        (Cutoff.coefficientCutoffLaw M L))
  have hJ2sampleMeas : AEStronglyMeasurable
      (fun omega => J2 (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega))) mu := by
    have hmapMeas : AEStronglyMeasurable (J2 ∘ dilateReg (-h))
        (Measure.map (Cutoff.coefficientCutoff M.nu L) mu) := by
      simpa only [← Cutoff.coefficientCutoffLaw_eq_map, mu] using hJ2coeffMeas
    simpa only [Function.comp_apply] using! hmapMeas.comp_quasiMeasurePreserving
      ((Cutoff.measurable_coefficientCutoff M.nu L).quasiMeasurePreserving mu)
  have hpoint : ∀ omega,
      J2 (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ≤ G omega := by
    intro omega
    simpa only [J2, G, c, h, a0, B, Q, Qphys, j, cellErrorFour] using
      starredBlockJTraceAverageSq_relativeCutoffSample_le_childErrorFourthAverage_trace
        M L n omega
  have hJ2sampleInt : Integrable
      (fun omega => J2 (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega))) mu := by
    refine Integrable.mono' hGint hJ2sampleMeas ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint omega
  have hJ2coeffInt : Integrable (J2 ∘ dilateReg (-h))
      (Cutoff.coefficientCutoffLaw M L) := by
    rw [Cutoff.coefficientCutoffLaw_eq_map]
    exact (integrable_map_measure hJ2coeffMeas
      (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable).mpr
        (by simpa only [Function.comp_apply] using! hJ2sampleInt)
  have hJ2Int : Integrable J2 P := by
    rw [hrelLaw]
    exact (integrable_map_measure hJ2MapMeas
      (measurable_dilateReg (d := d) (-h)).aemeasurable).mpr hJ2coeffInt
  have hJIntegralSample : (∫ a, J2 a ∂P) =
      ∫ omega, J2 (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ∂mu := by
    calc
      (∫ a, J2 a ∂P) =
          ∫ a, J2 (dilateReg (-h) a) ∂(Cutoff.coefficientCutoffLaw M L) := by
        rw [hrelLaw]
        exact integral_map (measurable_dilateReg (d := d) (-h)).aemeasurable hJ2MapMeas
      _ = ∫ omega, J2 (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ∂mu := by
        rw [Cutoff.coefficientCutoffLaw_eq_map]
        have hmapMeas : AEStronglyMeasurable (J2 ∘ dilateReg (-h))
            (Measure.map (Cutoff.coefficientCutoff M.nu L) mu) := by
          simpa only [← Cutoff.coefficientCutoffLaw_eq_map, mu] using hJ2coeffMeas
        exact integral_map (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable hmapMeas
  have hJBound : (∫ a, J2 a ∂P) ≤
      (Fintype.card (BlockCoord d) : ℝ) ^ 2 * fourthBudget := by
    rw [hJIntegralSample]
    calc
      _ ≤ ∫ omega, G omega ∂mu :=
        integral_mono hJ2sampleInt hGint hpoint
      _ = (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
          ∫ omega, descendantsAverage Qphys j
            (fun R => cellErrorFour R omega) ∂mu := by
        rw [integral_const_mul]
      _ = (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
          ∫ omega, X0 omega ^ (4 : ℕ) ∂mu := by rw [havgIntegral]
      _ ≤ (Fintype.card (BlockCoord d) : ℝ) ^ 2 * fourthBudget :=
        mul_le_mul_of_nonneg_left hXfourBound (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · simpa only [P, c, h, a0, B, Q, j, J2] using hJ2Int
  · simpa only [P, c, h, a0, B, Q, j, fourthBudget, J2] using
      mul_le_mul_of_nonneg_left hJBound (by norm_num : (0 : ℝ) ≤ 8)

end

end Algsuperdiff.Section3.Provider.Homogenization

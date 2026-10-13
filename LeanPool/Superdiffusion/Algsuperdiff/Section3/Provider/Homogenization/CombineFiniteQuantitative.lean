/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineFiniteMean
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.RelativeLimitLoadBridge

/-!
# CombineFiniteQuantitative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Relative descendant fluctuation decomposition

This module decomposes a relative-normalized descendant probe into its
centered random part and its deterministic annealed-scale defect. It also
transfers annealed block monotonicity across every integer relative scale.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch02
open _root_.HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
open _root_.HCPolySupport.IndependentSums
open scoped MatrixOrder

noncomputable section

private theorem doubledResponseJ_constantNormalizer_le_normSq_mul_error_sq
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) {s : ℝ} (hs : 0 < s)
    (q : FullBlockVec d) :
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let Pq : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) q)
    let Qq : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) q)
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q) Pq Qq ≤
      dotProduct q q *
        (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F a0) ^
          (2 : ℕ) := by
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let Pq : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) q)
  let Qq : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) q)
  let E : ℝ := Book.Ch02.HomogenizationErrorOnCube
    Q s .infinity (.finite 2) F a0
  dsimp only
  by_cases hqzero : q = 0
  · subst q
    change Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
        Pq Qq ≤ dotProduct (0 : FullBlockVec d) 0 * E ^ (2 : ℕ)
    have hPzero : Pq = 0 := by
      ext i <;> simp [Pq, ofFullBlockVec, Matrix.mulVec]
    have hQzero : Qq = 0 := by
      ext i <;> simp [Qq, ofFullBlockVec, Matrix.mulVec]
    rw [hPzero, hQzero]
    rw [(Book.Ch02.blockCoarseMatrixTheory
      (Book.Ch02.cubeDomain Q) (F.coeffOn Q)).doubled_response_splitting]
    simp [dotProduct, blockVecDot, blockMatVecMul, vecDot, matVecMul]
  · have hrPos : 0 < dotProduct q q := by
      simpa only [star_trivial] using
        (Matrix.dotProduct_self_star_pos_iff (v := q)).2 hqzero
    let t : ℝ := Real.sqrt (dotProduct q q)
    let u : FullBlockVec d := t⁻¹ • q
    have htPos : 0 < t := Real.sqrt_pos.2 hrPos
    have htSq : t ^ (2 : ℕ) = dotProduct q q := Real.sq_sqrt hrPos.le
    have hu : dotProduct u u = 1 := by
      dsimp only [u]
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      field_simp [htPos.ne']
      nlinarith [htSq]
    have huNorm : Book.Ch02.fullBlockVecNormSq u = 1 := by
      simpa [Book.Ch02.fullBlockVecNormSq, dotProduct, pow_two] using hu
    let Pu : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) u)
    let Qu : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) u)
    have hmem : Book.Ch02.doubledResponseJ
          (Book.Ch02.cubeDomain Q) (F.coeffOn Q) Pu Qu ∈
        Book.Ch02.normalizedBlockResponseValueSet Q F a0 := by
      exact ⟨u, huNorm, rfl⟩
    have hunit : Book.Ch02.doubledResponseJ
          (Book.Ch02.cubeDomain Q) (F.coeffOn Q) Pu Qu ≤
        Book.Ch02.normalizedBlockResponseMax Q F a0 := by
      exact le_csSup
        (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
          F a0 (by rw [descendantsAtScale_self]; exact Finset.mem_singleton_self Q)) hmem
    have hhom (c : ℝ) (P R : BlockVec d) :
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
            (c • P) (c • R) =
          c ^ (2 : ℕ) *
            Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q) P R := by
      rw [(Book.Ch02.blockCoarseMatrixTheory
        (Book.Ch02.cubeDomain Q) (F.coeffOn Q)).doubled_response_splitting,
        (Book.Ch02.blockCoarseMatrixTheory
          (Book.Ch02.cubeDomain Q) (F.coeffOn Q)).doubled_response_splitting]
      simp only [blockMatVecMul_smul, blockVecDot_smul_left,
        blockVecDot_smul_right]
      ring
    have htu : t • u = q := by
      dsimp only [u]
      ext alpha
      simp only [smul_eq_mul, Pi.smul_apply]
      field_simp [htPos.ne']
    have hPscale : Pq = t • Pu := by
      dsimp only [Pq, Pu]
      rw [← htu]
      rw [Matrix.mulVec_smul, ofFullBlockVec_smul]
    have hQscale : Qq = t • Qu := by
      dsimp only [Qq, Qu]
      rw [← htu]
      rw [Matrix.mulVec_smul, ofFullBlockVec_smul]
    have hmax : Book.Ch02.normalizedBlockResponseMax Q F a0 ≤ E ^ (2 : ℕ) := by
      have hdepth :=
        ObservationScaleFiniteCoverInternal.maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
          Q hs F a0 0
      norm_num at hdepth
      simpa only [E] using hdepth
    change Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
        Pq Qq ≤ dotProduct q q * E ^ (2 : ℕ)
    rw [hPscale, hQscale, hhom]
    calc
      t ^ (2 : ℕ) * Book.Ch02.doubledResponseJ
          (Book.Ch02.cubeDomain Q) (F.coeffOn Q) Pu Qu ≤
          t ^ (2 : ℕ) * Book.Ch02.normalizedBlockResponseMax Q F a0 :=
        mul_le_mul_of_nonneg_left hunit (sq_nonneg t)
      _ = dotProduct q q * Book.Ch02.normalizedBlockResponseMax Q F a0 := by
        rw [htSq]
      _ ≤ dotProduct q q * E ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hmax (dotProduct_self_nonneg q)

private theorem relativeOrigin_doubledResponseJ_le_normSq_mul_cutoffError_sq
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ)
    {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let h : ℤ := L + c
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let R : TriadicCube d := originCube d (-c)
    let aPhys : RegCoeffField d := Cutoff.coefficientCutoff M.nu L omega
    let haPhys : Book.Ch04.AELocallyUniformlyEllipticField aPhys :=
      Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
    let aRel : RegCoeffField d := dilateReg (-h) aPhys
    let haRel : Book.Ch04.AELocallyUniformlyEllipticField aRel :=
      Cutoff.aelocallyUniformlyEllipticField_dilateReg haPhys (-h)
    let Frel : Book.Ch02.TriadicCoeffFamily d :=
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aRel haRel
    let Pq : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) q)
    let Qq : BlockVec d := ofFullBlockVec
      (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) q)
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (Frel.coeffOn R) Pq Qq ≤
      dotProduct q q *
        Observable.cutoffHomogenizationErrorRaw M L L s sigma omega ^ (2 : ℕ) := by
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let R : TriadicCube d := originCube d (-c)
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
  let Pq : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) q)
  let Qq : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) q)
  have hR : Book.Ch02.dilateCube (-h) (originCube d L) = R := by
    simp [R, h, c, Book.Ch02.dilateCube, originCube]
  have hrelDil : Book.Ch02.TriadicCoeffFamily.AEEq Frel Fdil := by
    simpa only [Frel, Fdil, Fphys, aRel, haRel] using
      Cutoff.triadicCoeffFamily_dilateReg_aeeq_dilate haPhys (-h)
  have herr :
      Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) Frel a0 =
        Observable.cutoffHomogenizationErrorRaw M L L s sigma omega := by
    calc
      _ = Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) Fdil a0 :=
        Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq hrelDil R s
          .infinity (.finite 2) a0
      _ = Book.Ch02.HomogenizationErrorOnCube (originCube d L) s .infinity
          (.finite 2) Fphys a0 := by
        rw [← hR]
        exact Book.Ch02.HomogenizationErrorOnCube_dilate
          (Book.Ch02.TriadicCoeffFamily.isDilation_dilate (-h) Fphys)
          (originCube d L) s .infinity (.finite 2) a0
      _ = Book.Ch02.HomogenizationErrorOnCube (originCube d L) s .infinity
          (.finite 2) (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) a0 :=
        Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq
          (Cutoff.coefficientCutoff_canonicalFamily_aeeq M L omega)
          (originCube d L) s .infinity (.finite 2) a0
      _ = Observable.cutoffHomogenizationErrorRaw M L L s sigma omega := by
        rw [Observable.cutoffHomogenizationErrorRaw_characterization]
  have hbound := doubledResponseJ_constantNormalizer_le_normSq_mul_error_sq
    R Frel sigma hs q
  simpa only [Pq, Qq, a0, herr] using hbound

private theorem cutoffError_sq_integrable_and_le_of_twoTerm
    {d : ℕ} (M : ABKModel d) (L : ℤ) {s A D : ℝ} (hs : 0 < s)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨s, hs⟩) A D) :
    let X := Observable.cutoffHomogenizationError M L ⟨s, hs⟩
    let secondBudget : ℝ :=
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
    Integrable (fun omega => X omega ^ (2 : ℕ))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ omega, X omega ^ (2 : ℕ) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        secondBudget := by
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := Observable.cutoffHomogenizationError M L ⟨s, hs⟩
  let secondBudget : ℝ :=
    2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
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
  have hY2Int : Integrable (fun omega => Y0 omega ^ (2 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 2)
      (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hZ2Int : Integrable (fun omega => Z0 omega ^ (2 : ℕ)) mu := by
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 2)
      (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using h
  have hY2 : ∫ omega, Y0 omega ^ (2 : ℕ) ∂mu ≤
      (gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) := by
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Y0) (K := A) (σ := 2) (p := 2)
        (by norm_num) hA (by norm_num) hY0nonneg hY0meas hY0tail)
  have hZ2 : ∫ omega, Z0 omega ^ (2 : ℕ) ∂mu ≤
      (gammaMomentConst (1 / 2) *
        (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ) := by
    simpa only [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] using
      (integral_rpow_le_of_isBigOWith_gammaSigma
        (μ := mu) (Y := Z0) (K := D) (σ := (1 / 2 : ℝ)) (p := 2)
        (by norm_num) hD (by norm_num) hZ0nonneg hZ0meas hZ0tail)
  have hXnonneg : ∀ omega, 0 ≤ X omega := fun omega => by
    simpa only [X] using Observable.cutoffHomogenizationError_nonneg M L ⟨s, hs⟩ omega
  have hXdom : ∀ omega, X omega ≤ Y0 omega + Z0 omega := fun omega =>
    (hdom omega).trans (add_le_add (le_max_right _ _) (le_max_right _ _))
  have hX2Point : ∀ omega, X omega ^ (2 : ℕ) ≤
      2 * (Y0 omega ^ (2 : ℕ) + Z0 omega ^ (2 : ℕ)) := by
    intro omega
    have hp := pow_le_pow_left₀ (hXnonneg omega) (hXdom omega) 2
    nlinarith [sq_nonneg (Y0 omega - Z0 omega)]
  have hX2Int : Integrable (fun omega => X omega ^ (2 : ℕ)) mu := by
    refine Integrable.mono' ((hY2Int.add hZ2Int).const_mul 2)
      ((hXmeas.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hX2Point omega
  refine ⟨?_, ?_⟩
  · simpa only [mu, X] using hX2Int
  · change (∫ omega, X omega ^ (2 : ℕ) ∂mu) ≤ secondBudget
    calc
      _ ≤ ∫ omega, 2 * (Y0 omega ^ (2 : ℕ) + Z0 omega ^ (2 : ℕ)) ∂mu :=
        integral_mono hX2Int ((hY2Int.add hZ2Int).const_mul 2) hX2Point
      _ = 2 * ((∫ omega, Y0 omega ^ (2 : ℕ) ∂mu) +
          ∫ omega, Z0 omega ^ (2 : ℕ) ∂mu) := by
        rw [integral_const_mul, integral_add hY2Int hZ2Int]
      _ ≤ secondBudget := by
        dsimp only [secondBudget]
        exact mul_le_mul_of_nonneg_left (add_le_add hY2 hZ2) (by norm_num)

private theorem relativeNormalizedCutoffLaw_integrable_blockMatEntryAtScale_int
    {d : ℕ} [NeZero d] (M : ABKModel d) (L r : ℤ) :
    ∀ alpha beta,
      Integrable (fun a : RegCoeffField d =>
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d r)) a.toFun)
          alpha beta) (Cutoff.relativeNormalizedCutoffLaw M L) := by
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let dilation : ℤ := -(L + c)
  let P0 := Cutoff.coefficientCutoffLaw M L
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let Qrel : TriadicCube d := originCube d r
  let Qphys : TriadicCube d := originCube d (L + c + r)
  have hLaw : P = Measure.map (dilateReg dilation) P0 := by
    simpa only [P, P0, dilation, c] using
      Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg M L
  have hQ : Book.Ch02.dilateCube (-dilation) Qrel = Qphys := by
    simp [Qrel, Qphys, dilation, c, Book.Ch02.dilateCube, originCube, add_comm]
  intro alpha beta
  let f : RegCoeffField d → ℝ := fun a =>
    blockMatEntry (coarseBlockMatrix (cubeSet Qrel) a.toFun) alpha beta
  have hfMeas : AEMeasurable f P := by
    cases alpha with
    | inl i =>
        cases beta with
        | inl j =>
            simpa [f, blockMatEntry] using
              (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L).aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
                Qrel i j
        | inr j =>
            simpa [f, blockMatEntry] using
              (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L).aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
                Qrel i j
    | inr i =>
        cases beta with
        | inl j =>
            simpa [f, blockMatEntry] using
              (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L).aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
                Qrel i j
        | inr j =>
            simpa [f, blockMatEntry] using
              (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L).aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
                Qrel i j
  have hSourceEntry : Integrable
      (fun a : RegCoeffField d =>
        blockMatEntry (coarseBlockMatrix (cubeSet Qphys) a.toFun) alpha beta) P0 := by
    simpa only [P0] using
      Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
        M L Qphys alpha beta
  have hComp : Integrable (f ∘ dilateReg dilation) P0 := by
    refine hSourceEntry.congr ?_
    filter_upwards
      [(Cutoff.coefficientCutoffLaw_lawCarrier M L).ae_locallyUniformlyEllipticField]
      with a ha
    have hmatrix :=
      coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
        ha dilation Qrel
    rw [hQ] at hmatrix
    exact congrArg (fun A : BlockMat d => blockMatEntry A alpha beta) hmatrix.symm
  change Integrable f P
  rw [hLaw] at hfMeas ⊢
  exact (integrable_map_measure hfMeas.aestronglyMeasurable
    (measurable_dilateReg (d := d) dilation).aemeasurable).mpr hComp

private theorem integral_starredComparator_relativeOrigin_eq_annealedGap
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ) (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let Cchild := Book.Ch04.annealedBlockMatrixAtScale P (-c)
    (∫ a,
        fullBlockQuadratic
          (starredFluctuationMatrix B C0
            (cubeSet (originCube d (-c))) a) q ∂P) =
      fullBlockQuadratic
        (CFC.sqrt B *
          (toFullBlockMat (blockReflect Cchild) -
            toFullBlockMat (blockReflect C0)) * CFC.sqrt B) q := by
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let Cchild := Book.Ch04.annealedBlockMatrixAtScale P (-c)
  let rdiag := Book.Ch05.Section56.scalarFullBlockSqrtDiag
    (d := d) (sigma : ℝ) (sigma : ℝ)
  let Qv : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Matrix.diagonal rdiag) q)
  have hSdiag : CFC.sqrt B = Matrix.diagonal rdiag := by
    dsimp only [B, a0, rdiag]
    change Book.Ch02.constantFullBlockMatrixSqrt
      (scalarMatrix (d := d) (sigma : ℝ)) = _
    simpa only using
      (Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
        sigma.property)
  have hReflectEntries : ∀ alpha beta, Integrable
      (fun a : RegCoeffField d =>
        blockMatEntry
          (blockReflect
            (coarseBlockMatrix (cubeSet (originCube d (-c))) a.toFun))
          alpha beta) P := by
    intro alpha beta
    cases alpha with
    | inl i =>
        cases beta with
        | inl j =>
            simpa [blockReflect, blockMatEntry, P] using
              relativeNormalizedCutoffLaw_integrable_blockMatEntryAtScale_int
                M L (-c) (Sum.inr i) (Sum.inr j)
        | inr j =>
            simpa [blockReflect, blockMatEntry, P] using
              relativeNormalizedCutoffLaw_integrable_blockMatEntryAtScale_int
                M L (-c) (Sum.inr i) (Sum.inl j)
    | inr i =>
        cases beta with
        | inl j =>
            simpa [blockReflect, blockMatEntry, P] using
              relativeNormalizedCutoffLaw_integrable_blockMatEntryAtScale_int
                M L (-c) (Sum.inl i) (Sum.inr j)
        | inr j =>
            simpa [blockReflect, blockMatEntry, P] using
              relativeNormalizedCutoffLaw_integrable_blockMatEntryAtScale_int
                M L (-c) (Sum.inl i) (Sum.inl j)
  have hReflectQuadInt : Integrable
      (fun a : RegCoeffField d =>
        blockVecDot Qv
          (blockMatVecMul
            (blockReflect
              (coarseBlockMatrix (cubeSet (originCube d (-c))) a.toFun)) Qv)) P :=
    Book.Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
      hReflectEntries Qv Qv
  have hReflectIntegral :
      (∫ a,
          blockVecDot Qv
            (blockMatVecMul
              (blockReflect
                (coarseBlockMatrix (cubeSet (originCube d (-c))) a.toFun)) Qv) ∂P) =
        blockVecDot Qv (blockMatVecMul (blockReflect Cchild) Qv) := by
    have h := Book.Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
      hReflectEntries Qv Qv
    simpa [Cchild, Book.Ch04.annealedBlockMatrixAtScale,
      Book.Ch04.annealedBlockMatrix, blockReflect] using h
  have hpoint (a : RegCoeffField d) :
      fullBlockQuadratic
          (starredFluctuationMatrix B C0
            (cubeSet (originCube d (-c))) a) q =
        blockVecDot Qv
            (blockMatVecMul
              (blockReflect
                (coarseBlockMatrix (cubeSet (originCube d (-c))) a.toFun)) Qv) -
          blockVecDot Qv (blockMatVecMul (blockReflect C0) Qv) := by
    simp only [starredFluctuationMatrix, starredInverseCoarseBlockMatrix]
    rw [Matrix.mul_sub, Matrix.sub_mul, fullBlockQuadratic_sub]
    rw [hSdiag]
    rw [diagonalForm_eq_dotProduct,
      diagonalForm_eq_dotProduct]
  have hdet :
      fullBlockQuadratic
          (CFC.sqrt B *
            (toFullBlockMat (blockReflect Cchild) -
              toFullBlockMat (blockReflect C0)) * CFC.sqrt B) q =
        blockVecDot Qv (blockMatVecMul (blockReflect Cchild) Qv) -
          blockVecDot Qv (blockMatVecMul (blockReflect C0) Qv) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, fullBlockQuadratic_sub]
    rw [hSdiag]
    rw [diagonalForm_eq_dotProduct,
      diagonalForm_eq_dotProduct]
  dsimp only
  rw [show (∫ a,
      fullBlockQuadratic
        (starredFluctuationMatrix B C0
          (cubeSet (originCube d (-c))) a) q ∂P) =
      ∫ a,
        (blockVecDot Qv
            (blockMatVecMul
              (blockReflect
                (coarseBlockMatrix (cubeSet (originCube d (-c))) a.toFun)) Qv) -
          blockVecDot Qv (blockMatVecMul (blockReflect C0) Qv)) ∂P by
        exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_sub hReflectQuadInt (integrable_const _)]
  rw [hReflectIntegral, integral_const]
  simpa [Measure.real, IsProbabilityMeasure.measure_univ] using hdet.symm

private theorem starredDescendantProbe_eq_centeredComparator_add_meanDefect
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    (q : FullBlockVec d) (a : RegCoeffField d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let center : ℤ := n - L - c
    let Q : TriadicCube d := originCube d center
    let j : ℕ := (n - L).toNat
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
    let X : Set (Vec d) → RegCoeffField d → ℝ := fun U b =>
      fullBlockQuadratic (starredFluctuationMatrix B C0 U b) q
    fullBlockQuadratic
        (starredDescendantsAverageFluctuationMatrix B Cn Q j a) q =
      Book.Ch04.restrictionCenteredDescendantAverage P (-c) center X a +
        ((∫ b, X (cubeSet (originCube d (-c))) b ∂P) +
          fullBlockQuadratic
            (CFC.sqrt B *
              (toFullBlockMat (blockReflect C0) -
                toFullBlockMat (blockReflect Cn)) * CFC.sqrt B) q) := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let center : ℤ := n - L - c
  let Q : TriadicCube d := originCube d center
  let j : ℕ := (n - L).toNat
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let X : Set (Vec d) → RegCoeffField d → ℝ := fun U b =>
    fullBlockQuadratic (starredFluctuationMatrix B C0 U b) q
  have hdepth : descendantsAtDepth Q j = descendantsAtScale Q (-c) := by
    have hcQ : -c ≤ Q.scale := by simp [Q, center, originCube]; omega
    rw [descendantsAtScale_eq_descendantsAtDepth Q hcQ]
    congr 1
    simp [Q, center, j, originCube]
  dsimp only
  unfold starredDescendantsAverageFluctuationMatrix
  rw [Book.Ch05.Section56.SmallContrastAssembly.fullBlockQuadratic_descendantsAverageFullBlockMat]
  unfold descendantsAverage Book.Ch04.restrictionCenteredDescendantAverage
  rw [hdepth]
  dsimp only
  let mu0 : ℝ := ∫ b, X (cubeSet (originCube d (-c))) b ∂P
  let defect : ℝ := fullBlockQuadratic
    (CFC.sqrt B *
      (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
        CFC.sqrt B) q
  have hcardNe : ((descendantsAtScale Q (-c)).card : ℝ) ≠ 0 := by
    have hcQ : -c ≤ Q.scale := by simp [Q, center, originCube]; omega
    exact_mod_cast (descendantsAtScale_nonempty Q hcQ).card_ne_zero
  have hpoint (R : TriadicCube d) :
      fullBlockQuadratic (starredFluctuationMatrix B Cn (cubeSet R) a) q =
        X (cubeSet R) a + defect := by
    have hmat : starredFluctuationMatrix B Cn (cubeSet R) a =
        starredFluctuationMatrix B C0 (cubeSet R) a +
          CFC.sqrt B *
            (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
              CFC.sqrt B := by
      unfold starredFluctuationMatrix
      noncomm_ring
    rw [hmat]
    dsimp only [X, defect]
    unfold fullBlockQuadratic
    rw [Matrix.add_mulVec, dotProduct_add]
  rw [show (∑ R ∈ descendantsAtScale Q (-c),
      fullBlockQuadratic (starredFluctuationMatrix B Cn (cubeSet R) a) q) =
      ∑ R ∈ descendantsAtScale Q (-c), (X (cubeSet R) a + defect) by
        exact Finset.sum_congr rfl fun R _hR => hpoint R]
  change ((descendantsAtScale Q (-c)).card : ℝ)⁻¹ *
      (∑ R ∈ descendantsAtScale Q (-c), (X (cubeSet R) a + defect)) =
    ((descendantsAtScale Q (-c)).card : ℝ)⁻¹ *
        (∑ R ∈ descendantsAtScale Q (-c), (X (cubeSet R) a - mu0)) +
      (mu0 + defect)
  field_simp [hcardNe]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

private theorem annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_int
    {d : ℕ} [NeZero d] (M : ABKModel d) (L r : ℤ) :
    Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.relativeNormalizedCutoffLaw M L) r =
      Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M L)
        (L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ) + r) := by
  let dilation : ℤ := -(L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ))
  let hPmap : Book.Ch04.RestrictionLawCarrier
      (Measure.map (dilateReg dilation) (Cutoff.coefficientCutoffLaw M L)) := by
    simpa [dilation, Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg] using
      Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  have hmatrix := annealedBlockMatrix_map_dilateReg_cube
    (Cutoff.coefficientCutoffLaw_lawCarrier M L) dilation hPmap
    (originCube d r)
  simpa [Book.Ch04.annealedBlockMatrixAtScale, dilation,
    Book.Ch02.dilateCube, originCube, add_assoc, add_comm, add_left_comm,
    Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg] using hmatrix

private theorem relativeNormalizedCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ) {n k : ℤ}
    (hnk : n ≤ k) :
    BlockMatLoewnerLE
      (Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.relativeNormalizedCutoffLaw M L) k)
      (Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.relativeNormalizedCutoffLaw M L) n) := by
  rw [annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_int,
    annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_int]
  exact Provider.Annealed.coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
    M L (by omega)

private theorem barSigmaLimit_le_barSigmaAtScale_of_P4
    {d : ℕ} [NeZero d] {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Book.Ch05.QuantitativeCoarseGrainedEllipticity P) (n : ℕ) :
    Book.Ch05.Section57.barSigmaLimit hP hStruct ≤
      hP.barSigmaAtScale hStruct (n : ℤ) := by
  have hbdd : BddBelow
      (Set.range fun m : ℕ => hP.barSigmaAtScale hStruct (m : ℤ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact (Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m).le
  exact csInf_le hbdd ⟨n, rfl⟩

private theorem barSigmaStarAtScale_le_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Book.Ch04.RestrictionCoeffLaw d}
    (hP : Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Book.Ch05.QuantitativeCoarseGrainedEllipticity P) (n : ℕ) :
    hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
      Book.Ch05.Section57.barSigmaLimit hP hStruct := by
  refine le_csInf (Set.range_nonempty _) ?_
  rintro y ⟨m, rfl⟩
  by_cases hnm : n ≤ m
  · exact
      ((Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
          hP hStruct hP4 hnm).1).trans
        (Book.Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
          hP hStruct hP4 m)
  · have hmn : m ≤ n := by omega
    exact
      (Book.Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
          hP hStruct hP4 n).trans
        ((Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
          hP hStruct hP4 hmn).2.2)

private theorem constantBlockMatrix_sigmaBar_blockMatLoewnerLE_scalarAnnealed
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ) (n : ℕ) :
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let sigma := Annealed.sigmaBar M L
    BlockMatLoewnerLE
      (Book.Ch02.constantBlockMatrix
        (Observable.isotropicComparatorMatrix sigma))
      (Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (n : ℤ)) := by
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let hP4 := Cutoff.relativeNormalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L
  let sigma := Annealed.sigmaBar M L
  let b := hP.barSigmaAtScale hStruct (n : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (n : ℤ)
  have hlimit : Book.Ch05.Section57.barSigmaLimit hP hStruct = (sigma : ℝ) := by
    simpa only [hP, hStruct, sigma] using
      relativeNormalizedCutoff_barSigmaLimit_eq_sigmaBar M L
  have hsigmaLe : (sigma : ℝ) ≤ b := by
    rw [← hlimit]
    exact barSigmaLimit_le_barSigmaAtScale_of_P4 hP hStruct hP4 n
  have hcLe : c ≤ (sigma : ℝ) := by
    rw [← hlimit]
    exact barSigmaStarAtScale_le_barSigmaLimit_of_P4 hP hStruct hP4 n
  have hcPos : 0 < c := by
    simpa only [c] using
      Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 n
  have hinv : (sigma : ℝ)⁻¹ ≤ c⁻¹ :=
    (inv_le_inv₀ sigma.property hcPos).2 hcLe
  dsimp only
  intro X
  rcases X with ⟨p, q⟩
  rw [show Observable.isotropicComparatorMatrix sigma =
      scalarMatrix (d := d) (sigma : ℝ) by
        rfl]
  rw [Book.Ch02.constantBlockMatrix_scalarMatrix sigma.property]
  change (1 / 2 : ℝ) * blockVecDot (p, q)
      (blockMatVecMul
        (Book.Ch02.blockDiag ((sigma : ℝ) • (1 : Mat d))
          ((sigma : ℝ)⁻¹ • (1 : Mat d))) (p, q)) ≤
    (1 / 2 : ℝ) * blockVecDot (p, q)
      (blockMatVecMul
        (Book.Ch02.blockDiag (b • (1 : Mat d)) (c⁻¹ • (1 : Mat d))) (p, q))
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one]
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one]
  nlinarith [vecNormSq_nonneg p, vecNormSq_nonneg q]

private theorem constantBlockMatrix_sigmaBar_blockMatLoewnerLE_scalarAnnealed_int
    {d : ℕ} [NeZero d] (M : ABKModel d) (L r : ℤ) :
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let sigma := Annealed.sigmaBar M L
    BlockMatLoewnerLE
      (Book.Ch02.constantBlockMatrix
        (Observable.isotropicComparatorMatrix sigma))
      (Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct r) := by
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let hP4 := Cutoff.relativeNormalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L
  let sigma := Annealed.sigmaBar M L
  by_cases hr : 0 ≤ r
  · have hrNat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr
    simpa only [hP, hStruct, sigma, hrNat] using
      constantBlockMatrix_sigmaBar_blockMatLoewnerLE_scalarAnnealed M L r.toNat
  · have hr0 : r ≤ 0 := by omega
    have hbase := constantBlockMatrix_sigmaBar_blockMatLoewnerLE_scalarAnnealed M L 0
    have hmono :=
      relativeNormalizedCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
        M L hr0
    have hzero : Book.Ch04.annealedBlockMatrixAtScale P 0 =
        Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct 0 := by
      simpa only [P, hP, hStruct] using
        Book.Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
          hP hStruct 0
    have hrmat : Book.Ch04.annealedBlockMatrixAtScale P r =
        Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct r := by
      simpa only [P, hP, hStruct] using
        Book.Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
          hP hStruct r
    rw [hzero, hrmat] at hmono
    have hbase' : BlockMatLoewnerLE
        (Book.Ch02.constantBlockMatrix
          (Observable.isotropicComparatorMatrix sigma))
        (Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct 0) := by
      simpa only [hP, hStruct, sigma] using! hbase
    exact hbase'.trans hmono

private theorem relativeMeanDefect_nonneg_and_le_originMean
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let center : ℤ := n - L - c
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
    let X : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
      fullBlockQuadratic (starredFluctuationMatrix B C0 U a) q
    let meanDefect : ℝ :=
      (∫ a, X (cubeSet (originCube d (-c))) a ∂P) +
        fullBlockQuadratic
          (CFC.sqrt B *
            (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
              CFC.sqrt B) q
    0 ≤ meanDefect ∧
      meanDefect ≤ ∫ a, X (cubeSet (originCube d (-c))) a ∂P := by
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let hP4 := Cutoff.relativeNormalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L
  let center : ℤ := n - L - c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let Cchild : BlockMat d := Book.Ch04.annealedBlockMatrixAtScale P (-c)
  let X : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
    fullBlockQuadratic (starredFluctuationMatrix B C0 U a) q
  let meanDefect : ℝ :=
    (∫ a, X (cubeSet (originCube d (-c))) a ∂P) +
      fullBlockQuadratic
        (CFC.sqrt B *
          (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
            CFC.sqrt B) q
  let rdiag := Book.Ch05.Section56.scalarFullBlockSqrtDiag
    (d := d) (sigma : ℝ) (sigma : ℝ)
  let Qv : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Matrix.diagonal rdiag) q)
  have hSdiag : CFC.sqrt B = Matrix.diagonal rdiag := by
    dsimp only [B, a0, rdiag]
    change Book.Ch02.constantFullBlockMatrixSqrt
      (scalarMatrix (d := d) (sigma : ℝ)) = _
    simpa only using
      (Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
        sigma.property)
  have hquad (A₁ A₂ : BlockMat d) :
      fullBlockQuadratic
          (CFC.sqrt B *
            (toFullBlockMat (blockReflect A₁) - toFullBlockMat (blockReflect A₂)) *
              CFC.sqrt B) q =
        blockVecDot Qv (blockMatVecMul (blockReflect A₁) Qv) -
          blockVecDot Qv (blockMatVecMul (blockReflect A₂) Qv) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, fullBlockQuadratic_sub]
    rw [hSdiag]
    rw [diagonalForm_eq_dotProduct,
      diagonalForm_eq_dotProduct]
  have hmu : (∫ a, X (cubeSet (originCube d (-c))) a ∂P) =
      fullBlockQuadratic
        (CFC.sqrt B *
          (toFullBlockMat (blockReflect Cchild) -
            toFullBlockMat (blockReflect C0)) * CFC.sqrt B) q := by
    simpa only [P, c, sigma, a0, B, C0, Cchild, X] using
      integral_starredComparator_relativeOrigin_eq_annealedGap M L q
  have hmeanEq : meanDefect =
      fullBlockQuadratic
        (CFC.sqrt B *
          (toFullBlockMat (blockReflect Cchild) -
            toFullBlockMat (blockReflect Cn)) * CFC.sqrt B) q := by
    dsimp only [meanDefect]
    rw [hmu, hquad, hquad, hquad]
    ring
  have hchildCenter : -c ≤ center := by
    dsimp only [c, center]
    omega
  have hCnActual : Book.Ch04.annealedBlockMatrixAtScale P center = Cn := by
    simpa only [P, hP, hStruct, Cn] using
      Book.Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
        hP hStruct center
  have hCnChild : BlockMatLoewnerLE Cn Cchild := by
    rw [← hCnActual]
    simpa only [P, Cchild] using
      relativeNormalizedCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
        M L hchildCenter
  have hC0Cn : BlockMatLoewnerLE C0 Cn := by
    have hbase :=
      constantBlockMatrix_sigmaBar_blockMatLoewnerLE_scalarAnnealed_int M L center
    simpa only [hP, hStruct, sigma, a0, C0, Cn] using hbase
  have hnonneg : 0 ≤ meanDefect := by
    rw [hmeanEq, hquad]
    have horder := (Book.Ch04.blockMatLoewnerLE_blockReflect hCnChild) Qv
    linarith
  have hleMu : meanDefect ≤ ∫ a, X (cubeSet (originCube d (-c))) a ∂P := by
    rw [hmeanEq, hmu, hquad, hquad]
    have horder := (Book.Ch04.blockMatLoewnerLE_blockReflect hC0Cn) Qv
    linarith
  dsimp only
  exact ⟨hnonneg, hleMu⟩

private theorem relativeMeanDefect_sq_le_secondBudget_sq
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    {s A D : ℝ} (hs : 0 < s)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨s, hs⟩) A D)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let center : ℤ := n - L - c
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
    let X : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
      fullBlockQuadratic (starredFluctuationMatrix B C0 U a) q
    let meanDefect : ℝ :=
      (∫ a, X (cubeSet (originCube d (-c))) a ∂P) +
        fullBlockQuadratic
          (CFC.sqrt B *
            (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
              CFC.sqrt B) q
    let secondBudget : ℝ :=
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
    meanDefect ^ (2 : ℕ) ≤
      4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ) := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let center : ℤ := n - L - c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let Cchild : BlockMat d := Book.Ch04.annealedBlockMatrixAtScale P (-c)
  let R : TriadicCube d := originCube d (-c)
  let Afun : RegCoeffField d → BlockMat d := fun a =>
    coarseBlockMatrix (cubeSet R) a.toFun
  let Pq : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt a0) q)
  let Qq : BlockVec d := ofFullBlockVec
    (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt a0) q)
  let J : RegCoeffField d → ℝ := fun a =>
    (1 / 2 : ℝ) * blockVecDot Pq (blockMatVecMul (Afun a) Pq) +
      (1 / 2 : ℝ) * blockVecDot Qq (blockMatVecMul (blockReflect (Afun a)) Qq) -
        blockVecDot Pq Qq
  let X : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
    fullBlockQuadratic (starredFluctuationMatrix B C0 U a) q
  let meanDefect : ℝ :=
    (∫ a, X (cubeSet R) a ∂P) +
      fullBlockQuadratic
        (CFC.sqrt B *
          (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
            CFC.sqrt B) q
  let X0 := Observable.cutoffHomogenizationError M L ⟨s, hs⟩
  let secondBudget : ℝ :=
    2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
  have hsign := relativeMeanDefect_nonneg_and_le_originMean M L n hLn q
  have hmeanNonneg : 0 ≤ meanDefect := by
    simpa only [P, c, hP, hStruct, center, sigma, a0, B, C0, Cn, R, X,
      meanDefect] using hsign.1
  have hmeanLeMu : meanDefect ≤ ∫ a, X (cubeSet R) a ∂P := by
    simpa only [P, c, hP, hStruct, center, sigma, a0, B, C0, Cn, R, X,
      meanDefect] using hsign.2
  have hentry : ∀ alpha beta, Integrable
      (fun a => blockMatEntry (Afun a) alpha beta) P := by
    simpa only [Afun, R, P] using
      relativeNormalizedCutoffLaw_integrable_blockMatEntryAtScale_int M L (-c)
  have hreflectEntry : ∀ alpha beta, Integrable
      (fun a => blockMatEntry (blockReflect (Afun a)) alpha beta) P := by
    intro alpha beta
    cases alpha with
    | inl i =>
        cases beta with
        | inl j => simpa [blockReflect, blockMatEntry] using hentry (Sum.inr i) (Sum.inr j)
        | inr j => simpa [blockReflect, blockMatEntry] using hentry (Sum.inr i) (Sum.inl j)
    | inr i =>
        cases beta with
        | inl j => simpa [blockReflect, blockMatEntry] using hentry (Sum.inl i) (Sum.inr j)
        | inr j => simpa [blockReflect, blockMatEntry] using hentry (Sum.inl i) (Sum.inl j)
  have hprimalInt : Integrable
      (fun a => blockVecDot Pq (blockMatVecMul (Afun a) Pq)) P :=
    Book.Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
      hentry Pq Pq
  have hstarInt : Integrable
      (fun a => blockVecDot Qq (blockMatVecMul (blockReflect (Afun a)) Qq)) P :=
    Book.Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
      hreflectEntry Qq Qq
  have hJInt : Integrable J P :=
    ((hprimalInt.const_mul (1 / 2 : ℝ)).add
      (hstarInt.const_mul (1 / 2 : ℝ))).sub (integrable_const _)
  have hprimalMean :
      (∫ a, blockVecDot Pq (blockMatVecMul (Afun a) Pq) ∂P) =
        blockVecDot Pq (blockMatVecMul Cchild Pq) := by
    have hmean := Book.Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
      hentry Pq Pq
    simpa [Cchild, Book.Ch04.annealedBlockMatrixAtScale,
      Book.Ch04.annealedBlockMatrix, Afun, R] using hmean
  have hstarMean :
      (∫ a, blockVecDot Qq (blockMatVecMul (blockReflect (Afun a)) Qq) ∂P) =
        blockVecDot Qq (blockMatVecMul (blockReflect Cchild) Qq) := by
    have hmean := Book.Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
      hreflectEntry Qq Qq
    simpa [Cchild, Book.Ch04.annealedBlockMatrixAtScale,
      Book.Ch04.annealedBlockMatrix, Afun, R, blockReflect] using hmean
  have hJMean : (∫ a, J a ∂P) =
      (1 / 2 : ℝ) * blockVecDot Pq (blockMatVecMul Cchild Pq) +
        (1 / 2 : ℝ) * blockVecDot Qq (blockMatVecMul (blockReflect Cchild) Qq) -
          blockVecDot Pq Qq := by
    dsimp only [J]
    rw [integral_sub, integral_add, integral_const_mul, integral_const_mul,
      integral_const, hprimalMean, hstarMean]
    · simp [Measure.real, IsProbabilityMeasure.measure_univ]
    · exact hprimalInt.const_mul (1 / 2 : ℝ)
    · exact hstarInt.const_mul (1 / 2 : ℝ)
    · exact (hprimalInt.const_mul (1 / 2 : ℝ)).add
        (hstarInt.const_mul (1 / 2 : ℝ))
    · exact integrable_const _
  have hQv : blockMatVecMul C0 Pq = Qq := by
    dsimp only [C0, Pq, Qq, a0]
    change blockMatVecMul
      (Book.Ch02.constantBlockMatrix (scalarMatrix (d := d) (sigma : ℝ)))
      (ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixInvSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)) =
      ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)
    rw [Book.Ch02.constantBlockMatrix_scalarMatrix sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix
      sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix
      sigma.property]
    ext i <;>
      simp [blockMatVecMul, zero_matVecMul, matVecMul_scalarMatrix] <;>
      field_simp [ne_of_gt (Real.sqrt_pos.2 sigma.property)] <;>
      rw [Real.sq_sqrt sigma.property.le];
      field_simp [ne_of_gt sigma.property]
  have hreflectQv : blockMatVecMul (blockReflect C0) Qq = Pq := by
    dsimp only [C0, Pq, Qq, a0]
    change blockMatVecMul
      (blockReflect
        (Book.Ch02.constantBlockMatrix (scalarMatrix (d := d) (sigma : ℝ))))
      (ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)) =
      ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixInvSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)
    rw [Book.Ch02.constantBlockMatrix_scalarMatrix sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix
      sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix
      sigma.property]
    ext i <;>
      simp [blockReflect, blockMatVecMul, zero_matVecMul, matVecMul_scalarMatrix] <;>
      field_simp [ne_of_gt (Real.sqrt_pos.2 sigma.property)] <;>
      rw [Real.sq_sqrt sigma.property.le];
      field_simp [ne_of_gt sigma.property]
  have hpair : blockVecDot Pq Qq = dotProduct q q := by
    have hnormalizers :=
      Book.Ch05.Section57.blockVecDot_scalarConstantNormalizers_eq_fullBlockVecNormSq
        sigma.property q
    simpa [Pq, Qq, a0, Observable.isotropicComparatorMatrix,
      Book.Ch02.fullBlockVecNormSq, dotProduct, pow_two] using hnormalizers
  have hC0Child : BlockMatLoewnerLE C0 Cchild := by
    have hbase :=
      constantBlockMatrix_sigmaBar_blockMatLoewnerLE_scalarAnnealed_int M L (-c)
    have hactual : Cchild = Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (-c) := by
      simpa only [P, Cchild] using
        Book.Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
          hP hStruct (-c)
    rw [hactual]
    simpa only [hP, hStruct, sigma, a0, C0] using hbase
  have hprimalGap : blockVecDot Pq Qq ≤
      blockVecDot Pq (blockMatVecMul Cchild Pq) := by
    rw [← hQv]
    have horder := hC0Child Pq
    linarith
  let rdiag := Book.Ch05.Section56.scalarFullBlockSqrtDiag
    (d := d) (sigma : ℝ) (sigma : ℝ)
  have hSdiag : CFC.sqrt B = Matrix.diagonal rdiag := by
    dsimp only [B, a0, rdiag]
    change Book.Ch02.constantFullBlockMatrixSqrt
      (scalarMatrix (d := d) (sigma : ℝ)) = _
    simpa only using
      (Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
        sigma.property)
  have hQdiag : ofFullBlockVec (Matrix.mulVec (Matrix.diagonal rdiag) q) = Qq := by
    rw [← hSdiag]
    rfl
  have hmuEq : (∫ a, X (cubeSet R) a ∂P) =
      blockVecDot Qq (blockMatVecMul (blockReflect Cchild) Qq) -
        blockVecDot Pq Qq := by
    have hmu : (∫ a, X (cubeSet R) a ∂P) =
        fullBlockQuadratic
          (CFC.sqrt B *
            (toFullBlockMat (blockReflect Cchild) -
              toFullBlockMat (blockReflect C0)) * CFC.sqrt B) q := by
      simpa only [P, c, sigma, a0, B, C0, Cchild, R, X] using
        integral_starredComparator_relativeOrigin_eq_annealedGap M L q
    rw [hmu, Matrix.mul_sub, Matrix.sub_mul, fullBlockQuadratic_sub, hSdiag,
      diagonalForm_eq_dotProduct,
      diagonalForm_eq_dotProduct]
    rw [hQdiag, hreflectQv, blockVecDot_comm Qq Pq]
  have hmuLeJ : (∫ a, X (cubeSet R) a ∂P) ≤ 2 * ∫ a, J a ∂P := by
    rw [hmuEq, hJMean]
    nlinarith
  have hErr := cutoffError_sq_integrable_and_le_of_twoTerm M L hs hLower
  have hX0sqInt : Integrable (fun omega => X0 omega ^ (2 : ℕ)) mu := by
    simpa only [X0, mu] using hErr.1
  have hX0sqBound : (∫ omega, X0 omega ^ (2 : ℕ) ∂mu) ≤ secondBudget := by
    simpa only [X0, mu, secondBudget] using hErr.2
  have hJcoeffInt : Integrable (J ∘ dilateReg (-h))
      (Cutoff.coefficientCutoffLaw M L) := by
    have hrelLaw : P = Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L) := by
      simpa only [P, h, c] using Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg M L
    have hJMap : Integrable J
        (Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L)) := by
      simpa only [← hrelLaw] using hJInt
    exact (integrable_map_measure hJMap.aestronglyMeasurable
      (measurable_dilateReg (d := d) (-h)).aemeasurable).mp hJMap
  have hJsampleInt : Integrable
      (fun omega => J (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega))) mu := by
    have hcoeff := hJcoeffInt
    rw [Cutoff.coefficientCutoffLaw_eq_map] at hcoeff
    exact (integrable_map_measure hcoeff.aestronglyMeasurable
      (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable).mp hcoeff
  have hJsamplePoint :
      (fun omega => J (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega))) ≤ᵐ[mu]
        fun omega => dotProduct q q * X0 omega ^ (2 : ℕ) := by
    have hraw := Observable.cutoffHomogenizationError_ae_eq_raw M L ⟨s, hs⟩
    filter_upwards [hraw] with omega hrawOmega
    let aPhys : RegCoeffField d := Cutoff.coefficientCutoff M.nu L omega
    let haPhys : Book.Ch04.AELocallyUniformlyEllipticField aPhys :=
      Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
    let aRel : RegCoeffField d := dilateReg (-h) aPhys
    let haRel : Book.Ch04.AELocallyUniformlyEllipticField aRel :=
      Cutoff.aelocallyUniformlyEllipticField_dilateReg haPhys (-h)
    let Frel : Book.Ch02.TriadicCoeffFamily d :=
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aRel haRel
    have hcoarse : Afun aRel =
        Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R) (Frel.coeffOn R) := by
      simpa only [Afun] using
        Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
          haRel R
    have hstar :=
      (Book.Ch02.blockCoarseMatrixTheory
        (Book.Ch02.cubeDomain R) (Frel.coeffOn R)).starred_inverse_formula
    have hsplit :=
      (Book.Ch02.blockCoarseMatrixTheory
        (Book.Ch02.cubeDomain R) (Frel.coeffOn R)).doubled_response_splitting Pq Qq
    have hJeq : J aRel =
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (Frel.coeffOn R) Pq Qq := by
      dsimp only [J]
      rw [hsplit]
      rw [hcoarse]
      rw [hstar]
    have hb := relativeOrigin_doubledResponseJ_le_normSq_mul_cutoffError_sq
      M L hs omega q
    dsimp only [h, aPhys, aRel, Frel, haPhys, haRel] at hJeq hb
    rw [hJeq]
    rw [← hrawOmega] at hb
    simpa only [X0] using hb
  have hJIntegralSample : (∫ a, J a ∂P) =
      ∫ omega, J (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ∂mu := by
    have hrelLaw : P = Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L) := by
      simpa only [P, h, c] using Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg M L
    have hJMapMeas : AEStronglyMeasurable J
        (Measure.map (dilateReg (-h)) (Cutoff.coefficientCutoffLaw M L)) := by
      simpa only [← hrelLaw] using hJInt.aestronglyMeasurable
    have hJcoeffMapMeas : AEStronglyMeasurable (J ∘ dilateReg (-h))
        (Measure.map (Cutoff.coefficientCutoff M.nu L) mu) := by
      simpa only [← Cutoff.coefficientCutoffLaw_eq_map, mu] using
        hJcoeffInt.aestronglyMeasurable
    calc
      (∫ a, J a ∂P) =
          ∫ a, J (dilateReg (-h) a) ∂(Cutoff.coefficientCutoffLaw M L) := by
        rw [hrelLaw]
        exact MeasureTheory.integral_map
          (measurable_dilateReg (d := d) (-h)).aemeasurable hJMapMeas
      _ = ∫ omega, J (dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)) ∂mu := by
        rw [Cutoff.coefficientCutoffLaw_eq_map]
        exact MeasureTheory.integral_map
          (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable hJcoeffMapMeas
  have hqNonneg : 0 ≤ dotProduct q q := dotProduct_self_nonneg q
  have hJBound : (∫ a, J a ∂P) ≤ dotProduct q q * secondBudget := by
    rw [hJIntegralSample]
    calc
      _ ≤ ∫ omega, dotProduct q q * X0 omega ^ (2 : ℕ) ∂mu :=
        integral_mono_ae hJsampleInt (hX0sqInt.const_mul _) hJsamplePoint
      _ = dotProduct q q * ∫ omega, X0 omega ^ (2 : ℕ) ∂mu := by
        rw [integral_const_mul]
      _ ≤ dotProduct q q * secondBudget :=
        mul_le_mul_of_nonneg_left hX0sqBound hqNonneg
  dsimp only
  have hmeanLe : meanDefect ≤ 2 * dotProduct q q * secondBudget :=
    hmeanLeMu.trans (hmuLeJ.trans (by nlinarith))
  have hsecondNonneg : 0 ≤ secondBudget := by
    dsimp only [secondBudget]
    positivity
  have hrhsNonneg : 0 ≤ 2 * dotProduct q q * secondBudget := by positivity
  have hsq := (sq_le_sq₀ hsign.1 hrhsNonneg).2 hmeanLe
  calc meanDefect ^ (2 : ℕ) ≤ (2 * dotProduct q q * secondBudget) ^ (2 : ℕ) := hsq
    _ = 4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ) := by ring

/-- Second-moment control of an arbitrary quadratic probe of the actual
relative descendant-average fluctuation matrix. -/
theorem relativeStarredDescendantProbe_sq_integrable_and_le
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    {s A D : ℝ} (hs : 0 < s)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨s, hs⟩) A D)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let center : ℤ := n - L - c
    let Q : TriadicCube d := originCube d center
    let j : ℕ := (n - L).toNat
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
    let Y : RegCoeffField d → ℝ := fun a =>
      fullBlockQuadratic
        (starredDescendantsAverageFluctuationMatrix B Cn Q j a) q
    let N : ℝ := ((descendantsAtScale Q (-c)).card : ℝ)
    let budget : ℝ :=
      2 *
          ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
        8 *
          ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
    let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
    let secondBudget : ℝ :=
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
    let meanBudget : ℝ :=
      4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
    let K : ℝ := Real.sqrt probeBudget
    let rootBound : ℝ :=
      N⁻¹ *
        (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
              N ^ (1 / (2 : ℝ)) * K +
          Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
              Real.sqrt N * K)
    Integrable (fun a => (Y a) ^ (2 : ℕ)) P ∧
      (∫ a, (Y a) ^ (2 : ℕ) ∂P) ≤
        2 * rootBound ^ (2 : ℕ) + 2 * meanBudget := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let center : ℤ := n - L - c
  let Q : TriadicCube d := originCube d center
  let j : ℕ := (n - L).toNat
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let Cn : BlockMat d := Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let X : Set (Vec d) → RegCoeffField d → ℝ := fun U a =>
    fullBlockQuadratic (starredFluctuationMatrix B C0 U a) q
  let Z : RegCoeffField d → ℝ :=
    Book.Ch04.restrictionCenteredDescendantAverage P (-c) center X
  let meanDefect : ℝ :=
    (∫ a, X (cubeSet (originCube d (-c))) a ∂P) +
      fullBlockQuadratic
        (CFC.sqrt B *
          (toFullBlockMat (blockReflect C0) - toFullBlockMat (blockReflect Cn)) *
            CFC.sqrt B) q
  let Y : RegCoeffField d → ℝ := fun a =>
    fullBlockQuadratic
      (starredDescendantsAverageFluctuationMatrix B Cn Q j a) q
  let N : ℝ := ((descendantsAtScale Q (-c)).card : ℝ)
  let budget : ℝ :=
    2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
  let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
  let secondBudget : ℝ :=
    2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
  let meanBudget : ℝ :=
    4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
  let K : ℝ := Real.sqrt probeBudget
  let rootBound : ℝ :=
    N⁻¹ *
      (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
            N ^ (1 / (2 : ℝ)) * K +
        Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
            Real.sqrt N * K)
  have hMom := relativeStarredComparator_origin_and_descendant_moment_bounds
    M L n hLn hs hLower q
  have hZsqInt : Integrable (fun a => (Z a) ^ (2 : ℕ)) P := by
    have habs : Integrable (fun a => |Z a| ^ (2 : ℕ)) P := by
      simpa only [P, c, sigma, a0, B, C0, X, center, Q, N, budget,
        probeBudget, K] using hMom.2.2.1
    refine habs.congr ?_
    filter_upwards with a
    rw [sq_abs]
  have hroot : (∫ a, (Z a) ^ (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) ≤ rootBound := by
    simpa only [P, c, sigma, a0, B, C0, X, center, Q, N, budget,
      probeBudget, K, Z, sq_abs] using hMom.2.2.2
  have hmean := relativeMeanDefect_sq_le_secondBudget_sq
    M L n hLn hs hLower q
  have hmeanSq : meanDefect ^ (2 : ℕ) ≤ meanBudget := by
    simpa only [P, c, hP, hStruct, center, sigma, a0, B, C0, Cn, X,
      meanDefect, secondBudget, meanBudget] using hmean
  have hYeq : ∀ a, Y a = Z a + meanDefect := by
    intro a
    simpa only [P, c, hP, hStruct, center, Q, j, sigma, a0, B, C0, Cn,
      X, Z, meanDefect, Y] using
      starredDescendantProbe_eq_centeredComparator_add_meanDefect
        M L n hLn q a
  let S : FullBlockMat d := blockSwapMat d * CFC.sqrt B
  have hMatMeas :=
    Book.Ch05.Section56.aemeasurable_descendantsAverageFluctuationMatrixWithNormalizer
      hP hStruct center S Q j
  let g : FullBlockMat d → ℝ := fun T => fullBlockQuadratic T q
  have hg : Measurable g := by
    exact (by
      have : Continuous g := by
        dsimp only [g]
        unfold fullBlockQuadratic
        fun_prop
      exact this.measurable)
  have hYMeas : AEMeasurable Y P := by
    refine (hg.comp_aemeasurable hMatMeas).congr ?_
    filter_upwards with a
    dsimp only [Function.comp_apply, g, Y]
    exact congrArg (fun T : FullBlockMat d => fullBlockQuadratic T q)
      (starredDescendantsAverageFluctuationMatrix_eq_descendantsAverageFluctuationMatrixWithNormalizer
        hP hStruct center B Q j a).symm
  have hdomInt : Integrable
      (fun a => 2 * (Z a) ^ (2 : ℕ) + 2 * meanDefect ^ (2 : ℕ)) P :=
    (hZsqInt.const_mul 2).add (integrable_const _)
  have hYsqInt : Integrable (fun a => (Y a) ^ (2 : ℕ)) P := by
    refine Integrable.mono' hdomInt (hYMeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with a
    rw [hYeq]
    have := sq_nonneg (Z a - meanDefect)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hZIntegralNonneg : 0 ≤ ∫ a, (Z a) ^ (2 : ℕ) ∂P :=
    integral_nonneg fun a => sq_nonneg _
  have hZIntegralBound :
      (∫ a, (Z a) ^ (2 : ℕ) ∂P) ≤ rootBound ^ (2 : ℕ) := by
    rw [← Real.sqrt_eq_rpow] at hroot
    have hrootNonneg : 0 ≤ rootBound := (Real.sqrt_nonneg _).trans hroot
    calc
      (∫ a, (Z a) ^ (2 : ℕ) ∂P) =
          Real.sqrt (∫ a, (Z a) ^ (2 : ℕ) ∂P) ^ (2 : ℕ) :=
        (Real.sq_sqrt hZIntegralNonneg).symm
      _ ≤ rootBound ^ (2 : ℕ) :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) hrootNonneg).2 hroot
  refine ⟨hYsqInt, ?_⟩
  calc
    (∫ a, (Y a) ^ (2 : ℕ) ∂P) ≤
        ∫ a, (2 * (Z a) ^ (2 : ℕ) + 2 * meanDefect ^ (2 : ℕ)) ∂P := by
      refine integral_mono hYsqInt hdomInt ?_
      intro a
      change Y a ^ (2 : ℕ) ≤ 2 * Z a ^ (2 : ℕ) + 2 * meanDefect ^ (2 : ℕ)
      rw [hYeq]
      nlinarith [sq_nonneg (Z a - meanDefect)]
    _ = 2 * (∫ a, (Z a) ^ (2 : ℕ) ∂P) + 2 * meanDefect ^ (2 : ℕ) := by
      rw [integral_add, integral_const_mul, integral_const]
      · simp [Measure.real, IsProbabilityMeasure.measure_univ]
      · exact hZsqInt.const_mul 2
      · exact integrable_const _
    _ ≤ 2 * rootBound ^ (2 : ℕ) + 2 * meanBudget := by
      nlinarith

end

end Algsuperdiff.Section3.Provider.Homogenization

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineFiniteVariance

/-!
# CombineFiniteCarrierTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
  (annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale)

/-!
# Carrier transport for the finite-corridor two-plus-eight estimate

The quantitative finite-corridor estimate of `CombineFiniteVariance` is stated
at the same-cutoff relative-normalized law `Cutoff.relativeNormalizedCutoffLaw
M L`, which is *exactly* the spatial pushforward `Measure.map (dilateReg (-(L +
c))) (Cutoff.coefficientCutoffLaw M L)` of the genuine coefficient cutoff law
(`cutoffRelativeNormalizationShift d = c` is dimension-only).  This module
supplies that missing half and chains it with the proved corridor estimate.

Under the dilation the relative cube at scale `n - (L + c)` corresponds to the
physical cube at scale `n`, which is the scale correspondence already used for
the annealed comparator (`annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw`).
The deterministic centering matrix is carried through unchanged: all transport
statements below are stated for an arbitrary deterministic `C : BlockMat d`, so
no centering convention is smuggled in.  The identification of that centering
with the genuine law's annealed block matrix at the physical scale `n` is
recorded separately in
`annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center` and, in the
scalar form actually carried by the corridor estimate, in
`scalarAnnealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center_eq`.

## Main results

* `starredFluctuationOperatorNormSq_dilateReg_of_aelocallyUniformlyElliptic`
* `integral_starredFluctuationOperatorNormSq_relativeNormalizedCutoffLaw`
* `integral_starredFluctuationOperatorNormSq_relativeNormalizedCutoffLaw_originCube`
* `scalarAnnealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center_eq`
* `exists_coefficientCutoff_finiteCorridor_starredFluctuationVariance_bound`
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch05.Section56

noncomputable section



variable {d : ℕ}

/-! ## The dilation as a measurable equivalence -/

/-- Triadic dilation of the coefficient carrier, packaged as a measurable
equivalence; its inverse is the opposite dilation. -/
def dilateRegEquiv (k : ℤ) : RegCoeffField d ≃ᵐ RegCoeffField d where
  toEquiv :=
    { toFun := dilateReg k
      invFun := dilateReg (-k)
      left_inv := by
        intro a
        apply RegCoeffField.ext
        intro x
        simp only [dilateReg_apply, smul_smul, zpow_neg]
        rw [inv_inv,
          inv_mul_cancel₀ (zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)), one_smul]
      right_inv := by
        intro a
        apply RegCoeffField.ext
        intro x
        simp only [dilateReg_apply, smul_smul, zpow_neg]
        rw [inv_inv,
          mul_inv_cancel₀ (zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)), one_smul] }
  measurable_toFun := measurable_dilateReg k
  measurable_invFun := measurable_dilateReg (-k)

private theorem measurableEmbedding_dilateReg (k : ℤ) :
    MeasurableEmbedding (dilateReg (d := d) k) :=
  (dilateRegEquiv (d := d) k).measurableEmbedding

/-- Change of variables for a pushforward along a triadic dilation.  No
measurability hypothesis on the integrand is needed: the dilation is a
measurable equivalence. -/
private theorem integral_map_dilateReg (k : ℤ)
    (mu : Measure (RegCoeffField d)) (F : RegCoeffField d → ℝ) :
    ∫ a, F a ∂(Measure.map (dilateReg k) mu) = ∫ a, F (dilateReg k a) ∂mu :=
  (measurableEmbedding_dilateReg k).integral_map F

variable [NeZero d]

/-! ## Pointwise transport of the starred carriers -/

/-- The starred fluctuation matrix on a cube, evaluated at a dilated
coefficient field, is the starred fluctuation matrix on the correspondingly
dilated cube evaluated at the original field.  The deterministic centering is
untouched. -/
theorem starredFluctuationMatrix_dilateReg_of_aelocallyUniformlyElliptic
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (B : FullBlockMat d) (C : BlockMat d) (Q : TriadicCube d) :
    starredFluctuationMatrix B C (cubeSet Q) (dilateReg k a) =
      starredFluctuationMatrix B C (cubeSet (Ch02.dilateCube (-k) Q)) a := by
  unfold starredFluctuationMatrix starredInverseCoarseBlockMatrix
  rw [coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic ha k Q]

/-- Squared operator norm form of
`starredFluctuationMatrix_dilateReg_of_aelocallyUniformlyElliptic`. -/
theorem starredFluctuationOperatorNormSq_dilateReg_of_aelocallyUniformlyElliptic
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (B : FullBlockMat d) (C : BlockMat d) (Q : TriadicCube d) :
    starredFluctuationOperatorNormSq B C (cubeSet Q) (dilateReg k a) =
      starredFluctuationOperatorNormSq B C (cubeSet (Ch02.dilateCube (-k) Q)) a := by
  unfold starredFluctuationOperatorNormSq
  rw [starredFluctuationMatrix_dilateReg_of_aelocallyUniformlyElliptic ha k B C Q]

/-! ## Integral transport to the genuine coefficient cutoff law -/

omit [NeZero d] in
/-- The relative law is a pushforward along a triadic dilation, so every
integral against it is an integral of the dilated integrand against the genuine
coefficient cutoff law. -/
private theorem integral_relativeNormalizedCutoffLaw_eq_integral_dilateReg
    (M : ABKModel d) (L : ℤ) (F : RegCoeffField d → ℝ) :
    ∫ a, F a ∂(Cutoff.relativeNormalizedCutoffLaw M L) =
      ∫ a, F (dilateReg
            (-(L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ))) a)
        ∂(Cutoff.coefficientCutoffLaw M L) := by
  rw [Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg]
  exact integral_map_dilateReg _ _ F

omit [NeZero d] in
private theorem dilateCube_originCube_sub (m s : ℤ) :
    Ch02.dilateCube s (originCube d (m - s)) = originCube d m := by
  simp [Ch02.dilateCube, originCube]

/-- Transport of the starred fluctuation integral itself from the
relative-normalized law to the genuine coefficient cutoff law. -/
theorem integral_starredFluctuationOperatorNormSq_relativeNormalizedCutoffLaw
    (M : ABKModel d) (L : ℤ) (B : FullBlockMat d) (C : BlockMat d)
    (Q : TriadicCube d) :
    ∫ a, starredFluctuationOperatorNormSq B C (cubeSet Q) a
        ∂(Cutoff.relativeNormalizedCutoffLaw M L) =
      ∫ a, starredFluctuationOperatorNormSq B C
            (cubeSet (Ch02.dilateCube
              (L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ)) Q)) a
        ∂(Cutoff.coefficientCutoffLaw M L) := by
  rw [integral_relativeNormalizedCutoffLaw_eq_integral_dilateReg]
  refine integral_congr_ae ?_
  filter_upwards
    [(Cutoff.coefficientCutoffLaw_lawCarrier M L).ae_locallyUniformlyEllipticField]
    with a ha
  rw [starredFluctuationOperatorNormSq_dilateReg_of_aelocallyUniformlyElliptic
      ha _ B C Q, neg_neg]

/-- The relative observation cube at relative scale `n - (L + c)` is the
physical observation cube at scale `n`: the starred fluctuation itself. -/
theorem integral_starredFluctuationOperatorNormSq_relativeNormalizedCutoffLaw_originCube
    (M : ABKModel d) (L n : ℤ) (B : FullBlockMat d) (C : BlockMat d) :
    ∫ a, starredFluctuationOperatorNormSq B C
          (cubeSet (originCube d
            (n - (L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ))))) a
        ∂(Cutoff.relativeNormalizedCutoffLaw M L) =
      ∫ a, starredFluctuationOperatorNormSq B C (cubeSet (originCube d n)) a
        ∂(Cutoff.coefficientCutoffLaw M L) := by
  rw [integral_starredFluctuationOperatorNormSq_relativeNormalizedCutoffLaw,
    dilateCube_originCube_sub]

/-- Scale correspondence of the deterministic centering.  The annealed block
matrix of the relative law at relative centering scale `n - L - c` is the
annealed block matrix of the genuine coefficient cutoff law at the physical
scale `n`; this identifies the centering carried through the transport
statements above. -/
theorem annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center
    (M : ABKModel d) (L n : ℤ) :
    Ch04.annealedBlockMatrixAtScale (Cutoff.relativeNormalizedCutoffLaw M L)
        (n - L - (Cutoff.cutoffRelativeNormalizationShift d : ℤ)) =
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n := by
  let k : ℤ := -(L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ))
  have hPk : Ch04.RestrictionLawCarrier
      (Measure.map (dilateReg k) (Cutoff.coefficientCutoffLaw M L)) := by
    simpa [k, Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg] using
      Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  have hmatrix := annealedBlockMatrix_map_dilateReg_cube
    (Cutoff.coefficientCutoffLaw_lawCarrier M L) k hPk
    (originCube d (n - L - (Cutoff.cutoffRelativeNormalizationShift d : ℤ)))
  have hcube :
      Ch02.dilateCube (-k)
          (originCube d (n - L - (Cutoff.cutoffRelativeNormalizationShift d : ℤ))) =
        originCube d n := by
    rw [show n - L - (Cutoff.cutoffRelativeNormalizationShift d : ℤ) =
      n - (L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ)) by ring]
    simpa [k] using
      dilateCube_originCube_sub (d := d) n
        (L + (Cutoff.cutoffRelativeNormalizationShift d : ℤ))
  rw [hcube] at hmatrix
  rw [Ch04.annealedBlockMatrixAtScale, Ch04.annealedBlockMatrixAtScale,
    Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg]
  exact hmatrix

/-- Consumer-facing reading of the deterministic centering carried by
`exists_coefficientCutoff_finiteCorridor_starredFluctuationVariance_bound`: it
is exactly the G coefficient cutoff law's annealed block matrix at the physical
scale `n`. -/
theorem scalarAnnealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center_eq
    (M : ABKModel d) (L n : ℤ) :
    Ch04.scalarAnnealedBlockMatrixAtScale
        (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L)
        (Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L)
        (n - L - (Cutoff.cutoffRelativeNormalizationShift d : ℤ)) =
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n := by
  rw [←
    annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
    (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L)
    (Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L)]
  exact annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center M L n

/-! ## The genuine-law finite-corridor variance bound -/

/-- Uniform quantitative literal two-plus-eight control of the starred fluctuation
itself, at the G coefficient cutoff law and the physical observation cube
`□_n`, along the whole integer corridor `L ≤ n ≤ m` above the cutoff.

This is the carrier-transported form of
`exists_relativeCutoff_finiteCorridor_fluctuationVariance_bound`
(`CombineFiniteVariance`): the constants, the premise set, the deterministic
centering and the decay `3^(-d(n-L))` are unchanged; only the law and the
observation cube are moved across the dilation
`Cutoff.relativeNormalizedCutoffLaw M L = Measure.map (dilateReg (-(L + c)))
(Cutoff.coefficientCutoffLaw M L)`.  The deterministic centering `Cn` is the
relative law's scalar annealed block matrix at relative scale `n - L - c`; by
`scalarAnnealedBlockMatrixAtScale_relativeNormalizedCutoffLaw_center_eq` this
is, for every integer `n`, the genuine cutoff law's annealed block matrix
`Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n` at the
physical scale `n`.  This is a local Provider theorem and makes no source-node
status claim. -/
theorem exists_coefficientCutoff_finiteCorridor_starredFluctuationVariance_bound
    (d : ℕ) :
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
              let hd : NeZero d :=
                ⟨Nat.ne_of_gt
                  (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
              let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
              let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
              let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
              let center : ℤ := n - L - c
              let B : FullBlockMat d := @Book.Ch02.constantFullBlockMatrix d
                (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))
              let Cn : BlockMat d :=
                @Book.Ch04.scalarAnnealedBlockMatrixAtScale d hd _ hP hStruct center
              let delta : ℝ :=
                (E : ℝ) ^ 2 * M.gamma +
                  Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))
              let decay : ℝ := Real.rpow 3
                (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))
              ∫ a, starredFluctuationOperatorNormSq B Cn
                    (cubeSet (originCube d n)) a
                    ∂(Cutoff.coefficientCutoffLaw M L) ≤
                Cvar * delta * (delta + decay) := by
  obtain ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, hbound⟩ :=
    exists_relativeCutoff_finiteCorridor_fluctuationVariance_bound d
  refine ⟨Chom, Cvar, hChom64, hChomShift, hCvarOne, ?_⟩
  intro M m E hLower epsilon hepsilon hgamma L hseparation n hn
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hcorridor :=
    hbound M m E hLower epsilon hepsilon hgamma L hseparation n hn
  have hepsilonPos : 0 < epsilon := hepsilon.1
  have hepsilonHalf : epsilon ≤ 1 / 2 := hepsilon.2
  have hChomPos : (0 : ℝ) < Chom := by linarith
  have hlogNonpos : Real.log epsilon ≤ 0 :=
    Real.log_nonpos hepsilonPos.le
      (hepsilonHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have habsLog : |Real.log epsilon| = -Real.log epsilon :=
    abs_of_nonpos hlogNonpos
  have hlogHalf : Real.log epsilon ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log hepsilonPos hepsilonHalf
  have hlogTwo : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have habsLogHalf : (1 / 2 : ℝ) ≤ |Real.log epsilon| := by
    rw [habsLog]
    rw [hlogTwo] at hlogHalf
    nlinarith [Real.log_two_gt_d9]
  have hLmOne : L ≤ m - 1 := by
    have hChomLog : (1 : ℝ) ≤ Chom * |Real.log epsilon| := by
      have hmul := mul_le_mul hChom64 habsLogHalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by linarith : (0 : ℝ) ≤ Chom)
      nlinarith
    have hLplusOneReal : (L : ℝ) + 1 ≤ (m : ℝ) := by linarith
    have hLplusOne : L + 1 ≤ m := by exact_mod_cast hLplusOneReal
    omega
  have hEpos : (0 : ℝ) < (E : ℝ) := zero_lt_one.trans_le E.property
  have hChomInv : Chom⁻¹ ≤ (64 : ℝ)⁻¹ :=
    (inv_le_inv₀ hChomPos (by norm_num : (0 : ℝ) < 64)).2 hChom64
  have hEinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have hEinv : (E : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hEpos).2 E.property
    have hEinvNonneg : 0 ≤ (E : ℝ)⁻¹ := inv_nonneg.mpr hEpos.le
    nlinarith [sq_nonneg ((E : ℝ)⁻¹ - 1)]
  have hgamma128 : M.gamma ≤ 1 / 128 := by
    have hCinvNonneg : (0 : ℝ) ≤ Chom⁻¹ := inv_nonneg.mpr hChomPos.le
    have hstep1 : Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 ≤ (64 : ℝ)⁻¹ := by
      calc
        Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 ≤ Chom⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hEinvSq hCinvNonneg
        _ = Chom⁻¹ := mul_one _
        _ ≤ (64 : ℝ)⁻¹ := hChomInv
    have hstep2 : Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ≤ (64 : ℝ)⁻¹ * (1 / 2) := by
      calc
        Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ≤ (64 : ℝ)⁻¹ * epsilon :=
          mul_le_mul_of_nonneg_right hstep1 hepsilonPos.le
        _ ≤ (64 : ℝ)⁻¹ * (1 / 2) :=
          mul_le_mul_of_nonneg_left hepsilonHalf (by norm_num)
    have hfinal : M.gamma ≤ (64 : ℝ)⁻¹ * (1 / 2) := hgamma.trans hstep2
    norm_num at hfinal
    linarith
  have hwindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 := by
    constructor
    · linarith
    · norm_num
  have hLowerL : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2) (IndependentSums.gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨1 / 16, by norm_num⟩)
      ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma)
      (((1 / 16 : ℝ)⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) :=
    hLower L hLmOne (1 / 16) hwindow
  have hLn : L ≤ n := hn.1
  have hdescInt :=
    (two_mul_integral_relativeStarredDescendantOperatorNormSq_le
      M L n hLn (s := (1 / 16 : ℝ)) (by norm_num) hLowerL).1
  have htraceInt :=
    (eight_mul_integral_relativeStarredBlockJTraceAverageSq_le
      M L n hLn hLowerL).1
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let center : ℤ := n - L - c
  let Q : TriadicCube d := originCube d (n - (L + c))
  let j : ℕ := (n - L).toNat
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))
  let Cn : BlockMat d :=
    Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  have hB : B.PosDef :=
    Book.Ch02.constantFullBlockMatrix_posDef_of_isEllipticMatrix
      (by
        simpa only [Observable.isotropicComparatorMatrix] using
          isEllipticMatrix_scalarMatrix (Annealed.sigmaBar M L).property)
  have hdesc : Integrable
      (starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j) P := by
    simpa only [c, P, hP, hStruct, center, Q, j, B, Cn, sub_sub] using hdescInt
  have hJ : Integrable (starredBlockJTraceAverageSq B Q j) P := by
    simpa only [c, P, Q, j, B] using htraceInt
  have hbridge :=
    integral_starredFluctuationNormSq_le_descendantAndResponseBounds
      hP hStruct center B hB Q j hdesc hJ
  have htransport :=
    integral_starredFluctuationOperatorNormSq_relativeNormalizedCutoffLaw_originCube
      M L n B Cn
  calc
    ∫ a, starredFluctuationOperatorNormSq B Cn (cubeSet (originCube d n)) a
        ∂(Cutoff.coefficientCutoffLaw M L) =
        ∫ a, starredFluctuationOperatorNormSq B Cn (cubeSet Q) a ∂P :=
      htransport.symm
    _ ≤ 2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j a ∂P +
          8 * ∫ a, starredBlockJTraceAverageSq B Q j a ∂P := hbridge
    _ ≤ Cvar *
          ((E : ℝ) ^ 2 * M.gamma +
            Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) *
          (((E : ℝ) ^ 2 * M.gamma +
              Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) +
            Real.rpow 3 (-(d : ℝ) * (((n - L).toNat : ℕ) : ℝ))) := hcorridor

end

end Algsuperdiff.Section3.Provider.Homogenization

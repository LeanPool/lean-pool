/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RelativeNormalizedP4
public import LeanPool.Superdiffusion.Support.Book.Ch04.Theorems.DilationResponse

/-!
# RelativeLimitLoadBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Limiting scalar for the same-cutoff relative normalization

The relative normalization is an arbitrary integer triadic dilation of the
genuine cutoff law.  This file transports the deterministic coarse block
matrix through that dilation, lifts the identity to annealed block matrices,
and identifies the relative law's limiting scalar with the already
characterized source-facing `sigmaBar`.

The proof keeps the cutoff index fixed.  It uses only a finite shift of the
natural-scale limit and does not assume covariance between cutoff indices.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The deterministic coarse block matrix shifts on an arbitrary triadic cube
under an arbitrary integer dilation of the coefficient field. -/
theorem coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (Q : TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) (dilateReg k a).toFun =
      coarseBlockMatrix (cubeSet (Ch02.dilateCube (-k) Q)) a.toFun := by
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let hk := Cutoff.aelocallyUniformlyEllipticField_dilateReg ha k
  let G : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (dilateReg k a) hk
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate k F
  let Qsrc : TriadicCube d := Ch02.dilateCube (-k) Q
  have htarget : Ch02.dilateCube k Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_dilateCube_neg k Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F, hk] using Cutoff.triadicCoeffFamily_dilateReg_aeeq_dilate ha k
  have hAEEq := Ch02.coarseBlockMatrix_eq_ofAEEq (hGB Q)
  have hdilate :=
    Ch02.coarseBlockMatrix_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate k F Qsrc)
  have hdilate' :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := by
    rw [htarget] at hdilate
    simpa [B] using hdilate
  calc
    coarseBlockMatrix (cubeSet Q) (dilateReg k a).toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (G.coeffOn Q) := by
      simpa [G] using
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
          hk Q
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) := hAEEq
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := hdilate'
    _ = coarseBlockMatrix (cubeSet Qsrc) a.toFun :=
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
        ha Qsrc).symm

/-- Annealed coarse block matrices shift under an arbitrary integer dilation
pushforward. -/
theorem annealedBlockMatrix_map_dilateReg_cube
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (k : ℤ)
    (hPk : Ch04.RestrictionLawCarrier (Measure.map (dilateReg k) P))
    (Q : TriadicCube d) :
    Ch04.annealedBlockMatrix (Measure.map (dilateReg k) P) (cubeSet Q) =
      Ch04.annealedBlockMatrix P
        (cubeSet (Ch02.dilateCube (-k) Q)) := by
  unfold Ch04.annealedBlockMatrix
  refine Eq.mpr (BlockMat.mk.injEq _ _ _ _ _ _ _ _) ?_
  constructor
  · ext i j
    rw [MeasureTheory.integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.upperLeft i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
          ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
        Q i j).aestronglyMeasurable
  constructor
  · ext i j
    rw [MeasureTheory.integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.upperRight i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
          ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
        Q i j).aestronglyMeasurable
  constructor
  · ext i j
    rw [MeasureTheory.integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.lowerLeft i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
          ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
        Q i j).aestronglyMeasurable
  · ext i j
    rw [MeasureTheory.integral_map (measurable_dilateReg (d := d) k).aemeasurable]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      exact congrArg (fun A : BlockMat d => A.lowerRight i j)
        (coarseBlockMatrix_cubeSet_dilateReg_of_aelocallyUniformlyElliptic
          ha k Q)
    · exact (hPk.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
        Q i j).aestronglyMeasurable

/-- The relative law's annealed matrix at natural scale `r` is the genuine
same-index cutoff law's matrix at physical integer scale `cutoff + c + r`. -/
theorem annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw
    (M : ABKModel d) (cutoff : ℤ) (r : ℕ) :
    Ch04.annealedBlockMatrixAtScale
        (Cutoff.relativeNormalizedCutoffLaw M cutoff) (r : ℤ) =
      Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M cutoff)
        (cutoff + (Cutoff.cutoffRelativeNormalizationShift d : ℤ) + (r : ℤ)) := by
  let k : ℤ := -(cutoff + (Cutoff.cutoffRelativeNormalizationShift d : ℤ))
  let hPk : Ch04.RestrictionLawCarrier
      (Measure.map (dilateReg k) (Cutoff.coefficientCutoffLaw M cutoff)) := by
    simpa [k, Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg] using
      Cutoff.relativeNormalizedCutoffLaw_lawCarrier M cutoff
  have hmatrix := annealedBlockMatrix_map_dilateReg_cube
    (Cutoff.coefficientCutoffLaw_lawCarrier M cutoff) k hPk
    (originCube d (r : ℤ))
  simpa [Ch04.annealedBlockMatrixAtScale, k, Ch02.dilateCube, originCube,
    add_assoc, add_comm, add_left_comm,
    Cutoff.relativeNormalizedCutoffLaw_eq_map_dilateReg] using hmatrix

/-- A natural-scale limit is unchanged after any fixed integer shift of the
scale argument. -/
private theorem tendsto_natCast_add_int_shift
    {α : Type*} [TopologicalSpace α] (f : ℤ → α) (s : ℤ) {x : α}
    (h : Tendsto (fun n : ℕ => f (n : ℤ)) atTop (nhds x)) :
    Tendsto (fun n : ℕ => f (s + (n : ℤ))) atTop (nhds x) := by
  by_cases hs : 0 ≤ s
  · let k : ℕ := s.toNat
    have hs_eq : s = (k : ℤ) := by
      simpa [k] using (Int.toNat_of_nonneg hs).symm
    have htail := h.comp (tendsto_add_atTop_nat k)
    simpa [hs_eq, add_comm] using! htail
  · let k : ℕ := (-s).toNat
    have hneg : 0 ≤ -s := by omega
    have hs_eq : s = -(k : ℤ) := by
      have hk : ((k : ℕ) : ℤ) = -s := by
        simpa [k] using Int.toNat_of_nonneg hneg
      omega
    have htail := h.comp (tendsto_sub_atTop_nat k)
    refine htail.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    change f (((n - k : ℕ) : ℤ)) = f (s + (n : ℤ))
    apply congrArg f
    rw [hs_eq]
    omega

/-- The limiting scalar of the same-cutoff relative law is exactly the
source-facing running diffusivity. -/
theorem relativeNormalizedCutoff_barSigmaLimit_eq_sigmaBar
    (M : ABKModel d) (cutoff : ℤ) :
    Ch05.Section57.barSigmaLimit
        (Cutoff.relativeNormalizedCutoffLaw_lawCarrier M cutoff)
        (Cutoff.relativeNormalizedCutoffLaw_structuralLaw M cutoff) =
      (Annealed.sigmaBar M cutoff : ℝ) := by
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M cutoff
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M cutoff
  let hP4 :=
    Cutoff.relativeNormalizedCutoffLaw_quantitativeCoarseGrainedEllipticity
      M cutoff
  let L : ℝ := Ch05.Section57.barSigmaLimit hP hStruct
  let s : ℤ := cutoff + (Cutoff.cutoffRelativeNormalizationShift d : ℤ)
  have hrelative :=
    Annealed.annealedFullBlockMatrixAtScale_tendsto_barSigmaLimit_of_P4
      hP hStruct hP4
  have hshifted :
      Tendsto
        (fun n : ℕ =>
          toFullBlockMat
            (Ch04.annealedBlockMatrixAtScale
              (Cutoff.coefficientCutoffLaw M cutoff) (s + (n : ℤ))))
        atTop
        (nhds (toFullBlockMat (Ch02.blockDiag
          (L • (1 : Mat d)) (L⁻¹ • (1 : Mat d))))) := by
    refine hrelative.congr' (Eventually.of_forall fun n => ?_)
    rw [annealedBlockMatrixAtScale_relativeNormalizedCutoffLaw]
  have hsigma := tendsto_natCast_add_int_shift
    (fun m : ℤ =>
      toFullBlockMat
        (Ch04.annealedBlockMatrixAtScale
          (Cutoff.coefficientCutoffLaw M cutoff) m))
    s (Annealed.sigmaBar_characterization M cutoff).2.1
  have hlimit := tendsto_nhds_unique hshifted hsigma
  have hentry := congrArg
    (fun A : FullBlockMat d =>
      A (Sum.inl (0 : Fin d)) (Sum.inl (0 : Fin d))) hlimit
  simpa [L, toFullBlockMat, Ch02.blockDiag, Pi.smul_apply] using hentry

end

end Algsuperdiff.Section3.Provider.Homogenization

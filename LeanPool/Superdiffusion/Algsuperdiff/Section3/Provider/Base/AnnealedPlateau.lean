/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CGBoundSpecialization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.CubeScalar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization

/-!
# AnnealedPlateau

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# ABK26's `e.plateau.region.bound`

ABK26, takes the expectation of `e.basecase.tightbound` and uses
`e.annealed.khom.zero` and `e.km.L2.expectation` to obtain

`nu Id <= shom_{m,*}(cu_l) <= shom_m <= shom_m(cu_l)
   <= nu (1 + (1/2) nu^{-2} c* gamma^{-1} (1 + 4 gamma) 3^{2 gamma m}) Id`,

which is `e.basecase.shom.m`.

The local conclusion is the scalar pair carried by the frozen base-case
statement,

`nu <= sigmaBar_m <= nu (1 + c+ (2 nu^2)^{-1} gamma^{-1} (1 + 4 gamma) 3^{2 gamma m})`.

## Route

* Every annealed cutoff block on an origin cube is a scalar matrix
  (`Provider.Annealed.coefficientCutoffLaw_isScalarMatrix_annealedBAtScale`),
  and the annealed coupling matrix vanishes
  (`Provider.Annealed.coefficientCutoffLaw_annealedKappa_eq_zero`), so
  `shom_m(cu_n) = bhom_m(cu_n)` is a scalar.
* The finite-volume annealed block `bhom_m(cu_n)` is the expectation of the
  deterministic `b_m(cu_n)`, so the deterministic chain integrates: the lower
  leg gives `nu` and the upper leg gives `nu + nu^{-1}
  E[||k_m||^2_{L2bar(cu_n)}]`, with the expectation supplied *exactly* by
  `Provider.Stream.integral_average_frobeniusMass_cutoff`.
* The resulting two-sided bound is **uniform in the cube scale `n`**, which is
  what the source's monotone sandwich delivers.  Passing to the limit in the
  unique-choice characterization `Annealed.sigmaBar_characterization` therefore
  gives the same bounds for `sigmaBar_m`; no separate Loewner monotonicity input
  is needed.
* The arithmetic step is `e.K.cgamma.ineq`: `K_gamma <= gamma^{-1} + 4
  = gamma^{-1} (1 + 4 gamma)`.

## Main results

* `integrable_average_frobeniusMass_cutoff`
* `coarseBlockMatrix_upperLeft_coefficientCutoff`
* `annealedBAtScale_entry_bounds`
* `annealedPlateau`: the display `e.basecase.shom.m`.

## References

* ABK26, `e.plateau.region.bound`, `e.basecase.shom.m`.
* ABK26, `e.km.L2.expectation`.
* ABK26, `e.K.cgamma.ineq`.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory Filter
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Integrability of the per-cube stream mass -/

private theorem measurable_uncurry_swap (m : ℤ) : Measurable (Function.uncurry
    (fun (omega : CutoffSample d) (x : Vec d) =>
      Ch02.matrixFrobeniusNormSq (cutoff m omega x))) := by
  have hcomp : (Function.uncurry
      (fun (omega : CutoffSample d) (x : Vec d) =>
        Ch02.matrixFrobeniusNormSq (cutoff m omega x)))
      = (Function.uncurry
          (fun (x : Vec d) (omega : CutoffSample d) =>
            Ch02.matrixFrobeniusNormSq (cutoff m omega x))) ∘ Prod.swap := by
    funext p
    obtain ⟨omega, x⟩ := p
    rfl
  rw [hcomp]
  exact (Stream.measurable_uncurry_frobeniusMass_cutoff m).comp measurable_swap

private theorem stronglyMeasurable_setIntegral_frobeniusMass (l m : ℤ) :
    StronglyMeasurable (fun omega : CutoffSample d =>
      ∫ x in openCubeSet (originCube d l),
        Ch02.matrixFrobeniusNormSq (cutoff m omega x) ∂volume) :=
  (measurable_uncurry_swap (d := d) m).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (openCubeSet (originCube d l)))

/-- The per-cube volume-normalized `L^2` mass of `k_m` is integrable in the
cutoff sample: it is jointly measurable and dominated on `cu_l` by the square of
the corresponding local control, whose second moment is finite. -/
theorem integrable_average_frobeniusMass_cutoff (M : ABKModel d) (l m : ℤ) :
    Integrable
      (fun omega : CutoffSample d =>
        Ch02.average (Ch02.cubeDomain (originCube d l))
          (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))
      (cutoffSampleLaw M).toMeasure := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d l))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet
        (originCube d l)).isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet (openCubeSet (originCube d l)) :=
    measurableSet_openCubeSet _
  have hvol : (volume (openCubeSet (originCube d l))).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos _).ne'
  have hmeas : AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d l),
            Ch02.matrixFrobeniusNormSq (cutoff m omega x) ∂volume)
      (cutoffSampleLaw M).toMeasure :=
    ((stronglyMeasurable_setIntegral_frobeniusMass l m).const_mul _).aestronglyMeasurable
  refine Integrable.mono'
    ((integrable_cutoffLocalControl_pow M l m 2).const_mul ((d : ℝ) ^ 2)) hmeas ?_
  filter_upwards with omega
  have hnonneg : 0 ≤ volumeAverage (openCubeSet (originCube d l))
      (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) :=
    volumeAverage_nonneg_of_nonneg_on hUmeas fun x _ =>
      Ch02.matrixFrobeniusNormSq_nonneg _
  have hle : volumeAverage (openCubeSet (originCube d l))
      (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) ≤
      (d : ℝ) ^ 2 * cutoffLocalControl l m omega ^ 2 :=
    volumeAverage_le_of_le_on hUmeas (integrableOn_frobeniusMass_cutoff l m omega) hvol
      fun x hx => Stream.matrixFrobeniusNormSq_le_of_abs_entry_le fun i j =>
        abs_cutoff_entry_le_cutoffLocalControl l m omega hx i j
  show ‖volumeAverage (openCubeSet (originCube d l))
      (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x))‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

/-! ## The deterministic upper-left block -/

/-- The upper-left coarse block of the cutoff coefficient on an origin cube is
the Chapter 2 derived matrix `b_m(cu_n)`. -/
theorem coarseBlockMatrix_upperLeft_coefficientCutoff [NeZero d] (M : ABKModel d)
    (m n : ℤ) (omega : CutoffSample d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (coefficientCutoff M.nu m omega).toFun).upperLeft =
      Ch02.bCoarse (Ch02.cubeDomain (originCube d n))
        (coefficientCutoffCoeffOn M m omega (originCube d n)) := by
  have haeeq : Ch02.CoeffOn.AEEq
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff M.nu m omega)
          (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)).coeffOn
        (originCube d n))
      (coefficientCutoffCoeffOn M m omega (originCube d n)) := Filter.EventuallyEq.rfl
  rw [Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) (originCube d n),
    Ch02.coarseBlockMatrix_eq_ofAEEq haeeq]
  rfl

/-! ## The annealed upper-left block -/

private theorem blockVecDot_pair_zero (A : BlockMat d) (xi : Vec d) :
    blockVecDot (xi, (0 : Vec d)) (blockMatVecMul A (xi, (0 : Vec d))) =
      vecDot xi (matVecMul A.upperLeft xi) := by
  simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]

private theorem vecNormSq_single_one [NeZero d] :
    vecNormSq (Pi.single (0 : Fin d) (1 : ℝ)) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply]

private theorem integrable_upperLeft_quadratic [NeZero d] (M : ABKModel d) (m n : ℤ)
    (xi : Vec d) :
    Integrable (fun a : RegCoeffField d =>
      vecDot xi (matVecMul
        (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft xi))
      (coefficientCutoffLaw M m) := by
  refine (Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
    (fun alpha beta =>
      Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
        M m (originCube d n) alpha beta)
    (xi, (0 : Vec d)) (xi, (0 : Vec d))).congr ?_
  filter_upwards with a
  exact blockVecDot_pair_zero _ xi

private theorem vecDot_matVecMul_annealedBAtScale [NeZero d] (M : ABKModel d) (m n : ℤ)
    (xi : Vec d) :
    vecDot xi (matVecMul (Ch04.annealedBAtScale (coefficientCutoffLaw M m) n) xi) =
      ∫ a, vecDot xi (matVecMul
        (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft xi)
        ∂(coefficientCutoffLaw M m) := by
  have h := Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
    (fun alpha beta =>
      Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
        M m (originCube d n) alpha beta)
    (xi, (0 : Vec d)) (xi, (0 : Vec d))
  calc vecDot xi (matVecMul (Ch04.annealedBAtScale (coefficientCutoffLaw M m) n) xi)
      = blockVecDot (xi, (0 : Vec d))
          (blockMatVecMul (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M m) n)
            (xi, (0 : Vec d))) := (blockVecDot_pair_zero _ xi).symm
    _ = ∫ a, blockVecDot (xi, (0 : Vec d))
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun)
            (xi, (0 : Vec d))) ∂(coefficientCutoffLaw M m) := h.symm
    _ = ∫ a, vecDot xi (matVecMul
          (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft xi)
          ∂(coefficientCutoffLaw M m) :=
        integral_congr_ae (Filter.Eventually.of_forall fun a =>
          blockVecDot_pair_zero _ xi)

private theorem integrable_bCoarse_quadratic [NeZero d] (M : ABKModel d) (m n : ℤ)
    (xi : Vec d) :
    Integrable (fun omega : CutoffSample d =>
      vecDot xi (matVecMul (Ch02.bCoarse (Ch02.cubeDomain (originCube d n))
        (coefficientCutoffCoeffOn M m omega (originCube d n))) xi))
      (cutoffSampleLaw M).toMeasure := by
  have hq := integrable_upperLeft_quadratic M m n xi
  rw [coefficientCutoffLaw_eq_map] at hq
  refine ((integrable_map_measure hq.aestronglyMeasurable
    (measurable_coefficientCutoff M.nu m).aemeasurable).mp hq).congr ?_
  filter_upwards with omega
  exact congrArg (fun A : Mat d => vecDot xi (matVecMul A xi))
    (coarseBlockMatrix_upperLeft_coefficientCutoff M m n omega)

private theorem vecDot_matVecMul_annealedBAtScale_sample [NeZero d] (M : ABKModel d)
    (m n : ℤ) (xi : Vec d) :
    vecDot xi (matVecMul (Ch04.annealedBAtScale (coefficientCutoffLaw M m) n) xi) =
      ∫ omega : CutoffSample d,
        vecDot xi (matVecMul (Ch02.bCoarse (Ch02.cubeDomain (originCube d n))
          (coefficientCutoffCoeffOn M m omega (originCube d n))) xi)
        ∂(cutoffSampleLaw M).toMeasure := by
  have hq := integrable_upperLeft_quadratic M m n xi
  rw [vecDot_matVecMul_annealedBAtScale, coefficientCutoffLaw_eq_map] at *
  rw [integral_map (measurable_coefficientCutoff M.nu m).aemeasurable
    hq.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  exact congrArg (fun A : Mat d => vecDot xi (matVecMul A xi))
    (coarseBlockMatrix_upperLeft_coefficientCutoff M m n omega)

/-! ## The finite-volume annealed bounds -/

/-- **ABK26.**  The expectation of the specialized deterministic chain,
with the exact per-cube stream mass of `e.km.L2.expectation` inserted.  The
bounds do not depend on the cube scale `n`. -/
private theorem annealedBAtScale_quadratic_bounds [NeZero d] (M : ABKModel d) (m n : ℤ)
    (xi : Vec d) :
    M.nu * vecNormSq xi ≤
        vecDot xi (matVecMul (Ch04.annealedBAtScale (coefficientCutoffLaw M m) n) xi) ∧
      vecDot xi (matVecMul (Ch04.annealedBAtScale (coefficientCutoffLaw M m) n) xi) ≤
        M.nu * vecNormSq xi + M.nu⁻¹ * vecNormSq xi *
          (Disorder.cstarPlus M * Stream.Kgamma M.gamma / 2 *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  have hnu : M.nu ≠ 0 := M.nu_pos.ne'
  rw [vecDot_matVecMul_annealedBAtScale_sample]
  constructor
  · have hconst : (∫ _omega : CutoffSample d, M.nu * vecNormSq xi
        ∂(cutoffSampleLaw M).toMeasure) = M.nu * vecNormSq xi := by simp
    rw [← hconst]
    refine integral_mono (integrable_const _) (integrable_bCoarse_quadratic M m n xi)
      fun omega => ?_
    have hb := matLoewnerLE_nu_smul_one_bCoarse_coefficientCutoff M m omega
      (originCube d n) xi
    rw [vecDot_matVecMul_smul_one] at hb
    linarith
  · calc
      (∫ omega : CutoffSample d,
          vecDot xi (matVecMul (Ch02.bCoarse (Ch02.cubeDomain (originCube d n))
            (coefficientCutoffCoeffOn M m omega (originCube d n))) xi)
          ∂(cutoffSampleLaw M).toMeasure)
          ≤ ∫ omega : CutoffSample d, (M.nu * vecNormSq xi +
              M.nu⁻¹ * vecNormSq xi *
                Ch02.average (Ch02.cubeDomain (originCube d n))
                  (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))
              ∂(cutoffSampleLaw M).toMeasure := by
        refine integral_mono (integrable_bCoarse_quadratic M m n xi)
          ((integrable_const _).add
            ((integrable_average_frobeniusMass_cutoff M n m).const_mul
              (M.nu⁻¹ * vecNormSq xi))) fun omega => ?_
        have hb := matLoewnerLE_bCoarse_coefficientCutoff M n m omega xi
        rw [vecDot_matVecMul_smul_one] at hb
        have harith : M.nu * (1 + (M.nu ^ 2)⁻¹ *
            Ch02.average (Ch02.cubeDomain (originCube d n))
              (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x))) * vecNormSq xi =
          M.nu * vecNormSq xi + M.nu⁻¹ * vecNormSq xi *
            Ch02.average (Ch02.cubeDomain (originCube d n))
              (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) := by
          field_simp
        linarith
      _ = M.nu * vecNormSq xi + M.nu⁻¹ * vecNormSq xi *
            (Disorder.cstarPlus M * Stream.Kgamma M.gamma / 2 *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
        rw [integral_add (integrable_const _)
          ((integrable_average_frobeniusMass_cutoff M n m).const_mul
            (M.nu⁻¹ * vecNormSq xi)),
          integral_const_mul (M.nu⁻¹ * vecNormSq xi),
          Stream.integral_average_frobeniusMass_cutoff]
        simp

/-! ## The plateau arithmetic -/

/-- `e.K.cgamma.ineq` in the shape used by the plateau display:
`K_gamma <= gamma^{-1} + 4 = gamma^{-1} (1 + 4 gamma)`. -/
private theorem plateau_arith (M : ABKModel d) (m : ℤ) {s : ℝ} (hs : 0 ≤ s) :
    M.nu * s + M.nu⁻¹ * s *
        (Disorder.cstarPlus M * Stream.Kgamma M.gamma / 2 *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ≤
      M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
        (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) * s := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hnu' : M.nu ≠ 0 := hnu.ne'
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hg' : M.gamma ≠ 0 := hg.ne'
  have hc : (0 : ℝ) ≤ Disorder.cstarPlus M := Disorder.cstarPlus_nonneg M
  have hT : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hK : Stream.Kgamma M.gamma ≤ M.gamma⁻¹ + 4 := Stream.Kgamma_le hg
  have hKle : Disorder.cstarPlus M * Stream.Kgamma M.gamma / 2 *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
      Disorder.cstarPlus M * (M.gamma⁻¹ + 4) / 2 *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have h1 : Disorder.cstarPlus M * Stream.Kgamma M.gamma ≤
        Disorder.cstarPlus M * (M.gamma⁻¹ + 4) := mul_le_mul_of_nonneg_left hK hc
    nlinarith [hT.le]
  have hnn : (0 : ℝ) ≤ M.nu⁻¹ * s := mul_nonneg (inv_pos.mpr hnu).le hs
  have hstep := mul_le_mul_of_nonneg_left hKle hnn
  have heq : M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
      (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) * s =
      M.nu * s + M.nu⁻¹ * s * (Disorder.cstarPlus M * (M.gamma⁻¹ + 4) / 2 *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
    field_simp
  linarith

/-! ## The scalar finite-volume bounds and the infinite-volume limit -/

/-- **ABK26.**  The finite-volume annealed diffusivity of the cutoff at every
origin-cube scale `n` obeys the plateau bounds, uniformly in `n`. -/
theorem annealedBAtScale_entry_bounds [NeZero d] (M : ABKModel d) (m n : ℤ) :
    M.nu ≤ Ch04.annealedBAtScale (coefficientCutoffLaw M m) n 0 0 ∧
      Ch04.annealedBAtScale (coefficientCutoffLaw M m) n 0 0 ≤
        M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  obtain ⟨c, hc⟩ :=
    Provider.Annealed.coefficientCutoffLaw_isScalarMatrix_annealedBAtScale M m n
  have hentry : Ch04.annealedBAtScale (coefficientCutoffLaw M m) n 0 0 = c := by
    rw [hc]
    simp [Matrix.smul_apply]
  obtain ⟨hlow, hup⟩ :=
    annealedBAtScale_quadratic_bounds M m n (Pi.single (0 : Fin d) (1 : ℝ))
  rw [hc, vecDot_matVecMul_smul_one, vecNormSq_single_one] at hlow hup
  have harith := plateau_arith M m (s := (1 : ℝ)) zero_le_one
  rw [hentry]
  exact ⟨by linarith, by linarith⟩

/-- **ABK26, `e.plateau.region.bound`, `e.basecase.shom.m`.**

For every `m` in `Z`,

`nu <= sigmaBar_m <= nu (1 + c+ (2 nu^2)^{-1} gamma^{-1} (1 + 4 gamma)
3^{2 gamma m})`,

where `sigmaBar_m` is the infinite-volume annealed running diffusivity of the
coefficient cutoff and `c+` is the canonical Frobenius shell constant of
`e.km.L2.expectation`. -/
theorem annealedPlateau (M : ABKModel d) (m : ℤ) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M m : ℝ) ≤
        M.nu * (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  obtain ⟨-, hlim, -⟩ := Annealed.sigmaBar_characterization M m
  have hentry : Tendsto
      (fun n : ℕ => Ch04.annealedBAtScale (coefficientCutoffLaw M m) (n : ℤ) 0 0)
      atTop (nhds ((Annealed.sigmaBar M m : ℝ))) := by
    have h1 := (tendsto_pi_nhds.mp hlim) (Sum.inl (0 : Fin d))
    have h2 := (tendsto_pi_nhds.mp h1) (Sum.inl (0 : Fin d))
    simpa [toFullBlockMat, Ch02.blockDiag, Matrix.one_apply] using! h2
  exact ⟨ge_of_tendsto hentry (Filter.Eventually.of_forall fun n =>
      (annealedBAtScale_entry_bounds M m (n : ℤ)).1),
    le_of_tendsto hentry (Filter.Eventually.of_forall fun n =>
      (annealedBAtScale_entry_bounds M m (n : ℤ)).2)⟩

end

end Algsuperdiff.Section3.Provider.Base

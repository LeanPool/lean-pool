/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffL2Expectation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities

/-!
# CGBoundSpecialization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# ABK26's `e.basecase.tightbound`

ABK26, specializes the deterministic coarse-graining ellipticity chain
`e.CG.bounds.1` to the infrared cutoff coefficient `a_m = nu I + k_m`:

`nu Id <= s_{m,*}(cu_l) <= s_m(cu_l) <= b_m(cu_l)
     <= nu (1 + nu^{-2} ||k_m||^2_{L2bar(cu_l)}) Id`,

for every `m, l` in `Z` and every sample.

The specialization is exact, not an estimate.  The symmetric part of the cutoff
coefficient is *identically* `nu I`
(`Algsuperdiff.Section3.Cutoff.symmPart_coefficientCutoff`), so the harmonic
mean on the left of `e.CG.bounds.1` is `nu Id`, and the averaged correction on
the right is `nu Id + nu^{-1} (fint_{cu_l} k_m^t k_m) `.  Only the last step,
`k^t k <= ||k||_F^2 Id`, is an inequality.

The Loewner order is CoarseGraining's `Homogenization.MatLoewnerLE`, the coarse
matrices are CoarseGraining's Chapter 2 objects on the Chapter 2 cube domain,
and the volume normalized `L^2` mass of `k_m` is `Ch02.average (Ch02.cubeDomain
(originCube d l)) (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x))`,
the same expression whose expectation is computed by
`Algsuperdiff.Section3.Provider.Stream.integral_average_frobeniusMass_cutoff`.

## Main results

* `skewPart_coefficientCutoff`, `inv_symmPart_coefficientCutoff`
* `averagedSymmPartInv_coefficientCutoff`,
  `averagedSymmPartPlusCorrection_coefficientCutoff`
* `matLoewnerLE_nu_smul_one_sigmaStarCoarse_coefficientCutoff`
* `matLoewnerLE_bCoarse_coefficientCutoff`
* `matLoewnerLE_nu_smul_one_bCoarse_coefficientCutoff`: the composed lower leg
  of `e.basecase.tightbound`, placing `nu Id` below `b_m(cu_l)`.

## References

* ABK26, `e.basecase.tightbound`.
* ABK26, `e.CG.bounds.1`.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Pointwise algebra of the cutoff coefficient -/

/-- The matrix inverse of a nonzero scalar multiple of the identity. -/
private theorem inv_smul_one {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Mat d))⁻¹ = c⁻¹ • (1 : Mat d) := by
  rw [nonsing_inv_smul c hc (by simp)]
  simp

/-- Multiplication by the identity matrix on vectors. -/
private theorem matVecMul_one_vec (xi : Vec d) : matVecMul (1 : Mat d) xi = xi := by
  funext k
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- Transitivity of the Loewner order. -/
private theorem matLoewnerLE_trans {A B C : Mat d} (hAB : MatLoewnerLE A B)
    (hBC : MatLoewnerLE B C) : MatLoewnerLE A C :=
  fun x => (hAB x).trans (hBC x)

/-- The quadratic form of a scalar matrix. -/
theorem vecDot_matVecMul_smul_one (c : ℝ) (xi : Vec d) :
    vecDot xi (matVecMul (c • (1 : Mat d)) xi) = c * vecNormSq xi := by
  rw [smul_matVecMul, vecDot_smul_right, matVecMul_one_vec]
  rfl

/-- **The skew part of the cutoff coefficient is the stream matrix `k_m`.**
This is a pointwise identity: `a_m = nu I + k_m` with `k_m` antisymmetric. -/
theorem skewPart_coefficientCutoff (nu : ℝ) (m : ℤ) (omega : CutoffSample d)
    (x : Vec d) :
    skewPart (coefficientCutoff nu m omega x) = cutoff m omega x := by
  have hskew := cutoff_skew m omega x
  ext i j
  have hskew_entry : cutoff m omega x j i = -cutoff m omega x i j := by
    have := congrFun (congrFun hskew i) j
    simpa using this
  simp only [skewPart, coefficientCutoff_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [hskew_entry]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply, ite_eq_left]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [Matrix.one_apply, ite_eq_right hij, ite_eq_right hji]
    ring

/-- The pointwise inverse symmetric part of the cutoff coefficient is
`nu^{-1} I`, exactly. -/
theorem inv_symmPart_coefficientCutoff (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (x : Vec d) :
    (symmPart (coefficientCutoff M.nu m omega x))⁻¹ = M.nu⁻¹ • (1 : Mat d) := by
  rw [symmPart_coefficientCutoff, inv_smul_one M.nu_pos.ne']

/-- The pointwise integrand of the right-hand side of `e.CG.bounds.1`, for the cutoff
coefficient: `symm + skew^t symm^{-1} skew = nu I + nu^{-1} k_m^t k_m`. -/
theorem symmPartPlusCorrection_coefficientCutoff (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (x : Vec d) :
    symmPart (coefficientCutoff M.nu m omega x) +
        matTranspose (skewPart (coefficientCutoff M.nu m omega x)) *
          (symmPart (coefficientCutoff M.nu m omega x))⁻¹ *
            skewPart (coefficientCutoff M.nu m omega x) =
      M.nu • (1 : Mat d) +
        M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x) := by
  rw [inv_symmPart_coefficientCutoff, symmPart_coefficientCutoff,
    skewPart_coefficientCutoff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The quadratic form of the pointwise correction matrix. -/
theorem vecDot_matVecMul_correction (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (x xi : Vec d) :
    vecDot xi (matVecMul (M.nu • (1 : Mat d) +
        M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) xi) =
      M.nu * vecNormSq xi +
        M.nu⁻¹ * vecNormSq (matVecMul (cutoff m omega x) xi) := by
  rw [add_matVecMul, vecDot_add_right, smul_matVecMul, smul_matVecMul,
    vecDot_smul_right, vecDot_smul_right, matVecMul_one_vec, ← matVecMul_mul,
    vecDot_matVecMul_transpose]
  rfl

/-! ## The two averaged coefficient matrices of `e.CG.bounds.1` -/

/-- The harmonic-mean matrix of the cutoff coefficient is `nu^{-1} I` on every
triadic cube. -/
theorem averagedSymmPartInv_coefficientCutoff (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    Ch02.averagedSymmPartInv (Ch02.cubeDomain Q)
        (coefficientCutoffCoeffOn M m omega Q) = M.nu⁻¹ • (1 : Mat d) := by
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  ext i j
  show volumeAverage (openCubeSet Q)
      (fun x => ((symmPart (coefficientCutoff M.nu m omega x))⁻¹ : Mat d) i j) = _
  rw [show (fun x : Vec d => ((symmPart (coefficientCutoff M.nu m omega x))⁻¹ : Mat d) i j)
      = fun _ : Vec d => (M.nu⁻¹ • (1 : Mat d)) i j from
    funext fun x => congrFun (congrFun (inv_symmPart_coefficientCutoff M m omega x) i) j]
  exact volumeAverage_const hvol

/-- The averaged upper coefficient matrix of the cutoff coefficient. -/
theorem averagedSymmPartPlusCorrection_coefficientCutoff (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    Ch02.averagedSymmPartPlusCorrection (Ch02.cubeDomain Q)
        (coefficientCutoffCoeffOn M m omega Q) =
      Ch02.averageMat (Ch02.cubeDomain Q)
        (fun x => M.nu • (1 : Mat d) +
          M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) := by
  unfold Ch02.averagedSymmPartPlusCorrection
  congr 1
  funext x
  exact symmPartPlusCorrection_coefficientCutoff M m omega x

/-! ## Continuity and integrability on an origin cube -/

private theorem integrableOn_openCubeSet_of_continuous_of_bounded
    {Q : TriadicCube d} {f : Vec d → ℝ} (hcont : Continuous f) {B : ℝ}
    (hb : ∀ x ∈ openCubeSet Q, |f x| ≤ B) :
    IntegrableOn f (openCubeSet Q) volume := by
  refine Measure.integrableOn_of_bounded (M := B) (volume_openCubeSet_lt_top Q).ne
    hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  simpa only [Real.norm_eq_abs] using hb x hx

private theorem abs_one_entry_le_one (i j : Fin d) : |(1 : Mat d) i j| ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem continuous_transposeMul_cutoff_entry (m : ℤ) (omega : CutoffSample d)
    (i j : Fin d) :
    Continuous (fun x : Vec d =>
      (matTranspose (cutoff m omega x) * cutoff m omega x) i j) := by
  have h : (fun x : Vec d => (matTranspose (cutoff m omega x) * cutoff m omega x) i j)
      = fun x => ∑ r : Fin d, cutoff m omega x r i * cutoff m omega x r j := by
    funext x
    simp [Matrix.mul_apply, matTranspose]
  rw [h]
  exact continuous_finsetSum _ fun r _ =>
    (continuous_cutoff_entry m omega r i).mul (continuous_cutoff_entry m omega r j)

private theorem continuous_vecNormSq_matVecMul_cutoff (m : ℤ) (omega : CutoffSample d)
    (xi : Vec d) :
    Continuous (fun x : Vec d => vecNormSq (matVecMul (cutoff m omega x) xi)) := by
  show Continuous fun x : Vec d => ∑ i : Fin d,
    (∑ j : Fin d, cutoff m omega x i j * xi j) *
      (∑ j : Fin d, cutoff m omega x i j * xi j)
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ ?_ <;>
    exact continuous_finsetSum _ fun j _ =>
      (continuous_cutoff_entry m omega i j).mul continuous_const

private theorem abs_transposeMul_cutoff_entry_le (ell m : ℤ) (omega : CutoffSample d)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) (i j : Fin d) :
    |(matTranspose (cutoff m omega x) * cutoff m omega x) i j| ≤
      (d : ℝ) * cutoffLocalControl ell m omega ^ 2 := by
  have h : (matTranspose (cutoff m omega x) * cutoff m omega x) i j
      = ∑ r : Fin d, cutoff m omega x r i * cutoff m omega x r j := by
    simp [Matrix.mul_apply, matTranspose]
  rw [h]
  calc
    |∑ r : Fin d, cutoff m omega x r i * cutoff m omega x r j|
        ≤ ∑ r : Fin d, |cutoff m omega x r i * cutoff m omega x r j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin d, cutoffLocalControl ell m omega ^ 2 := by
      refine Finset.sum_le_sum fun r _ => ?_
      rw [abs_mul, pow_two]
      exact mul_le_mul (abs_cutoff_entry_le_cutoffLocalControl ell m omega hx r i)
        (abs_cutoff_entry_le_cutoffLocalControl ell m omega hx r j) (abs_nonneg _)
        (le_trans (abs_nonneg _)
          (abs_cutoff_entry_le_cutoffLocalControl ell m omega hx r i))
    _ = (d : ℝ) * cutoffLocalControl ell m omega ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The Frobenius mass of `k_m` is integrable on every origin cube: it is
continuous and bounded there by the proved local control of the cutoff. -/
theorem integrableOn_frobeniusMass_cutoff (ell m : ℤ) (omega : CutoffSample d) :
    IntegrableOn (fun x : Vec d => Ch02.matrixFrobeniusNormSq (cutoff m omega x))
      (openCubeSet (originCube d ell)) volume := by
  refine integrableOn_openCubeSet_of_continuous_of_bounded
    (B := (d : ℝ) ^ 2 * cutoffLocalControl ell m omega ^ 2)
    (Stream.continuous_frobeniusMass_cutoff m omega) ?_
  intro x hx
  rw [abs_of_nonneg (Ch02.matrixFrobeniusNormSq_nonneg (cutoff m omega x))]
  exact Stream.matrixFrobeniusNormSq_le_of_abs_entry_le fun i l =>
    abs_cutoff_entry_le_cutoffLocalControl ell m omega hx i l

private theorem integrableOn_correction_entry (M : ABKModel d) (ell m : ℤ)
    (omega : CutoffSample d) (i j : Fin d) :
    IntegrableOn (fun x : Vec d => (M.nu • (1 : Mat d) +
        M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) i j)
      (openCubeSet (originCube d ell)) volume := by
  have hrw : (fun x : Vec d => (M.nu • (1 : Mat d) +
      M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) i j)
      = fun x : Vec d => M.nu * ((1 : Mat d) i j) +
          M.nu⁻¹ * (matTranspose (cutoff m omega x) * cutoff m omega x) i j := by
    funext x
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [hrw]
  refine integrableOn_openCubeSet_of_continuous_of_bounded
    (B := |M.nu| * 1 + |M.nu⁻¹| * ((d : ℝ) * cutoffLocalControl ell m omega ^ 2))
    (continuous_const.add
      (continuous_const.mul (continuous_transposeMul_cutoff_entry m omega i j))) ?_
  intro x hx
  calc
    |M.nu * ((1 : Mat d) i j) +
        M.nu⁻¹ * (matTranspose (cutoff m omega x) * cutoff m omega x) i j|
        ≤ |M.nu * ((1 : Mat d) i j)| +
          |M.nu⁻¹ * (matTranspose (cutoff m omega x) * cutoff m omega x) i j| :=
      abs_add_le _ _
    _ = |M.nu| * |(1 : Mat d) i j| +
          |M.nu⁻¹| * |(matTranspose (cutoff m omega x) * cutoff m omega x) i j| := by
      rw [abs_mul, abs_mul]
    _ ≤ |M.nu| * 1 + |M.nu⁻¹| * ((d : ℝ) * cutoffLocalControl ell m omega ^ 2) := by
      gcongr
      · exact abs_one_entry_le_one i j
      · exact abs_transposeMul_cutoff_entry_le ell m omega hx i j

private theorem integrableOn_correction_quadratic (M : ABKModel d) (l m : ℤ)
    (omega : CutoffSample d) (xi : Vec d) :
    IntegrableOn (fun x : Vec d => vecDot xi (matVecMul (M.nu • (1 : Mat d) +
        M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) xi))
      (openCubeSet (originCube d l)) volume := by
  have hrw : (fun x : Vec d => vecDot xi (matVecMul (M.nu • (1 : Mat d) +
      M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) xi))
      = fun x : Vec d => M.nu * vecNormSq xi +
          M.nu⁻¹ * vecNormSq (matVecMul (cutoff m omega x) xi) :=
    funext fun x => vecDot_matVecMul_correction M m omega x xi
  rw [hrw]
  refine integrableOn_openCubeSet_of_continuous_of_bounded
    (B := |M.nu * vecNormSq xi| +
      |M.nu⁻¹| * ((d : ℝ) ^ 2 * cutoffLocalControl l m omega ^ 2 * vecNormSq xi))
    (continuous_const.add
      (continuous_const.mul (continuous_vecNormSq_matVecMul_cutoff m omega xi))) ?_
  intro x hx
  have hfro := Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
    (cutoff m omega x) xi
  have hmass : Ch02.matrixFrobeniusNormSq (cutoff m omega x) ≤
      (d : ℝ) ^ 2 * cutoffLocalControl l m omega ^ 2 :=
    Stream.matrixFrobeniusNormSq_le_of_abs_entry_le fun i j =>
      abs_cutoff_entry_le_cutoffLocalControl l m omega hx i j
  have hV : vecNormSq (matVecMul (cutoff m omega x) xi) ≤
      (d : ℝ) ^ 2 * cutoffLocalControl l m omega ^ 2 * vecNormSq xi :=
    hfro.trans (mul_le_mul_of_nonneg_right hmass (vecNormSq_nonneg xi))
  calc
    |M.nu * vecNormSq xi + M.nu⁻¹ * vecNormSq (matVecMul (cutoff m omega x) xi)|
        ≤ |M.nu * vecNormSq xi| +
          |M.nu⁻¹ * vecNormSq (matVecMul (cutoff m omega x) xi)| := abs_add_le _ _
    _ = |M.nu * vecNormSq xi| +
          |M.nu⁻¹| * |vecNormSq (matVecMul (cutoff m omega x) xi)| := by
      rw [abs_mul M.nu⁻¹]
    _ ≤ |M.nu * vecNormSq xi| +
          |M.nu⁻¹| * ((d : ℝ) ^ 2 * cutoffLocalControl l m omega ^ 2 * vecNormSq xi) := by
      gcongr
      rw [abs_of_nonneg (vecNormSq_nonneg _)]
      exact hV

/-! ## The two ends of the specialized chain -/

/-- **ABK26.**  The left-hand leg of `e.basecase.tightbound`: the harmonic mean
of the cutoff coefficient is exactly `nu Id`, so the coarse starred matrix
dominates `nu Id`. -/
theorem matLoewnerLE_nu_smul_one_sigmaStarCoarse_coefficientCutoff (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    MatLoewnerLE (M.nu • (1 : Mat d))
      (Ch02.sigmaStarCoarse (Ch02.cubeDomain Q)
        (coefficientCutoffCoeffOn M m omega Q)) := by
  have h := Ch02.harmonicMean_le_sigmaStarCoarse (Ch02.cubeDomain Q)
    (coefficientCutoffCoeffOn M m omega Q)
  rwa [averagedSymmPartInv_coefficientCutoff,
    inv_smul_one (inv_ne_zero M.nu_pos.ne'), inv_inv] at h

/-- **ABK26.**  The averaged upper coefficient matrix of the cutoff is dominated
by `nu (1 + nu^{-2} ||k_m||^2_{L2bar(cu_l)}) Id`. -/
theorem matLoewnerLE_averagedSymmPartPlusCorrection_coefficientCutoff
    (M : ABKModel d) (l m : ℤ) (omega : CutoffSample d) :
    MatLoewnerLE
      (Ch02.averagedSymmPartPlusCorrection (Ch02.cubeDomain (originCube d l))
        (coefficientCutoffCoeffOn M m omega (originCube d l)))
      ((M.nu * (1 + (M.nu ^ 2)⁻¹ *
        Ch02.average (Ch02.cubeDomain (originCube d l))
          (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))) • (1 : Mat d)) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d l))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet
        (originCube d l)).isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet (openCubeSet (originCube d l)) :=
    measurableSet_openCubeSet _
  have hvol : (volume (openCubeSet (originCube d l))).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos _).ne'
  intro xi
  have hsplit : (fun x : Vec d => M.nu * vecNormSq xi +
      M.nu⁻¹ * vecNormSq xi * Ch02.matrixFrobeniusNormSq (cutoff m omega x))
      = (fun _ : Vec d => M.nu * vecNormSq xi) +
        (M.nu⁻¹ * vecNormSq xi) •
          (fun x : Vec d => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hgInt : IntegrableOn ((fun _ : Vec d => M.nu * vecNormSq xi) +
      (M.nu⁻¹ * vecNormSq xi) •
        (fun x : Vec d => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))
      (openCubeSet (originCube d l)) volume :=
    (integrable_const _).add
      ((integrableOn_frobeniusMass_cutoff l m omega).smul (M.nu⁻¹ * vecNormSq xi))
  have hkey : vecDot xi (matVecMul
      (Ch02.averagedSymmPartPlusCorrection (Ch02.cubeDomain (originCube d l))
        (coefficientCutoffCoeffOn M m omega (originCube d l))) xi) ≤
      (M.nu * (1 + (M.nu ^ 2)⁻¹ *
        Ch02.average (Ch02.cubeDomain (originCube d l))
          (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))) * vecNormSq xi := by
    calc
      vecDot xi (matVecMul
          (Ch02.averagedSymmPartPlusCorrection (Ch02.cubeDomain (originCube d l))
            (coefficientCutoffCoeffOn M m omega (originCube d l))) xi)
          = volumeAverage (openCubeSet (originCube d l))
            (fun x => vecDot xi (matVecMul (M.nu • (1 : Mat d) +
              M.nu⁻¹ • (matTranspose (cutoff m omega x) * cutoff m omega x)) xi)) := by
          rw [averagedSymmPartPlusCorrection_coefficientCutoff]
          exact vecDot_matVecMul_volumeAverageMat
            (fun i j => integrableOn_correction_entry M l m omega i j) xi xi
      _ ≤ volumeAverage (openCubeSet (originCube d l))
            (fun x => M.nu * vecNormSq xi +
              M.nu⁻¹ * vecNormSq xi * Ch02.matrixFrobeniusNormSq (cutoff m omega x)) := by
          refine volumeAverage_le_volumeAverage_of_le_on hUmeas
            (integrableOn_correction_quadratic M l m omega xi) ?_ ?_
          · rw [hsplit]
            exact hgInt
          · intro x _hx
            rw [vecDot_matVecMul_correction]
            have hfro := Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
              (cutoff m omega x) xi
            have hnu : (0 : ℝ) ≤ M.nu⁻¹ := (inv_pos.mpr M.nu_pos).le
            nlinarith [mul_le_mul_of_nonneg_left hfro hnu]
      _ = M.nu * vecNormSq xi + M.nu⁻¹ * vecNormSq xi *
            volumeAverage (openCubeSet (originCube d l))
              (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) := by
          rw [hsplit, volumeAverage_add (integrable_const _)
            ((integrableOn_frobeniusMass_cutoff l m omega).smul (M.nu⁻¹ * vecNormSq xi)),
            volumeAverage_smul, volumeAverage_const hvol]
      _ = (M.nu * (1 + (M.nu ^ 2)⁻¹ *
            Ch02.average (Ch02.cubeDomain (originCube d l))
              (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))) *
                vecNormSq xi := by
          have hnu : M.nu ≠ 0 := M.nu_pos.ne'
          show M.nu * vecNormSq xi + M.nu⁻¹ * vecNormSq xi *
              volumeAverage (openCubeSet (originCube d l))
                (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)) =
            (M.nu * (1 + (M.nu ^ 2)⁻¹ *
              volumeAverage (openCubeSet (originCube d l))
                (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))) * vecNormSq xi
          field_simp
  rw [vecDot_matVecMul_smul_one]
  linarith

/-- **ABK26.**  The right-hand leg of
`e.basecase.tightbound`. -/
theorem matLoewnerLE_bCoarse_coefficientCutoff (M : ABKModel d) (l m : ℤ)
    (omega : CutoffSample d) :
    MatLoewnerLE
      (Ch02.bCoarse (Ch02.cubeDomain (originCube d l))
        (coefficientCutoffCoeffOn M m omega (originCube d l)))
      ((M.nu * (1 + (M.nu ^ 2)⁻¹ *
        Ch02.average (Ch02.cubeDomain (originCube d l))
          (fun x => Ch02.matrixFrobeniusNormSq (cutoff m omega x)))) • (1 : Mat d)) :=
  matLoewnerLE_trans
    (Ch02.bCoarse_le_averagedSymmPartPlusCorrection (Ch02.cubeDomain (originCube d l))
      (coefficientCutoffCoeffOn M m omega (originCube d l)))
    (matLoewnerLE_averagedSymmPartPlusCorrection_coefficientCutoff M l m omega)

/-- The composed lower leg: `nu Id` is dominated by every matrix of the
specialized chain, in particular by `b_m(cu_l)`. -/
theorem matLoewnerLE_nu_smul_one_bCoarse_coefficientCutoff (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    MatLoewnerLE (M.nu • (1 : Mat d))
      (Ch02.bCoarse (Ch02.cubeDomain Q) (coefficientCutoffCoeffOn M m omega Q)) :=
  matLoewnerLE_trans
    (matLoewnerLE_nu_smul_one_sigmaStarCoarse_coefficientCutoff M m omega Q)
    (matLoewnerLE_trans
      (Ch02.sigmaStarCoarse_le_sigmaCoarse (Ch02.cubeDomain Q)
        (coefficientCutoffCoeffOn M m omega Q))
      (Ch02.sigmaCoarse_le_bCoarse (Ch02.cubeDomain Q)
        (coefficientCutoffCoeffOn M m omega Q)))

end

end Algsuperdiff.Section3.Provider.Base

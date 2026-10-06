/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.CenteredCubeH1Interpolation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CubeFractionalNormBridge
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.H1HsTestEmbedding

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

@[expose]
public noncomputable def testCubeVectorH1
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    CubeVectorH1Function (originCube d n) where
  coord i := H1Function.ofContDiff (isOpen_openCubeSet _)
    ((contDiff_apply ℝ ℝ i).comp (hpsi.contDiff.of_le (by simp)))
    (hpsi.hasCompactSupport.comp_left rfl)

@[simp] private theorem testCubeVectorH1_toField
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi)
    (x : Vec d) :
    (testCubeVectorH1 n psi hpsi).toField x = psi x := by
  ext i
  rfl

@[simp] private theorem testCubeVectorH1_grad
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi)
    (i : Fin d) (x : Vec d) :
    ((testCubeVectorH1 n psi hpsi).coord i).grad x =
      smoothGrad (fun y => psi y i) x := by
  rfl

private theorem centeredEuclideanL2Field_ae_eq
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field =ᵐ[
        (centeredCubeDomain d n).normalizedVolume] psi := by
  filter_upwards with x
  exact testCubeVectorH1_toField n psi hpsi x

private theorem centeredEuclideanL2Field_norm_sq
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    ((centeredCubeDomain d n).normalizedEuclideanLpENorm 2
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field) ^ (2 : ℕ) =
      eVolumeAverage (openCubeSet (originCube d n))
        (fun x => ENNReal.ofReal (vecNormSq (psi x))) := by
  rw [(centeredCubeDomain d n).normalizedEuclideanLpENorm_congr_ae
    (2 : ℝ≥0∞) (centeredEuclideanL2Field_ae_eq n psi hpsi)]
  have hcont : Continuous (fun v : Vec d => euclideanNorm v) := by
    simp_rw [euclideanNorm_eq_norm_ofVec]
    exact (PiLp.continuous_toLp 2 fun _ : Fin d => ℝ).norm
  exact normalizedEuclideanLpENorm_two_sq_eq_eVolumeAverage
    (originCube d n) psi (hcont.comp hpsi.contDiff.continuous).aestronglyMeasurable

@[expose]
public noncomputable def pulledTestCompetitor
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    ContinuousKCompetitor d where
  coord i := H1Function.ofContDiff (isOpen_openCubeSet _)
    ((contDiff_apply ℝ ℝ i).comp
      ((hpsi.contDiff.of_le (by simp)).comp
        (contDiff_const_smul (centeredCubeScale n))))
    ((hpsi.hasCompactSupport.comp_smul (centeredCubeScale_ne_zero n)).comp_left rfl)

@[simp] private theorem pulledTestCompetitor_toField
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi)
    (x : Vec d) :
    (pulledTestCompetitor n psi hpsi).toField x =
      psi (centeredCubeScale n • x) := by
  ext i
  rfl

@[simp] private theorem pulledTestCompetitor_gradient
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi)
    (x : Vec d) (i j : Fin d) :
    (pulledTestCompetitor n psi hpsi).gradient x i j =
      centeredCubeScale n *
        smoothGrad (fun y => psi y i) (centeredCubeScale n • x) j := by
  change fderiv ℝ (fun z : Vec d => psi (centeredCubeScale n • z) i) x
      (basisVec j) = _
  have hderiv := fderiv_comp_smul
    (𝕜 := ℝ) (f := fun y : Vec d => psi y i) (x := x)
    (centeredCubeScale n)
  simpa only [smoothGrad, smul_apply, smul_eq_mul] using
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec j)) hderiv

private theorem lintegral_centeredNormalizedVolume_eq_eVolumeAverage
    {d : ℕ} (n : ℤ) (f : Vec d → ℝ≥0∞) :
    (∫⁻ x, f x ∂(centeredCubeDomain d n).normalizedVolume) =
      eVolumeAverage (openCubeSet (originCube d n)) f := by
  rw [centeredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  unfold eVolumeAverage normalizedCubeMeasure cubeMeasure
  rw [lintegral_smul_measure]
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hvol : volume (openCubeSet (originCube d n)) =
      ENNReal.ofReal (cubeVolume (originCube d n)) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top (originCube d n)).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg _ )])
  rw [hvol, ENNReal.ofReal_inv_of_pos (cubeVolume_pos _)]
  simp only [div_eq_mul_inv, smul_eq_mul]
  ac_rfl

private theorem eLpNorm_two_sq_eq_lintegral_enorm
    {α E : Type*} [MeasurableSpace α] [ENorm E] [TopologicalSpace E]
    (mu : Measure α) (F : α → E) (hF : AEStronglyMeasurable F mu) :
    eLpNorm F 2 mu ^ (2 : ℕ) = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂mu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul]
  norm_num

@[expose]
public def physicalGradientMatrix {d : ℕ}
    (psi : Vec d → Vec d) (x : Vec d) : Mat d :=
  fun i j => smoothGrad (fun y => psi y i) x j

@[expose]
public noncomputable def physicalGradientMagnitude {d : ℕ}
    (psi : Vec d → Vec d) (x : Vec d) : ℝ :=
  matrixFrobeniusMagnitude (physicalGradientMatrix psi x)

private theorem matrixFrobeniusMagnitude_smul_of_pos {d : ℕ}
    {c : ℝ} (hc : 0 < c) (A : Mat d) :
    matrixFrobeniusMagnitude (c • A) = c * matrixFrobeniusMagnitude A := by
  apply (sq_eq_sq₀ (matrixFrobeniusMagnitude_nonneg _)
    (mul_nonneg hc.le (matrixFrobeniusMagnitude_nonneg A))).mp
  rw [sq_matrixFrobeniusMagnitude, mul_pow, sq_matrixFrobeniusMagnitude]
  change (∑ i : Fin d, ∑ j : Fin d, (c * A i j) ^ 2) =
    c ^ 2 * ∑ i : Fin d, ∑ j : Fin d, A i j ^ 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]

private theorem physicalGradientMagnitude_memL2
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    MemLp (physicalGradientMagnitude psi) (2 : ℝ≥0∞)
      (centeredCubeDomain d n).normalizedVolume := by
  have hmat : MemLp
      (fun x => HilbertMat.ofMat (physicalGradientMatrix psi x))
      (2 : ℝ≥0∞) (centeredCubeDomain d n).normalizedVolume := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    rw [memLp_piLp_iff]
    intro i
    rw [memLp_piLp_iff]
    intro j
    simpa only [physicalGradientMatrix, HilbertMat.ofMat,
      PiLp.toLp_apply, testCubeVectorH1_grad] using
      ((testCubeVectorH1 n psi hpsi).coord i).grad_memL2_normalizedCubeMeasure j
  change MemLp
    (fun x => matrixFrobeniusMagnitude (physicalGradientMatrix psi x))
      (2 : ℝ≥0∞) (centeredCubeDomain d n).normalizedVolume
  simpa only [matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat] using hmat.norm

private theorem pulledGradientMagnitude_eq
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi)
    (x : Vec d) :
    matrixFrobeniusMagnitude
        ((pulledTestCompetitor n psi hpsi).gradient x) =
      centeredCubeScale n *
        physicalGradientMagnitude psi (centeredCubeScale n • x) := by
  unfold physicalGradientMagnitude
  rw [← matrixFrobeniusMagnitude_smul_of_pos
    (centeredCubeScale_pos n)]
  congr 1
  ext i j
  exact pulledTestCompetitor_gradient n psi hpsi x i j

private theorem ofReal_pulledGradientNorm_eq
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    ENNReal.ofReal
        (continuousKGradientNorm (pulledTestCompetitor n psi hpsi)) =
      ENNReal.ofReal (centeredCubeScale n) *
        eLpNorm (physicalGradientMagnitude psi) 2
          (centeredCubeDomain d n).normalizedVolume := by
  let G := pulledTestCompetitor n psi hpsi
  have hfinite : eLpNorm
      (fun x => matrixFrobeniusMagnitude (G.gradient x)) 2
      (unitCenteredCubeDomain d).normalizedVolume ≠ ∞ :=
    G.gradientFrobeniusMemL2.eLpNorm_ne_top
  unfold continuousKGradientNorm BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [ENNReal.ofReal_toReal hfinite]
  have hfun :
      (fun x => matrixFrobeniusMagnitude (G.gradient x)) =
        fun x => centeredCubeScale n *
          physicalGradientMagnitude psi (centeredCubeScale n • x) := by
    funext x
    exact pulledGradientMagnitude_eq n psi hpsi x
  rw [hfun]
  change eLpNorm
      ((centeredCubeScale n) •
        (physicalGradientMagnitude psi ∘ centeredCubeDilation (d := d) n))
      2 (unitCenteredCubeDomain d).normalizedVolume = _
  rw [eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal (centeredCubeScale_pos n).le]
  congr 1
  rw [show unitCenteredCubeDomain d = centeredCubeDomain d 0 by rfl]
  exact eLpNorm_comp_measurePreserving
    (physicalGradientMagnitude_memL2 n psi hpsi).aestronglyMeasurable
    (centeredCubeDilationMeasurePreserving n)

private theorem physicalGradient_eLpNorm_sq
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d) :
    eLpNorm (physicalGradientMagnitude psi) 2
          (centeredCubeDomain d n).normalizedVolume ^ (2 : ℕ) =
      eVolumeAverage (openCubeSet (originCube d n))
        (fun x => ENNReal.ofReal
          (∑ i : Fin d,
            vecNormSq (smoothGrad (fun y => psi y i) x))) := by
  have hmeas : Measurable (physicalGradientMagnitude psi) := by
    unfold physicalGradientMagnitude matrixFrobeniusMagnitude physicalGradientMatrix smoothGrad
    fun_prop
  rw [eLpNorm_two_sq_eq_lintegral_enorm _ _ hmeas.aestronglyMeasurable]
  calc
    (∫⁻ x, ‖physicalGradientMagnitude psi x‖ₑ ^ (2 : ℝ)
        ∂(centeredCubeDomain d n).normalizedVolume) =
        ∫⁻ x, ENNReal.ofReal
          (∑ i : Fin d,
            vecNormSq (smoothGrad (fun y => psi y i) x))
          ∂(centeredCubeDomain d n).normalizedVolume := by
      apply lintegral_congr
      intro x
      change ‖matrixFrobeniusMagnitude
        (physicalGradientMatrix psi x)‖ₑ ^ (2 : ℝ) = _
      rw [Real.enorm_eq_ofReal
        (matrixFrobeniusMagnitude_nonneg
          (physicalGradientMatrix psi x))]
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
        (matrixFrobeniusMagnitude_nonneg
          (physicalGradientMatrix psi x))]
      rw [sq_matrixFrobeniusMagnitude]
      unfold physicalGradientMatrix vecNormSq vecDot
      simp only [pow_two]
    _ = _ := lintegral_centeredNormalizedVolume_eq_eVolumeAverage n _

private theorem rpow_half_sq (x : ℝ≥0∞) :
    (x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem centeredL2_eq_root_valueEnergy
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    (centeredCubeDomain d n).normalizedEuclideanLpENorm 2
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field =
      (eVolumeAverage (openCubeSet (originCube d n))
        (fun x => ENNReal.ofReal (vecNormSq (psi x)))) ^ (1 / 2 : ℝ) := by
  calc
    (centeredCubeDomain d n).normalizedEuclideanLpENorm 2
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field =
      (((centeredCubeDomain d n).normalizedEuclideanLpENorm 2
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field) ^
          (2 : ℕ)) ^ (1 / 2 : ℝ) := (rpow_half_sq _).symm
    _ = _ := by rw [centeredEuclideanL2Field_norm_sq]

private theorem physicalGradient_eLpNorm_eq_root
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d) :
    eLpNorm (physicalGradientMagnitude psi) 2
          (centeredCubeDomain d n).normalizedVolume =
      (eVolumeAverage (openCubeSet (originCube d n))
        (fun x => ENNReal.ofReal
          (∑ i : Fin d,
            vecNormSq (smoothGrad (fun y => psi y i) x)))) ^ (1 / 2 : ℝ) := by
  calc
    eLpNorm (physicalGradientMagnitude psi) 2
          (centeredCubeDomain d n).normalizedVolume =
      (eLpNorm (physicalGradientMagnitude psi) 2
          (centeredCubeDomain d n).normalizedVolume ^ (2 : ℕ)) ^
            (1 / 2 : ℝ) := (rpow_half_sq _).symm
    _ = _ := by rw [physicalGradient_eLpNorm_sq]

private theorem h1_volumeWeight_eq {d : ℕ} [NeZero d] (n : ℤ) :
    volume (openCubeSet (originCube d n)) ^ (-(2 : ℝ) / (d : ℝ)) =
      (ENNReal.ofReal (centeredCubeScale n)) ^ (-2 : ℝ) := by
  have hvol : volume (openCubeSet (originCube d n)) =
      ENNReal.ofReal (cubeVolume (originCube d n)) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top (originCube d n)).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg _)])
  rw [hvol, cubeVolume_eq_pow_scale]
  change ENNReal.ofReal ((centeredCubeScale n) ^ d) ^
      (-(2 : ℝ) / (d : ℝ)) = _
  rw [ENNReal.ofReal_pow (centeredCubeScale_pos n).le]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  field_simp

private theorem root_le_mul_root_of_inv_sq_mul_le
    {a x y : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ∞)
    (h : a ^ (-2 : ℝ) * x ≤ y) :
    x ^ (1 / 2 : ℝ) ≤ a * y ^ (1 / 2 : ℝ) := by
  have hxy : x ≤ a ^ (2 : ℝ) * y := by
    calc
      x = a ^ (2 : ℝ) * (a ^ (-2 : ℝ) * x) := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ ha0 hat]
        norm_num
      _ ≤ a ^ (2 : ℝ) * y := mul_le_mul_right h _
  calc
    x ^ (1 / 2 : ℝ) ≤
        (a ^ (2 : ℝ) * y) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hxy (by norm_num)
    _ = (a ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        y ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg]
      norm_num
    _ = a * y ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num

private theorem l2_add_pulledGradient_le_h1
    {d : ℕ} [NeZero d] (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    (centeredCubeDomain d n).normalizedEuclideanLpENorm 2
          (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field +
        ENNReal.ofReal
          (continuousKGradientNorm (pulledTestCompetitor n psi hpsi)) ≤
      2 * ENNReal.ofReal (centeredCubeScale n) *
        (h1NormSq (openCubeSet (originCube d n)) psi) ^ (1 / 2 : ℝ) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (centeredCubeScale n)
  let E0 : ℝ≥0∞ := eVolumeAverage (openCubeSet (originCube d n))
    (fun x => ENNReal.ofReal (vecNormSq (psi x)))
  let E1 : ℝ≥0∞ := eVolumeAverage (openCubeSet (originCube d n))
    (fun x => ENNReal.ofReal
      (∑ i : Fin d, vecNormSq (smoothGrad (fun y => psi y i) x)))
  let H : ℝ≥0∞ := h1NormSq (openCubeSet (originCube d n)) psi
  have ha0 : a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos n)
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hH : H = a ^ (-2 : ℝ) * E0 + E1 := by
    dsimp only [H, a, E0, E1]
    unfold h1NormSq
    rw [h1_volumeWeight_eq n]
  have hE0 : a ^ (-2 : ℝ) * E0 ≤ H := by
    rw [hH]
    exact le_add_right le_rfl
  have hE1 : E1 ≤ H := by
    rw [hH]
    exact le_add_left le_rfl
  have hL :
      (centeredCubeDomain d n).normalizedEuclideanLpENorm 2
          (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field ≤
        a * H ^ (1 / 2 : ℝ) := by
    rw [centeredL2_eq_root_valueEnergy]
    exact root_le_mul_root_of_inv_sq_mul_le ha0 hat hE0
  have hGrad :
      ENNReal.ofReal
          (continuousKGradientNorm (pulledTestCompetitor n psi hpsi)) ≤
        a * H ^ (1 / 2 : ℝ) := by
    rw [ofReal_pulledGradientNorm_eq,
      physicalGradient_eLpNorm_eq_root]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hE1 (by norm_num)) a
  calc
    (centeredCubeDomain d n).normalizedEuclideanLpENorm 2
          (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field +
        ENNReal.ofReal
          (continuousKGradientNorm (pulledTestCompetitor n psi hpsi)) ≤
      a * H ^ (1 / 2 : ℝ) + a * H ^ (1 / 2 : ℝ) :=
        add_le_add hL hGrad
    _ = 2 * a * H ^ (1 / 2 : ℝ) := by ring

private theorem pullback_toField_eq_pulledTest
    {d : ℕ} (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field.pullbackToUnit.toField =
      (pulledTestCompetitor n psi hpsi).toField := by
  funext x
  rw [CenteredCubeEuclideanL2Field.pullbackToUnit_apply]
  change (testCubeVectorH1 n psi hpsi).toField
      (centeredCubeScale n • x) = _
  rw [
    testCubeVectorH1_toField,
    pulledTestCompetitor_toField]

private theorem centeredHsFull_le_h1_root
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (n : ℤ) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    centeredCubeEuclideanHsFullENorm s
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field ≤
      (2 * continuousKEuclideanHsFullENormConstant s d *
          (1 + (ENNReal.ofReal ((2 - 2 * s.1)⁻¹)) ^ ((2 : ℝ)⁻¹))) *
        (ENNReal.ofReal (centeredCubeScale n)) ^ (1 - s.1) *
          (h1NormSq (openCubeSet (originCube d n)) psi) ^ (1 / 2 : ℝ) := by
  let F := (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field
  let G := pulledTestCompetitor n psi hpsi
  let a : ℝ≥0∞ := ENNReal.ofReal (centeredCubeScale n)
  let A : ℝ≥0∞ := continuousKEuclideanHsFullENormConstant s d
  let B : ℝ≥0∞ :=
    (ENNReal.ofReal ((2 - 2 * s.1)⁻¹)) ^ ((2 : ℝ)⁻¹)
  let H : ℝ≥0∞ := h1NormSq (openCubeSet (originCube d n)) psi
  have ha0 : a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos n)
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hsemi : continuousKSeminorm s F.pullbackToUnit ≤
      B * ENNReal.ofReal (continuousKGradientNorm G) := by
    simpa only [B, F, G] using
      continuousKSeminorm_le_gradientNorm_of_eq_toField s F.pullbackToUnit G
        (pullback_toField_eq_pulledTest n psi hpsi)
  have hfull : continuousKFullENorm s F.pullbackToUnit ≤
      (1 + B) *
        ((centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
          ENNReal.ofReal (continuousKGradientNorm G)) := by
    rw [continuousKFullENorm_eq]
    rw [CenteredCubeEuclideanL2Field.normalizedEuclideanLpENorm_pullbackToUnit]
    calc
      (centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
          continuousKSeminorm s F.pullbackToUnit ≤
        (centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
          B * ENNReal.ofReal (continuousKGradientNorm G) :=
        add_le_add le_rfl hsemi
      _ ≤ (1 + B) *
          ((centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
            ENNReal.ofReal (continuousKGradientNorm G)) := by
        calc
          _ ≤ (1 + B) *
                (centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
              (1 + B) * ENNReal.ofReal (continuousKGradientNorm G) := by
            exact add_le_add
              (by
                simpa only [one_mul] using mul_le_mul_left
                  (show (1 : ℝ≥0∞) ≤ 1 + B from le_add_right le_rfl)
                  ((centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F))
              (mul_le_mul_left
                (show B ≤ 1 + B from le_add_left le_rfl) _)
          _ = _ := by ring
  have hLK :
      (centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
          ENNReal.ofReal (continuousKGradientNorm G) ≤
        2 * a * H ^ (1 / 2 : ℝ) := by
    simpa only [F, G, a, H] using
      l2_add_pulledGradient_le_h1 n psi hpsi
  rw [centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit]
  calc
    a ^ (-s.1) * euclideanHsFullENorm s F.pullbackToUnit ≤
        a ^ (-s.1) * (A * continuousKFullENorm s F.pullbackToUnit) := by
      exact mul_le_mul_right
        (by simpa only [A] using
          euclideanHsFullENorm_le_mul_continuousKFullENorm s F.pullbackToUnit) _
    _ ≤ a ^ (-s.1) *
        (A * ((1 + B) *
          ((centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F +
            ENNReal.ofReal (continuousKGradientNorm G)))) := by
      gcongr
    _ ≤ a ^ (-s.1) * (A * ((1 + B) *
          (2 * a * H ^ (1 / 2 : ℝ)))) := by
      gcongr
    _ = (2 * A * (1 + B)) * a ^ (1 - s.1) * H ^ (1 / 2 : ℝ) := by
      rw [show (1 - s.1) = (-s.1) + 1 by ring,
        ENNReal.rpow_add _ _ ha0 hat, ENNReal.rpow_one]
      ring
    _ = _ := by rfl

private theorem centeredHsEnergy_eq_fracSeminormSq
    {d : ℕ} (s : FractionalOrder) (n : ℤ)
    (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    centeredCubeEuclideanHsEnergy s
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field =
      fracSeminormSq (openCubeSet (originCube d n)) s.1 psi := by
  let Q : TriadicCube d := originCube d n
  let mu : Measure (Vec d) := volume.restrict (cubeSet Q)
  let K : Vec d × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal
    (vecNormSq (psi z.1 - psi z.2) /
      euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1))
  have hpsiCube : AEStronglyMeasurable psi mu := by
    rw [show mu = volume.restrict (openCubeSet Q) by
      simp only [mu, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
    exact hpsi.contDiff.continuous.aestronglyMeasurable.restrict
  have hfst : AEStronglyMeasurable (fun z : Vec d × Vec d => psi z.1)
      (mu.prod mu) :=
    hpsiCube.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun z : Vec d × Vec d => psi z.2)
      (mu.prod mu) :=
    hpsiCube.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hnum : AEMeasurable (fun z : Vec d × Vec d =>
      vecNormSq (psi z.1 - psi z.2)) (mu.prod mu) :=
    (continuous_vecNormSq.measurable.comp_aemeasurable
      (hfst.sub hsnd).aemeasurable)
  have hdist : Continuous (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2) := by
    unfold euclideanDist euclideanNorm
    exact (continuous_vecNormSq.comp (continuous_fst.sub continuous_snd)).sqrt
  have hden : Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1)) :=
    hdist.measurable.pow measurable_const
  have hK : AEMeasurable K (mu.prod mu) :=
    (hnum.div hden.aemeasurable).ennreal_ofReal
  rw [centeredCubeEuclideanHsEnergy_eq_lintegral,
    centeredCubeEuclideanHsProductMeasure_eq_gagliardoCubeMeasure]
  have hfield :
      (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field.toField = psi := by
    funext x
    exact testCubeVectorH1_toField n psi hpsi x
  rw [hfield]
  simp_rw [HilbertVec.norm_sq_eq_sum_sq, ← vecNormSq_eq_sum_sq]
  change (∫⁻ z, K z ∂Gagliardo.gagliardoCubeMeasure Q) = _
  unfold fracSeminormSq eVolumeAverage Gagliardo.gagliardoCubeMeasure
    normalizedCubeMeasure cubeMeasure
  rw [Measure.prod_smul_left, lintegral_smul_measure]
  change ENNReal.ofReal (cubeVolume Q)⁻¹ •
      (∫⁻ z, K z ∂(mu.prod mu)) = _
  rw [lintegral_prod K hK]
  rw [show mu = volume.restrict (openCubeSet Q) by
    simp only [mu, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  simp only [K, euclideanDist, euclideanNorm]
  have hvol : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  rw [hvol, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  simp only [div_eq_mul_inv, smul_eq_mul]
  ac_rfl

private theorem hs_volumeWeight_eq {d : ℕ} [NeZero d]
    (s : FractionalOrder) (n : ℤ) :
    volume (openCubeSet (originCube d n)) ^
        (-(2 * s.1) / (d : ℝ)) =
      (ENNReal.ofReal (centeredCubeScale n)) ^ (-2 * s.1) := by
  have hvol : volume (openCubeSet (originCube d n)) =
      ENNReal.ofReal (cubeVolume (originCube d n)) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top (originCube d n)).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg _)])
  rw [hvol, cubeVolume_eq_pow_scale]
  change ENNReal.ofReal ((centeredCubeScale n) ^ d) ^
      (-(2 * s.1) / (d : ℝ)) = _
  rw [ENNReal.ofReal_pow (centeredCubeScale_pos n).le]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  field_simp

private theorem rpow_half_nat_sq (x : ℝ≥0∞) :
    (x ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem add_sq_le_sq_add (x y : ℝ≥0∞) :
    x ^ (2 : ℕ) + y ^ (2 : ℕ) ≤ (x + y) ^ (2 : ℕ) := by
  calc
    x ^ (2 : ℕ) + y ^ (2 : ℕ) =
        x ^ (2 : ℕ) + 0 + y ^ (2 : ℕ) := by simp
    _ ≤ x ^ (2 : ℕ) + (x * y + y * x) + y ^ (2 : ℕ) := by
      gcongr
      exact zero_le
    _ = (x + y) ^ (2 : ℕ) := by ring

private theorem hsNormSq_le_centeredHsFull_sq
    {d : ℕ} [NeZero d] (s : FractionalOrder) (n : ℤ)
    (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet (originCube d n)) psi) :
    hsNormSq (openCubeSet (originCube d n)) s.1 psi ≤
      (centeredCubeEuclideanHsFullENorm s
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field) ^ (2 : ℕ) := by
  let F := (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field
  let a : ℝ≥0∞ := ENNReal.ofReal (centeredCubeScale n)
  let L : ℝ≥0∞ :=
    (centeredCubeDomain d n).normalizedEuclideanLpENorm 2 F
  let X : ℝ≥0∞ := a ^ (-s.1) * L
  let Y : ℝ≥0∞ := centeredCubeEuclideanHsESeminorm s F
  have hX : X ^ (2 : ℕ) =
      volume (openCubeSet (originCube d n)) ^
          (-(2 * s.1) / (d : ℝ)) *
        eVolumeAverage (openCubeSet (originCube d n))
          (fun x => ENNReal.ofReal (vecNormSq (psi x))) := by
    dsimp only [X, a, L, F]
    rw [mul_pow]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    have hexp : (-s.1) * ((2 : ℕ) : ℝ) = -2 * s.1 := by
      norm_num
      ring
    rw [hexp]
    rw [← hs_volumeWeight_eq (d := d) s n]
    rw [centeredEuclideanL2Field_norm_sq n psi hpsi]
  have hY : Y ^ (2 : ℕ) =
      fracSeminormSq (openCubeSet (originCube d n)) s.1 psi := by
    dsimp only [Y]
    unfold centeredCubeEuclideanHsESeminorm
    rw [rpow_half_nat_sq]
    exact centeredHsEnergy_eq_fracSeminormSq s n psi hpsi
  have hFull : centeredCubeEuclideanHsFullENorm s F = X + Y := by
    rw [centeredCubeEuclideanHsFullENorm_eq,
      exactOverlapRootWeight_originCube_eq_scale_rpow]
  unfold hsNormSq
  rw [← hX, ← hY, hFull]
  exact add_sq_le_sq_add X Y

private theorem centeredScale_orderPower_eq
    (s : FractionalOrder) (n : ℤ) :
    (ENNReal.ofReal (centeredCubeScale n)) ^ (2 * (1 - s.1)) =
      ENNReal.ofReal
        ((3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))) := by
  have hscale : ENNReal.ofReal (centeredCubeScale n) =
      (3 : ℝ≥0∞) ^ (n : ℝ) := by
    unfold centeredCubeScale
    rw [← Real.rpow_intCast]
    rw [← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < 3 by norm_num)]
    norm_num
  rw [hscale, ← ENNReal.rpow_mul]
  have hrhs : ENNReal.ofReal
      ((3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))) =
        (3 : ℝ≥0∞) ^ (2 * (1 - s.1) * (n : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < 3 by norm_num)]
    norm_num
  rw [hrhs]
  congr 1
  ring

private theorem scaled_root_sq
    (C a H : ℝ≥0∞) (t : ℝ) :
    (C * a ^ t * H ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) =
      C ^ (2 : ℕ) * a ^ (2 * t) * H := by
  rw [mul_pow, mul_pow]
  have ha : (a ^ t) ^ (2 : ℕ) = a ^ (2 * t) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [ha, rpow_half_nat_sq]

/-- Quantitative `H^1`-to-`H^s` embedding for the complete local test class
on every origin cube. The constant depends only on the dimension and order. -/
theorem exists_hsNormSq_le_h1NormSq
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℤ) (psi : Vec d → Vec d),
        IsLocalVecTest (openCubeSet (originCube d n)) psi →
          hsNormSq (openCubeSet (originCube d n)) s.1 psi ≤
            ENNReal.ofReal
                (K * (3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))) *
              h1NormSq (openCubeSet (originCube d n)) psi := by
  let A : ℝ≥0∞ := continuousKEuclideanHsFullENormConstant s d
  let B : ℝ≥0∞ :=
    (ENNReal.ofReal ((2 - 2 * s.1)⁻¹)) ^ ((2 : ℝ)⁻¹)
  let C : ℝ≥0∞ := 2 * A * (1 + B)
  have hBtop : B < ∞ := by
    dsimp only [B]
    finiteness
  have hCtop : C < ∞ := by
    dsimp only [C, A]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num)
        (continuousKEuclideanHsFullENormConstant_lt_top s d))
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hBtop⟩)
  let K : ℝ := C.toReal ^ (2 : ℕ) + 1
  have hKpos : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hKpos, ?_⟩
  intro n psi hpsi
  let H : ℝ≥0∞ := h1NormSq (openCubeSet (originCube d n)) psi
  let a : ℝ≥0∞ := ENNReal.ofReal (centeredCubeScale n)
  have hfull : centeredCubeEuclideanHsFullENorm s
      (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field ≤
        C * a ^ (1 - s.1) * H ^ ((2 : ℝ)⁻¹) := by
    simpa only [C, A, B, a, H, one_div] using
      centeredHsFull_le_h1_root s n psi hpsi
  have hsq :
      (centeredCubeEuclideanHsFullENorm s
        (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field) ^ (2 : ℕ) ≤
        (C * a ^ (1 - s.1) * H ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) :=
    pow_le_pow_left' hfull 2
  have hCoeff : C ^ (2 : ℕ) ≤ ENNReal.ofReal K := by
    calc
      C ^ (2 : ℕ) = (ENNReal.ofReal C.toReal) ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_toReal hCtop.ne]
      _ = ENNReal.ofReal (C.toReal ^ (2 : ℕ)) := by
        rw [ENNReal.ofReal_pow (ENNReal.toReal_nonneg)]
      _ ≤ ENNReal.ofReal K := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [K]
        exact le_add_of_nonneg_right zero_le_one
  calc
    hsNormSq (openCubeSet (originCube d n)) s.1 psi ≤
        (centeredCubeEuclideanHsFullENorm s
          (testCubeVectorH1 n psi hpsi).centeredEuclideanL2Field) ^ (2 : ℕ) :=
      hsNormSq_le_centeredHsFull_sq s n psi hpsi
    _ ≤ (C * a ^ (1 - s.1) * H ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) := hsq
    _ = C ^ (2 : ℕ) * a ^ (2 * (1 - s.1)) * H :=
      scaled_root_sq C a H (1 - s.1)
    _ ≤ ENNReal.ofReal K * a ^ (2 * (1 - s.1)) * H := by
      gcongr
    _ = ENNReal.ofReal K *
          ENNReal.ofReal
            ((3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))) * H := by
      rw [centeredScale_orderPower_eq]
    _ = ENNReal.ofReal
          (K * (3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))) * H := by
      rw [ENNReal.ofReal_mul hKpos.le]
    _ = _ := by rfl

end

end HighContrast
end HCPolySupport

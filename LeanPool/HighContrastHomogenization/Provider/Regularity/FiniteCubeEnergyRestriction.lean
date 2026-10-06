/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingPDE
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.Energy
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-!
# High-contrast homogenization: Provider.Regularity.FiniteCubeEnergyRestriction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized energy under centered-cube restriction

This module identifies the weighted gradient norm with the Chapter 3
energy norm and records the normalized-volume loss under restriction to a
centered child cube.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The weighted gradient norm is the normalized local symmetric
energy on a triadic cube. -/
theorem weightedGradNorm_eq_localSymmetricEnergyENorm
    {d : ℕ} (Q : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    weightedGradNorm a.toCoeffField (openCubeSet Q) u.grad =
      Book.Ch03.ABK26.localSymmetricEnergyENorm Q a u := by
  have hvol : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  unfold weightedGradNorm eVolumeAverage
  rw [Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_coefficientEnergyDensity]
  rw [lintegral_normalizedCubeMeasure_eq]
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hvol, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  simp only [div_eq_mul_inv]
  ac_rfl

/-- The local symmetric energy is the `ENNReal` realization of the public
Chapter 3 energy norm. -/
theorem localSymmetricEnergyENorm_eq_ofReal_h1EnergyNormOnCube
    {d : ℕ} (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    Book.Ch03.ABK26.localSymmetricEnergyENorm Q (a.coeffOn Q) u =
      ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube Q a u) := by
  let X : ℝ := Book.Ch03.localizedCoeffEnergyValue
    (openCubeSet Q) (a.coeffOn Q) u
  have havg : cubeAverage Q
        (coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.grad) = X := by
    calc
      cubeAverage Q
          (coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.grad) =
          volumeAverage (openCubeSet Q)
            (coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.grad) := by
        simp [cubeAverage, volumeAverage,
          volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
          setIntegral_cubeSet_eq_setIntegral_openCubeSet]
      _ = X := by
        exact
          (Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity
            (openCubeSet Q) (a.coeffOn Q) u).symm
  have hX : 0 ≤ X := by
    dsimp [X]
    rw [←
      Book.Ch03.cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (Book.Ch03.publicCoeffField Q a) u.grad
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a)
  rw [Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_ofReal_cubeAverage_coefficientEnergyDensity
    (u := (u : H1Function (openCubeSet Q))), havg]
  unfold Book.Ch03.h1EnergyNormOnCube
  rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)]

/-- The weighted gradient norm is exactly the `ENNReal` realization of
the public Chapter 3 cube energy norm. -/
theorem weightedGradNorm_eq_ofReal_h1EnergyNormOnCube
    {d : ℕ} (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    weightedGradNorm (a.coeffOn Q).toCoeffField (openCubeSet Q) u.grad =
      ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube Q a u) := by
  rw [weightedGradNorm_eq_localSymmetricEnergyENorm
      (u := (u : H1Function (openCubeSet Q))),
    localSymmetricEnergyENorm_eq_ofReal_h1EnergyNormOnCube]

/-- Restricting a centered-cube solution to its centered child loses at most
the number of ordinary children in the normalized energy norm. -/
theorem h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_one_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) :
    Book.Ch03.h1EnergyNormOnCube (originCube d (m - 1)) a
        (finiteCubeSolutionRestriction a (by omega : m - 1 ≤ m) u).toH1 ≤
      ((3 ^ d : ℕ) : ℝ) *
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
  let Q : TriadicCube d := originCube d m
  let R : TriadicCube d := originCube d (m - 1)
  let uR : Book.Ch03.CubeSolution R a :=
    finiteCubeSolutionRestriction a (by omega : m - 1 ≤ m) u
  let A : ℝ≥0∞ := ENNReal.ofReal ((3 ^ d : ℕ) : ℝ)
  let f : Vec d → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.toH1.grad x)
  have hRQ : R = CubeCalderonZygmund.centralDescendant Q 1 := by
    simpa only [Q, R, pow_one, show m - ((1 : ℕ) : ℤ) = m - 1 by simp] using
      (centralDescendant_originCube_eq_originCube_sub (d := d) m 1).symm
  have hsub : openCubeSet R ⊆ openCubeSet Q := by
    simpa only [Q, R] using
      openCubeSet_originCube_subset_of_le (d := d) (by omega : m - 1 ≤ m)
  have hcoeffVol : (a.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)] (a.coeffOn Q).toCoeffField :=
    a.restrictsTo_of_subset hsub
  have hcoeff : ∀ᵐ x ∂normalizedCubeMeasure R,
      (a.coeffOn R).toCoeffField x = (a.coeffOn Q).toCoeffField x := by
    simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      MeasureTheory.Measure.ae_smul_measure hcoeffVol
        (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hinner : Book.Ch03.ABK26.localSymmetricEnergyENorm R (a.coeffOn R) uR.toH1 =
      (∫⁻ x, f x ∂normalizedCubeMeasure R) ^ (1 / 2 : ℝ) := by
    rw [Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_coefficientEnergyDensity
      (u := (uR.toH1 : H1Function (openCubeSet R)))]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hcoeff] with x hx
    simp only [f, uR, coefficientEnergyDensity, finiteCubeSolutionRestriction_grad, hx]
  have hmeasure : normalizedCubeMeasure R =
      A • (normalizedCubeMeasure Q).restrict (cubeSet R) := by
    rw [hRQ,
      CubeCalderonZygmund.normalizedCubeMeasure_centralDescendant_eq_smul_restrict]
    simp only [A, pow_one]
  have hrestrict : ∫⁻ x, f x ∂(normalizedCubeMeasure Q).restrict (cubeSet R) ≤
      ∫⁻ x, f x ∂normalizedCubeMeasure Q :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero d (by norm_num : (3 : ℕ) ≠ 0))
  have hAroot : A ^ (1 / 2 : ℝ) ≤ A := by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le hA (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hlocal : Book.Ch03.ABK26.localSymmetricEnergyENorm R (a.coeffOn R) uR.toH1 ≤
      A * Book.Ch03.ABK26.localSymmetricEnergyENorm Q (a.coeffOn Q) u.toH1 := by
    rw [hinner, hmeasure, MeasureTheory.lintegral_smul_measure, smul_eq_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_coefficientEnergyDensity
      (u := (u.toH1 : H1Function (openCubeSet Q)))]
    exact mul_le_mul hAroot
      (ENNReal.rpow_le_rpow hrestrict (by norm_num))
      (by positivity) (by positivity)
  have henn : ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube R a uR.toH1) ≤
      ENNReal.ofReal (((3 ^ d : ℕ) : ℝ) *
        Book.Ch03.h1EnergyNormOnCube Q a u.toH1) := by
    calc
      ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube R a uR.toH1) =
          Book.Ch03.ABK26.localSymmetricEnergyENorm R (a.coeffOn R) uR.toH1 :=
        (localSymmetricEnergyENorm_eq_ofReal_h1EnergyNormOnCube R a uR.toH1).symm
      _ ≤ A * Book.Ch03.ABK26.localSymmetricEnergyENorm Q (a.coeffOn Q) u.toH1 := hlocal
      _ = ENNReal.ofReal (((3 ^ d : ℕ) : ℝ) *
          Book.Ch03.h1EnergyNormOnCube Q a u.toH1) := by
        rw [localSymmetricEnergyENorm_eq_ofReal_h1EnergyNormOnCube]
        change ENNReal.ofReal (((3 ^ d : ℕ) : ℝ)) *
            ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube Q a u.toH1) =
          ENNReal.ofReal (((3 ^ d : ℕ) : ℝ) *
            Book.Ch03.h1EnergyNormOnCube Q a u.toH1)
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ))]
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity)
      (by exact Real.sqrt_nonneg _))).1 henn

/-- Restriction by an arbitrary fixed number of centered scales loses at
most the corresponding power of the number of ordinary children. -/
theorem h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_nat_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (N : ℕ) (u : Book.Ch03.CubeSolution (originCube d m) a) :
    Book.Ch03.h1EnergyNormOnCube (originCube d (m - (N : ℤ))) a
        (finiteCubeSolutionRestriction a (by omega : m - (N : ℤ) ≤ m) u).toH1 ≤
      ((((3 ^ d) ^ N : ℕ) : ℝ)) *
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
  let Q : TriadicCube d := originCube d m
  let R : TriadicCube d := originCube d (m - (N : ℤ))
  let uR : Book.Ch03.CubeSolution R a :=
    finiteCubeSolutionRestriction a (by omega : m - (N : ℤ) ≤ m) u
  let A : ℝ≥0∞ := ENNReal.ofReal ((((3 ^ d) ^ N : ℕ) : ℝ))
  let f : Vec d → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.toH1.grad x)
  have hRQ : R = CubeCalderonZygmund.centralDescendant Q N := by
    simpa only [Q, R] using
      (centralDescendant_originCube_eq_originCube_sub (d := d) m N).symm
  have hsub : openCubeSet R ⊆ openCubeSet Q := by
    simpa only [Q, R] using
      openCubeSet_originCube_subset_of_le
        (d := d) (by omega : m - (N : ℤ) ≤ m)
  have hcoeffVol : (a.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)] (a.coeffOn Q).toCoeffField :=
    a.restrictsTo_of_subset hsub
  have hcoeff : ∀ᵐ x ∂normalizedCubeMeasure R,
      (a.coeffOn R).toCoeffField x = (a.coeffOn Q).toCoeffField x := by
    simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      MeasureTheory.Measure.ae_smul_measure hcoeffVol
        (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hinner : Book.Ch03.ABK26.localSymmetricEnergyENorm R
        (a.coeffOn R) uR.toH1 =
      (∫⁻ x, f x ∂normalizedCubeMeasure R) ^ (1 / 2 : ℝ) := by
    rw [Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_coefficientEnergyDensity
      (u := (uR.toH1 : H1Function (openCubeSet R)))]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hcoeff] with x hx
    simp only [f, uR, coefficientEnergyDensity,
      finiteCubeSolutionRestriction_grad, hx]
  have hmeasure : normalizedCubeMeasure R =
      A • (normalizedCubeMeasure Q).restrict (cubeSet R) := by
    rw [hRQ,
      CubeCalderonZygmund.normalizedCubeMeasure_centralDescendant_eq_smul_restrict]
  have hrestrict : ∫⁻ x, f x ∂(normalizedCubeMeasure Q).restrict (cubeSet R) ≤
      ∫⁻ x, f x ∂normalizedCubeMeasure Q :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero N (pow_ne_zero d (by norm_num : (3 : ℕ) ≠ 0)))
  have hAroot : A ^ (1 / 2 : ℝ) ≤ A := by
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le hA (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hlocal : Book.Ch03.ABK26.localSymmetricEnergyENorm R
        (a.coeffOn R) uR.toH1 ≤
      A * Book.Ch03.ABK26.localSymmetricEnergyENorm Q
        (a.coeffOn Q) u.toH1 := by
    rw [hinner, hmeasure, MeasureTheory.lintegral_smul_measure, smul_eq_mul,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [Book.Ch03.ABK26.localSymmetricEnergyENorm_eq_coefficientEnergyDensity
      (u := (u.toH1 : H1Function (openCubeSet Q)))]
    exact mul_le_mul hAroot
      (ENNReal.rpow_le_rpow hrestrict (by norm_num))
      (by positivity) (by positivity)
  have henn : ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube R a uR.toH1) ≤
      ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ)) *
        Book.Ch03.h1EnergyNormOnCube Q a u.toH1) := by
    calc
      ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube R a uR.toH1) =
          Book.Ch03.ABK26.localSymmetricEnergyENorm R
            (a.coeffOn R) uR.toH1 :=
        (localSymmetricEnergyENorm_eq_ofReal_h1EnergyNormOnCube
          R a uR.toH1).symm
      _ ≤ A * Book.Ch03.ABK26.localSymmetricEnergyENorm Q
          (a.coeffOn Q) u.toH1 := hlocal
      _ = ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ)) *
          Book.Ch03.h1EnergyNormOnCube Q a u.toH1) := by
        rw [localSymmetricEnergyENorm_eq_ofReal_h1EnergyNormOnCube]
        change ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ))) *
            ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube Q a u.toH1) = _
        rw [ENNReal.ofReal_mul (by positivity :
          (0 : ℝ) ≤ ((((3 ^ d) ^ N : ℕ) : ℝ)))]
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity)
      (by exact Real.sqrt_nonneg _))).1 henn

end

end HighContrast
end HCPolySupport

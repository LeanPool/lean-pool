/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.WitnessZeroTraceAtCube

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.WindowedFrozenWitnessPrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The frozen-witness price with an arbitrary law-free coarse-graining window

An earlier form carried `𝓔 ≤ 1` as a binder.  The upstream ellipticity control
`inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one` holds
for **any** value of `𝓔`, so a law-free bound `𝓔 ≤ Cwit` suffices and only
replaces the window `4d` by `2d(Cwit² + 1)`.

This file re-threads the whole chain with that window as a parameter:
ellipticity → cube energy norm → cube price → translated-cube price →
frozen-witness price.  Setting `Cwit = 1` recovers the unit-energy constants.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03 MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The windowed coarse ellipticity -/

/-- The coarse-graining window produced by a weak-error bound `Cwit`. -/
@[expose]
def ellipticityWindow (d : ℕ) (Cwit : ℝ) : ℝ := 2 * (d : ℝ) * (Cwit ^ 2 + 1)

theorem ellipticityWindow_nonneg (d : ℕ) (Cwit : ℝ) :
    0 ≤ ellipticityWindow d Cwit := by
  unfold ellipticityWindow
  have h : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ Cwit ^ 2 + 1 := by positivity
  positivity

/-- **The windowed ellipticity bound.** -/
theorem lambdaSq_finite_two_le_of_identityError_le [NeZero d]
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) {s Cwit : ℝ}
    (hs : 0 < s) (_hCwit : 0 ≤ Cwit)
    (herr : Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
      (1 : Mat d) ≤ Cwit) :
    Book.Ch02.LambdaSq Q s (.finite 2) a ≤ ellipticityWindow d Cwit := by
  have hbase :=
    Book.Ch02.inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      Q a hs (by norm_num : (0 : ℝ) < 1)
  rw [scalarMatrix_one_eq_one, inv_one, one_mul, Fintype.card_fin] at hbase
  have hnonneg :=
    homogenizationErrorOnCube_infinity_two_nonneg Q s a (1 : Mat d)
  have hsq :
      Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (1 : Mat d) ^ 2 ≤ Cwit ^ 2 :=
    pow_le_pow_left₀ hnonneg herr 2
  refine hbase.trans ?_
  have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
  unfold ellipticityWindow
  exact mul_le_mul_of_nonneg_left (by linarith only [hsq])
    (by linarith only [hd])

/-- The windowed upper coarse ellipticity factor. -/
theorem poincareUpperEllipticityFactor_le_of_identityError_le [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) {s Cwit : ℝ} (hs : 0 < s)
    (hCwit : 0 ≤ Cwit)
    (herr : Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
      (1 : Mat d) ≤ Cwit) :
    poincareUpperEllipticityFactor Q a s (.finite 2) ≤
      Real.rpow (ellipticityWindow d Cwit) (1 / 2 : ℝ) := by
  unfold poincareUpperEllipticityFactor
  exact Real.rpow_le_rpow
    (Book.Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num))
    (lambdaSq_finite_two_le_of_identityError_le Q a hs hCwit herr)
    (by norm_num)

/-! ## The windowed constants -/

/-- The windowed law-free cube constant. -/
@[expose]
def lawFreeCubeEnergyConstantW (C : ℝ) (d : ℕ) (s Cwit : ℝ) : ℝ :=
  (C * Real.rpow s (-(1 / 2 : ℝ)) *
    Real.rpow (ellipticityWindow d Cwit) (1 / 2 : ℝ)) ^ 2

theorem lawFreeCubeEnergyConstantW_nonneg (C : ℝ) (d : ℕ) (s Cwit : ℝ) :
    0 ≤ lawFreeCubeEnergyConstantW C d s Cwit := by
  unfold lawFreeCubeEnergyConstantW
  positivity

/-- The windowed cube price. -/
@[expose]
def gaugeCubeEnergyPriceW (C : ℝ) (d : ℕ) (s Cwit ell : ℝ) : ℝ :=
  lawFreeCubeEnergyConstantW C d s Cwit *
    (BufferToCell.positiveBesovContinuousComparisonConstant d *
      ell ^ (2 * s))

/-- **The windowed frozen-witness price.**  `Klawfree(d,s,Cwit)` times the
eccentricity power `d + 2s`. -/
@[expose]
def gaugeWitnessEnergyPriceW (C : ℝ) (d : ℕ) (s Cwit : ℝ) (abar : Mat d) : ℝ :=
  lawFreeCubeEnergyConstantW C d s Cwit *
      BufferToCell.positiveBesovContinuousComparisonConstant d *
    (gaugeFrameConstant d s *
      witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s))

/-! ## The windowed chain -/

/-- The windowed un-squared cube energy bound. -/
theorem exists_windowedDirichletCubeEnergyNormBound (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (a : CoeffFamily d) (s Cwit : ℝ)
        (v : DirichletForcedCubeSolution Q a (0 : Vec d → Vec d)),
        0 < s → s < 1 → 0 ≤ Cwit →
        ForceBesovRegularity Q s (dirichletBoundaryGradientField v) →
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
            (1 : Mat d) ≤ Cwit →
          dirichletForcedSolutionEnergyNorm Q a v ≤
            C * Real.rpow s (-(1 / 2 : ℝ)) *
                Real.rpow (ellipticityWindow d Cwit) (1 / 2 : ℝ) *
              scaleNormalizedPositiveBesovVectorNormTwo Q s
                (dirichletBoundaryGradientField v) := by
  obtain ⟨C, hCpos, hdir, -⟩ :=
    (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro Q a s Cwit v hs hs1 hCwit hboundary herr
  have hbase := hdir (Q := Q) (a := a) (s := s) (g := (0 : Vec d → Vec d)) v
    hs hs1 (forceBesovRegularity_zero Q s) hboundary
  have hRHS :
      dirichletEnergyWithRHSRHS C Q a s (0 : Vec d → Vec d) v =
        C * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v) := by
    unfold dirichletEnergyWithRHSRHS
    simp only [scaleNormalizedPositiveBesovVectorSeminormTwo,
      cubeBesovPositiveVectorSeminormTwo_zero, mul_zero, zero_add]
  rw [hRHS] at hbase
  have hnormNonneg :
      0 ≤ scaleNormalizedPositiveBesovVectorNormTwo Q s
        (dirichletBoundaryGradientField v) := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        hboundary)
  have hprefNonneg : 0 ≤ C * Real.rpow s (-(1 / 2 : ℝ)) := by
    have := Real.rpow_nonneg hs.le (-(1 / 2 : ℝ))
    positivity
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (poincareUpperEllipticityFactor_le_of_identityError_le Q a hs hCwit herr)
      hprefNonneg)
    hnormNonneg

/-- The windowed price on a translate of a triadic cube. -/
theorem exists_windowedPriceAtTranslatedCubeWitness (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (z : Vec d) (a : CoeffFamily d) (s Cwit : ℝ)
        (v : DirichletForcedCubeSolution Q a (0 : Vec d → Vec d))
        (bTrans : CoeffField d) (uGrad FTrans : Vec d → Vec d),
        0 < s → s < 1 → 0 ≤ Cwit →
        ForceBesovRegularity Q s (dirichletBoundaryGradientField v) →
        MemVectorL2 (openCubeSet Q) (dirichletBoundaryGradientField v) →
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a
            (1 : Mat d) ≤ Cwit →
        (∀ y, bTrans (y + z) = ((a.coeffOn Q).toCoeffField) y) →
        (∀ y, uGrad (y + z) = v.toH1.grad y) →
        (∀ y, FTrans (y + z) = dirichletBoundaryGradientField v y) →
          0 ≤ gaugeCubeEnergyPriceW C d s Cwit (cubeScaleFactor Q) ∧
            eVolumeAverage (translateSet z (openCubeSet Q)) (fun x =>
                ENNReal.ofReal
                  (coefficientEnergyDensity bTrans uGrad x)) ≤
              ENNReal.ofReal
                  (gaugeCubeEnergyPriceW C d s Cwit (cubeScaleFactor Q)) *
                hsNormSq (translateSet z (openCubeSet Q)) s FTrans := by
  obtain ⟨C, hCpos, hbound⟩ := exists_windowedDirichletCubeEnergyNormBound d
  refine ⟨C, hCpos, ?_⟩
  intro Q z a s Cwit v bTrans uGrad FTrans hs hs1 hCwit hboundary hL2 herr
    hb hu hF
  have hell : 0 < cubeScaleFactor Q := by
    unfold cubeScaleFactor
    positivity
  have hbesovNonneg :
      0 ≤ BufferToCell.positiveBesovContinuousComparisonConstant d :=
    (BufferToCell.positiveBesovContinuousComparisonConstant_pos d).le
  have hellPowPos : 0 < cubeScaleFactor Q ^ (2 * s) :=
    Real.rpow_pos_of_pos hell _
  have hKnonneg : 0 ≤ gaugeCubeEnergyPriceW C d s Cwit (cubeScaleFactor Q) := by
    unfold gaugeCubeEnergyPriceW
    have h1 : 0 ≤ lawFreeCubeEnergyConstantW C d s Cwit :=
      lawFreeCubeEnergyConstantW_nonneg C d s Cwit
    positivity
  refine ⟨hKnonneg, ?_⟩
  set F : Vec d → Vec d := dirichletBoundaryGradientField v with hFdef
  set N : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q s F with hNdef
  set pref : ℝ :=
    C * Real.rpow s (-(1 / 2 : ℝ)) *
      Real.rpow (ellipticityWindow d Cwit) (1 / 2 : ℝ) with hprefDef
  have hprefNonneg : 0 ≤ pref := by
    rw [hprefDef]
    have h1 : 0 ≤ Real.rpow s (-(1 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
    have h2 : 0 ≤ Real.rpow (ellipticityWindow d Cwit) (1 / 2 : ℝ) :=
      rpow_half_nonneg _
    positivity
  have hEnergy := hbound Q a s Cwit v hs hs1 hCwit hboundary herr
  have hNnonneg : 0 ≤ N := by
    rw [hNdef]
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        hboundary)
  -- the extended-real left-hand side, after the translation transport
  have hLHS :
      eVolumeAverage (translateSet z (openCubeSet Q)) (fun x =>
          ENNReal.ofReal (coefficientEnergyDensity bTrans uGrad x)) =
        ENNReal.ofReal (h1EnergyNormOnCube Q a v.toH1) ^ (2 : ℕ) := by
    rw [eVolumeAverage_coefficientEnergyDensity_translateSet,
      ← eVolumeAverage_coefficientEnergyDensity_eq Q a v.toH1]
    refine congrArg (eVolumeAverage (openCubeSet Q)) ?_
    funext y
    refine congrArg ENNReal.ofReal ?_
    unfold coefficientEnergyDensity
    simp only [hb, hu]
  have hEnergyNorm :
      ENNReal.ofReal (h1EnergyNormOnCube Q a v.toH1) ≤
        ENNReal.ofReal (pref * N) :=
    ENNReal.ofReal_le_ofReal hEnergy
  have hstep1 :
      eVolumeAverage (translateSet z (openCubeSet Q)) (fun x =>
          ENNReal.ofReal (coefficientEnergyDensity bTrans uGrad x)) ≤
        ENNReal.ofReal (pref * N) ^ (2 : ℕ) := by
    rw [hLHS]
    exact pow_le_pow_left' hEnergyNorm 2
  have hRHSeq :
      hsNormSq (translateSet z (openCubeSet Q)) s FTrans =
        hsNormSq (openCubeSet Q) s F := by
    rw [hsNormSq_translateSet_add]
    refine congrArg (hsNormSq (openCubeSet Q) s) ?_
    funext y
    exact hF y
  have hBesovBound :
      ENNReal.ofReal N ^ (2 : ℕ) ≤
        ENNReal.ofReal
            (BufferToCell.positiveBesovContinuousComparisonConstant d) *
          ENNReal.ofReal ((cubeScaleFactor Q) ^ (2 * s)) *
            hsNormSq (openCubeSet Q) s F :=
    BufferToCell.positiveBesovNorm_sq_le_continuousFractionalSquare
      Q ⟨s, hs, hs1⟩ F hboundary hL2
  have hsplit :
      ENNReal.ofReal (pref * N) ^ (2 : ℕ) =
        ENNReal.ofReal pref ^ (2 : ℕ) * ENNReal.ofReal N ^ (2 : ℕ) := by
    rw [ENNReal.ofReal_mul hprefNonneg, mul_pow]
  have hconst :
      ENNReal.ofReal pref ^ (2 : ℕ) *
          (ENNReal.ofReal
              (BufferToCell.positiveBesovContinuousComparisonConstant d) *
            ENNReal.ofReal ((cubeScaleFactor Q) ^ (2 * s))) =
        ENNReal.ofReal (gaugeCubeEnergyPriceW C d s Cwit (cubeScaleFactor Q)) := by
    have hpref2 : 0 ≤ pref ^ 2 := pow_nonneg hprefNonneg 2
    rw [← ENNReal.ofReal_pow hprefNonneg, ← ENNReal.ofReal_mul hbesovNonneg,
      ← ENNReal.ofReal_mul hpref2]
    exact congrArg ENNReal.ofReal rfl
  rw [hRHSeq]
  calc
    eVolumeAverage (translateSet z (openCubeSet Q)) (fun x =>
        ENNReal.ofReal (coefficientEnergyDensity bTrans uGrad x)) ≤
        ENNReal.ofReal (pref * N) ^ (2 : ℕ) := hstep1
    _ = ENNReal.ofReal pref ^ (2 : ℕ) * ENNReal.ofReal N ^ (2 : ℕ) := hsplit
    _ ≤ ENNReal.ofReal pref ^ (2 : ℕ) *
          (ENNReal.ofReal
              (BufferToCell.positiveBesovContinuousComparisonConstant d) *
            ENNReal.ofReal ((cubeScaleFactor Q) ^ (2 * s)) *
              hsNormSq (openCubeSet Q) s F) :=
      mul_le_mul' (le_refl _) hBesovBound
    _ = (ENNReal.ofReal pref ^ (2 : ℕ) *
          (ENNReal.ofReal
              (BufferToCell.positiveBesovContinuousComparisonConstant d) *
            ENNReal.ofReal ((cubeScaleFactor Q) ^ (2 * s)))) *
              hsNormSq (openCubeSet Q) s F := by ring
    _ = ENNReal.ofReal (gaugeCubeEnergyPriceW C d s Cwit (cubeScaleFactor Q)) *
          hsNormSq (openCubeSet Q) s F := by rw [hconst]

/-- **The windowed capstone price at the frozen witness.** -/
theorem exists_windowedGaugePhysicalEnergyPriceAtFrozenWitness
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (abar : Mat d) (_hS : (symmPart abar).PosDef)
        (U : Set (Vec d)) (j : ℤ) (z : Vec d) (s Cwit : ℝ)
        (aFam : CoeffFamily d)
        (v : DirichletForcedCubeSolution (originCube d j) aFam
          (0 : Vec d → Vec d))
        (aHat : CoeffField d)
        (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U))
        (g0grad FTrans : Vec d → Vec d),
        0 < s → s < 1 / 2 → 0 ≤ Cwit →
        U = (fun x : Vec d =>
              z + matVecMul (matSqrt (symmPart abar)) x) ''
            openCubeSet (originCube d j) →
        U ⊆ ellipsoid abar 1 →
        ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
        ForceBesovRegularity (originCube d j) s
          (dirichletBoundaryGradientField v) →
        MemVectorL2 (openCubeSet (originCube d j))
          (dirichletBoundaryGradientField v) →
        Book.Ch02.HomogenizationErrorOnCube (originCube d j) s .infinity
            (.finite 2) aFam (1 : Mat d) ≤ Cwit →
        (∀ y, aHat (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
          ((aFam.coeffOn (originCube d j)).toCoeffField) y) →
        (∀ y, uHat.grad (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
          v.toH1.grad y) →
        (∀ y, FTrans (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
          dirichletBoundaryGradientField v y) →
        (∀ x, FTrans (matVecMul (matSqrt (symmPart abar))⁻¹ x) =
          matVecMul (matSqrt (symmPart abar)) (g0grad x)) →
          RowSupply.GaugePhysicalEnergyPriceAtWitness
            (matImage (matSqrt (symmPart abar))⁻¹ U) aHat uHat
            (gaugeWitnessEnergyPriceW C d s Cwit abar)
            (hsNormSq U s
              (fun x => matVecMul (matSqrt (symmPart abar)) (g0grad x))) := by
  obtain ⟨C, hCpos, hprice⟩ := exists_windowedPriceAtTranslatedCubeWitness d
  refine ⟨C, hCpos, ?_⟩
  intro abar hS U j z s Cwit aFam v aHat uHat g0grad FTrans hs hsHalf hCwit hU
    hOuter hInner hBesov hL2 herr hb hu hF hFrame
  classical
  have hu' : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hLinv : IsUnit ((matSqrt (symmPart abar))⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det _ hu'
  have hgauge : matImage (matSqrt (symmPart abar))⁻¹ U =
      translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
        (openCubeSet (originCube d j)) := by
    rw [hU]
    exact RowSupply.matImage_inv_affineImage hu' z _
  have hUopen : IsOpen U := by
    rw [hU]
    exact RowSupply.isOpen_affineImage hu' z (isOpen_openCubeSet _)
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hrpos : (0 : ℝ) < 1 / (3 * Real.sqrt (d : ℝ)) := by
    have hd : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hsq : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd
    positivity
  have hU0 : volume U ≠ 0 := by
    have hpos : 0 < volume (ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ)))) :=
      volume_ellipsoid_pos abar hrpos
    exact (lt_of_lt_of_le hpos (measure_mono hInner)).ne'
  obtain ⟨hKnonneg, hstep1⟩ :=
    hprice (originCube d j) (matVecMul (matSqrt (symmPart abar))⁻¹ z) aFam s
      Cwit v aHat uHat.grad FTrans hs (hsHalf.trans (by norm_num)) hCwit
      hBesov hL2 herr hb hu hF
  have hframe :
      hsNormSq (matImage (matSqrt (symmPart abar))⁻¹ U) s FTrans ≤
        ENNReal.ofReal
            (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
              ‖matSqrt (symmPart abar)‖) *
          hsNormSq U s
            (fun x => matVecMul (matSqrt (symmPart abar)) (g0grad x)) := by
    have hbase := hsNormSq_matImage_le_opNorm
      (L := (matSqrt (symmPart abar))⁻¹) hLinv hUmeas hU0 (s := s) (by
        have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
        linarith only [hd, hs]) FTrans
    rw [Matrix.nonsing_inv_nonsing_inv _ hu'] at hbase
    have hfun :
        (fun y : Vec d => FTrans (matVecMul (matSqrt (symmPart abar))⁻¹ y)) =
          fun x : Vec d => matVecMul (matSqrt (symmPart abar)) (g0grad x) := by
      funext x
      exact hFrame x
    rwa [hfun] at hbase
  have hell : cubeScaleFactor (originCube d j) ≤
      2 * ‖(matSqrt (symmPart abar))⁻¹‖ :=
    witnessCubeSide_le_two_mul_norm_inv_matSqrt hS hU hOuter
  have hellNonneg : (0 : ℝ) ≤ cubeScaleFactor (originCube d j) := by
    unfold cubeScaleFactor
    positivity
  have hfr :
      hsAffineFactor (matSqrt (symmPart abar))⁻¹ s ‖matSqrt (symmPart abar)‖ *
          cubeScaleFactor (originCube d j) ^ (2 * s) ≤
        gaugeFrameConstant d s *
          witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) :=
    hsAffineFactor_mul_cubeSide_le_witnessEccentricity_rpow hS hs hsHalf
      hellNonneg hell
  have hbaseNonneg :
      (0 : ℝ) ≤ lawFreeCubeEnergyConstantW C d s Cwit *
        BufferToCell.positiveBesovContinuousComparisonConstant d :=
    mul_nonneg (lawFreeCubeEnergyConstantW_nonneg C d s Cwit)
      (BufferToCell.positiveBesovContinuousComparisonConstant_pos d).le
  have hconst :
      gaugeCubeEnergyPriceW C d s Cwit (cubeScaleFactor (originCube d j)) *
          hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
            ‖matSqrt (symmPart abar)‖ ≤
        gaugeWitnessEnergyPriceW C d s Cwit abar := by
    unfold gaugeCubeEnergyPriceW gaugeWitnessEnergyPriceW
    have hrw :
        lawFreeCubeEnergyConstantW C d s Cwit *
              (BufferToCell.positiveBesovContinuousComparisonConstant d *
                cubeScaleFactor (originCube d j) ^ (2 * s)) *
            hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
              ‖matSqrt (symmPart abar)‖ =
          (lawFreeCubeEnergyConstantW C d s Cwit *
              BufferToCell.positiveBesovContinuousComparisonConstant d) *
            (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
                ‖matSqrt (symmPart abar)‖ *
              cubeScaleFactor (originCube d j) ^ (2 * s)) := by
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hfr hbaseNonneg
  have hKfinal : (0 : ℝ) ≤ gaugeWitnessEnergyPriceW C d s Cwit abar := by
    unfold gaugeWitnessEnergyPriceW
    have h1 : (0 : ℝ) ≤ gaugeFrameConstant d s := gaugeFrameConstant_nonneg d s
    have h2 : (0 : ℝ) ≤
        witnessEccentricity (symmPart abar) ^ ((d : ℝ) + 2 * s) := by
      refine Real.rpow_nonneg ?_ _
      unfold witnessEccentricity
      exact Real.sqrt_nonneg _
    exact mul_nonneg hbaseNonneg (mul_nonneg h1 h2)
  refine ⟨hKfinal, ?_⟩
  rw [← hgauge] at hstep1
  calc
    eVolumeAverage (matImage (matSqrt (symmPart abar))⁻¹ U) (fun x =>
        ENNReal.ofReal (coefficientEnergyDensity aHat uHat.grad x)) ≤
        ENNReal.ofReal
            (gaugeCubeEnergyPriceW C d s Cwit
              (cubeScaleFactor (originCube d j))) *
          hsNormSq (matImage (matSqrt (symmPart abar))⁻¹ U) s FTrans := hstep1
    _ ≤ ENNReal.ofReal
            (gaugeCubeEnergyPriceW C d s Cwit
              (cubeScaleFactor (originCube d j))) *
          (ENNReal.ofReal
              (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
                ‖matSqrt (symmPart abar)‖) *
            hsNormSq U s
              (fun x => matVecMul (matSqrt (symmPart abar)) (g0grad x))) :=
      mul_le_mul' (le_refl _) hframe
    _ = ENNReal.ofReal
          (gaugeCubeEnergyPriceW C d s Cwit
              (cubeScaleFactor (originCube d j)) *
            hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
              ‖matSqrt (symmPart abar)‖) *
          hsNormSq U s
            (fun x => matVecMul (matSqrt (symmPart abar)) (g0grad x)) := by
      rw [ENNReal.ofReal_mul hKnonneg, mul_assoc]
    _ ≤ ENNReal.ofReal (gaugeWitnessEnergyPriceW C d s Cwit abar) *
          hsNormSq U s
            (fun x => matVecMul (matSqrt (symmPart abar)) (g0grad x)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) (le_refl _)

end

end EnergyPrice
end HighContrast
end HCPolySupport

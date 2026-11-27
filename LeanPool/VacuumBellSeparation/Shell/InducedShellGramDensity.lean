/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCoordinates

/-!
# The actual six-dimensional Euclidean Gram density

The density is sqrt(det Gram) of the six real derivative columns in
the eight-dimensional Euclidean ambient space. Its equality with the
pinned norm determinant supplies the actual Hausdorff scaling theorem
for each tangent linear map. A nonlinear area formula is separate.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

/-- Shell real orthonormal basis. -/
noncomputable def shellRealOrthonormalBasis :
    OrthonormalBasis (Fin 6) ℝ ShellEuclideanDomain :=
  (stdOrthonormalBasis ℝ ShellEuclideanDomain).reindex
    (finCongr shellEuclideanDomain_real_finrank)

/-- Shell derivative gram defined as `Matrix.gram ℝ (fun i => A (shellRealOrthonormalBasis i))`. -/
noncomputable def shellDerivativeGram
    (A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.gram ℝ (fun i => A (shellRealOrthonormalBasis i))

/-- Shell derivative density defined as `Real.sqrt (shellDerivativeGram A).det`. -/
noncomputable def shellDerivativeDensity
    (A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient) : ℝ :=
  Real.sqrt (shellDerivativeGram A).det

theorem shellDerivativeGram_posDef
    {A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient} (hA : Function.Injective A) :
    (shellDerivativeGram A).PosDef :=
  Matrix.posDef_gram_of_linearIndependent
    (shellRealOrthonormalBasis.toBasis.linearIndependent.map' A.toLinearMap
      (LinearMap.ker_eq_bot.mpr hA))

theorem shellDerivativeDensity_nonneg
    (A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient) : 0 ≤ shellDerivativeDensity A :=
  Real.sqrt_nonneg _

theorem shellDerivativeDensity_pos
    {A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient} (hA : Function.Injective A) :
    0 < shellDerivativeDensity A :=
  Real.sqrt_pos.2 (shellDerivativeGram_posDef hA).det_pos

theorem shellDerivativeDensity_eq_normDet
    (A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient) :
    shellDerivativeDensity A = A.toLinearMap.normDet := by
  have h : A.toLinearMap.normDet ^ 2 = (shellDerivativeGram A).det :=
    A.toLinearMap.normDet_sq_eq_det_gram shellRealOrthonormalBasis
  rw [shellDerivativeDensity, ← h, Real.sqrt_sq A.toLinearMap.normDet_nonneg]

theorem continuous_shellDerivativeGram : Continuous shellDerivativeGram := by
  unfold shellDerivativeGram
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient =>
    inner ℝ (A (shellRealOrthonormalBasis i)) (A (shellRealOrthonormalBasis j)))
  fun_prop

theorem continuous_shellDerivativeDensity : Continuous shellDerivativeDensity :=
  continuous_shellDerivativeGram.matrix_det.sqrt

/-- Actual Euclidean six-dimensional Hausdorff scaling of every tangent
linear map, with the domain's genuine Euclidean Lebesgue measure. -/
theorem shellDerivative_euclideanHausdorff_image
    (A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient) (s : Set ShellEuclideanDomain) :
    (Measure.euclideanHausdorffMeasure 6 : Measure ShellEuclideanAmbient) (A '' s) =
      ENNReal.ofReal (shellDerivativeDensity A) * volume s := by
  have h := A.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
  simpa only [shellEuclideanDomain_real_finrank, shellDerivativeDensity_eq_normDet,
    ContinuousLinearMap.coe_coe] using h

/-- Induced shell chart gram defined as `shellDerivativeGram (fderiv ℝ (euclideanLorentzShellChart
m Λ) w)`. -/
noncomputable def inducedShellChartGram (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (w : ShellEuclideanDomain) : Matrix (Fin 6) (Fin 6) ℝ :=
  shellDerivativeGram (fderiv ℝ (euclideanLorentzShellChart m Λ) w)

/-- Induced shell chart density defined as `shellDerivativeDensity (fderiv ℝ
(euclideanLorentzShellChart m Λ) w)`. -/
noncomputable def inducedShellChartDensity (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (w : ShellEuclideanDomain) : ℝ :=
  shellDerivativeDensity (fderiv ℝ (euclideanLorentzShellChart m Λ) w)

theorem inducedShellChartGram_posDef {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    {w : ShellEuclideanDomain} (hw : w ∈ euclideanShellChartDomain m) :
    (inducedShellChartGram m Λ w).PosDef :=
  shellDerivativeGram_posDef (euclideanLorentzShellChart_real_derivative_injective Λ hw)

theorem inducedShellChartDensity_pos {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    {w : ShellEuclideanDomain} (hw : w ∈ euclideanShellChartDomain m) :
    0 < inducedShellChartDensity m Λ w :=
  shellDerivativeDensity_pos (euclideanLorentzShellChart_real_derivative_injective Λ hw)

theorem inducedShellChart_tangent_volume {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (w : ShellEuclideanDomain) (s : Set ShellEuclideanDomain) :
    (Measure.euclideanHausdorffMeasure 6 : Measure ShellEuclideanAmbient)
        ((fderiv ℝ (euclideanLorentzShellChart m Λ) w) '' s) =
      ENNReal.ofReal (inducedShellChartDensity m Λ w) * volume s :=
  shellDerivative_euclideanHausdorff_image _ _

end VacuumBellSeparation

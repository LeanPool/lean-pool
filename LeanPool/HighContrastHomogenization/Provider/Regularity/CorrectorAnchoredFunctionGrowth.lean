/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAnchoredMeanGrowth
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorAnchoredFunctionGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale-linear centered-cube growth of anchored correctors

The normalized `L²` norm is split into its fluctuation and mean.  The
oscillation is supplied by the caller, while the anchored telescope controls the
mean.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A scale-linear normalized oscillation bound above a threshold gives a
scale-linear normalized `L²` bound for the global value representative on
the centered exhaustion cubes. -/
theorem
  NormalizedLocalH1Carrier.exists_globalRepresentativeLpBound_of_oscillation
    {d : ℕ} (z : NormalizedLocalH1Carrier d)
    (q₀ : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hosc : ∀ q : ℕ, q₀ ≤ q →
      cubeBesovOscillation (originCube d (q : ℤ)) (2 : ℝ≥0∞)
          (z.localH1Function q).toFun ≤ M * (3 : ℝ) ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) (2 : ℝ≥0∞)
          z.globalValueRepresentative ≤ C * (3 : ℝ) ^ q := by
  obtain ⟨A, hA, hmean⟩ :=
    z.exists_abs_cubeAverage_le_three_pow_of_oscillation_bound q₀ M hM hosc
  let C : ℝ := M + A
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hM hA
  refine ⟨C, hC, ?_⟩
  intro q hq
  let Q : TriadicCube d := originCube d (q : ℤ)
  let u : H1Function (openCubeSet Q) := z.localH1Function q
  have haeVolume : z.globalValueRepresentative
      =ᵐ[volumeMeasureOn (openCubeSet Q)] u.toFun := by
    simpa only [Q, u, localGradientCube] using
      z.globalValueRepresentative_ae_eq_localH1Function q
  have haeNormalized : z.globalValueRepresentative
      =ᵐ[normalizedCubeMeasure Q] u.toFun := by
    simpa only [Filter.EventuallyEq, volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      Measure.ae_smul_measure haeVolume
        (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hnormEq :
      cubeLpNorm Q (2 : ℝ≥0∞) z.globalValueRepresentative =
        cubeLpNorm Q (2 : ℝ≥0∞) u.toFun := by
    unfold cubeLpNorm
    rw [eLpNorm_congr_ae haeNormalized]
  have hmeanEq : cubeAverage Q z.globalValueRepresentative =
      cubeAverage Q u.toFun := by
    simpa only [Q, u] using
      z.cubeAverage_globalValueRepresentative_eq_localH1Function q
  have hsplit :=
    Book.Ch03.cubeLpNorm_two_le_cubeLpNorm_fluctuation_add_norm_cubeAverage
      Q u.toFun u.memL2_normalizedCubeMeasure
  have hoscq :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) ≤
        M * (3 : ℝ) ^ q := by
    simpa only [Q, u, cubeBesovOscillation] using hosc q hq
  have hmeanq : ‖cubeAverage Q u.toFun‖ ≤ A * (3 : ℝ) ^ q := by
    rw [← hmeanEq, Real.norm_eq_abs]
    simpa only [Q] using hmean q hq
  rw [hnormEq]
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) u.toFun ≤
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) +
          ‖cubeAverage Q u.toFun‖ := hsplit
    _ ≤ M * (3 : ℝ) ^ q + A * (3 : ℝ) ^ q := add_le_add hoscq hmeanq
    _ = C * (3 : ℝ) ^ q := by
      dsimp only [C]
      ring

end

end HighContrast
end HCPolySupport

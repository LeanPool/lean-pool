/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AELimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffFrobeniusMass
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpSquared
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# CutoffFrobeniusMassTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform tail of the per-cube cutoff Frobenius mass

This module specializes the translated stream-increment estimate to `p = 2`
and to the finite lower tail `(m - (q + 1), m]`.  The elementary entrywise
comparison between Frobenius and operator norms prices the finite per-cube
mass by `d^2` times that increment mass.  The closed formula
`streamPointScale_sq` then removes the lower endpoint from the amplitude, and
the one-sided almost-everywhere limit theorem passes the same bound to the
genuine cutoff.

## Source and correction

* ABK26, `e.kmn.bounds`, label and display, gives the stream-increment
  estimate for every origin-cube scale `l`, assuming only `n < m`.  The proved
  translation theorem carries that all-`l` statement to every translated
  triadic cube `Q`; this is the source authority for the arbitrary-`Q` theorem
  below.
* ABK26, records the finite-lower-cutoff passage and related increment estimates
  used by the specialization.
* ABK26, supplies the volume-normalized squared Frobenius expansion and
  estimates.  Its restricted scale ranges support the Frobenius calculation
  but are not authority for the arbitrary-`Q` scope.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- A dimension-only amplitude for finite and genuine cutoff Frobenius masses. -/
noncomputable def cutoffFrobeniusMassFiniteConst (d : ℕ) : ℝ :=
  1 +
    2 * Real.exp 1 * (d : ℝ) ^ 2 *
      (IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 *
        (d : ℝ) ^ 2 * geometricConcentrationConst) ^ 2

/-- The dimension-only cutoff Frobenius-mass amplitude is strictly positive. -/
theorem cutoffFrobeniusMassFiniteConst_pos (d : ℕ) :
    0 < cutoffFrobeniusMassFiniteConst d := by
  rw [cutoffFrobeniusMassFiniteConst]
  exact add_pos_of_pos_of_nonneg zero_lt_one (by positivity)

private theorem average_cubeDomain_eq_cubeAverage
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    Book.Ch02.average (Book.Ch02.cubeDomain Q) f = cubeAverage Q f := by
  rw [Book.Ch02.average, Book.Ch02.cubeDomain_coe, cubeAverage,
    volume_openCubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]

private theorem finiteLowerCutoffFrobeniusMass_le_operatorMass
    (Q : TriadicCube d) (m : ℤ) (q : ℕ) (omega : CutoffSample d) :
    finiteLowerCutoffFrobeniusMass Q m (q + 1) omega ≤
      (d : ℝ) ^ 2 * cubeAverage Q
        (streamIncrementLpDensity 2
          (m - (((q + 1 : ℕ) : ℤ))) m omega.1) := by
  rw [finiteLowerCutoffFrobeniusMass, average_cubeDomain_eq_cubeAverage]
  have hleft : IntegrableOn
      (fun x : Vec d => matrixFrobeniusNormSq
        (finiteLowerCutoff m (q + 1) omega.1 x)) (cubeSet Q) volume := by
    change IntegrableOn
      (fun x : Vec d => matrixFrobeniusNormSq
        (finiteShellIncrement omega.1 (m - (((q + 1 : ℕ) : ℤ))) m x))
      (cubeSet Q) volume
    exact (continuous_frobeniusMass_finiteShellIncrement
      (m - (((q + 1 : ℕ) : ℤ))) m omega.1).continuousOn.integrableOn_compact
        (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)) |>.mono_set
          (cubeSet_subset_closedBall Q)
  have hright : IntegrableOn
      (fun x : Vec d => (d : ℝ) ^ 2 *
        streamIncrementLpDensity 2
          (m - (((q + 1 : ℕ) : ℤ))) m omega.1 x) (cubeSet Q) volume :=
    (integrableOn_cubeSet_streamIncrementLpDensity (by norm_num) Q
      (m - (((q + 1 : ℕ) : ℤ))) m omega.1).const_mul _
  have hint :
      ∫ x in cubeSet Q,
          matrixFrobeniusNormSq (finiteLowerCutoff m (q + 1) omega.1 x) ∂volume ≤
        ∫ x in cubeSet Q, (d : ℝ) ^ 2 *
          streamIncrementLpDensity 2
            (m - (((q + 1 : ℕ) : ℤ))) m omega.1 x ∂volume := by
    refine setIntegral_mono_on hleft hright (measurableSet_cubeSet Q) fun x _ => ?_
    have hfro := matrixFrobeniusNormSq_le_of_abs_entry_le
      (A := finiteShellIncrement omega.1
        (m - (((q + 1 : ℕ) : ℤ))) m x)
      (fun i j => Book.Ch02.abs_entry_le_matrixOperatorNorm _ i j)
    simpa only [finiteLowerCutoff, streamIncrementLpDensity, Real.rpow_two] using hfro
  unfold cubeAverage
  calc
    (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q,
            matrixFrobeniusNormSq (finiteLowerCutoff m (q + 1) omega.1 x) ∂volume
        ≤ (cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, (d : ℝ) ^ 2 *
            streamIncrementLpDensity 2
              (m - (((q + 1 : ℕ) : ℤ))) m omega.1 x ∂volume :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (cubeVolume_pos Q).le)
    _ = (d : ℝ) ^ 2 * ((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q,
            streamIncrementLpDensity 2
              (m - (((q + 1 : ℕ) : ℤ))) m omega.1 x ∂volume) := by
      rw [integral_const_mul]
      ring

private theorem mul_streamIncrementLpMassScale_two_le
    (M : ABKModel d) (m : ℤ) (q : ℕ) :
    (d : ℝ) ^ 2 * streamIncrementLpMassScale M 2
        (m - (((q + 1 : ℕ) : ℤ))) m ≤
      cutoffFrobeniusMassFiniteConst d * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := by
  let n : ℤ := m - (((q + 1 : ℕ) : ℤ))
  let R : ℝ :=
    2 * Real.exp 1 * (d : ℝ) ^ 2 *
      (IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 *
        (d : ℝ) ^ 2 * geometricConcentrationConst) ^ 2
  have hnm : n < m := by
    dsimp [n]
    omega
  have hmin : min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) ≤ M.gamma⁻¹ :=
    min_le_left _ _
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have htail_nonneg :
      0 ≤ M.gamma⁻¹ * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) :=
    mul_nonneg (inv_nonneg.mpr M.shellPrefix.gamma_pos.le) hpow_nonneg
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hscale :
      (d : ℝ) ^ 2 * streamIncrementLpMassScale M 2 n m =
        R * (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
    rw [streamIncrementLpMassScale, Real.rpow_two, mul_pow,
      streamPointScale_sq M hnm]
    dsimp [R]
    norm_num [Real.rpow_two]
    ring
  change (d : ℝ) ^ 2 * streamIncrementLpMassScale M 2 n m ≤ _
  calc
    (d : ℝ) ^ 2 * streamIncrementLpMassScale M 2 n m =
        R * (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := hscale
    _ ≤ R * (M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hR_nonneg
      exact mul_le_mul_of_nonneg_right hmin hpow_nonneg
    _ ≤ (1 + R) * (M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
      apply mul_le_mul_of_nonneg_right _ htail_nonneg
      exact le_add_of_nonneg_left zero_le_one
    _ = cutoffFrobeniusMassFiniteConst d * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := by
      rw [cutoffFrobeniusMassFiniteConst]
      dsimp [R]
      ring

/-- Every finite lower cutoff has a uniform one-sided `Gamma_1` per-cube
Frobenius-mass tail at the dimension-only amplitude. -/
theorem isBigOWith_gammaSigma_one_finiteLowerCutoffFrobeniusMass
    (M : ABKModel d) (m : ℤ) (q : ℕ) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega : CutoffSample d =>
        finiteLowerCutoffFrobeniusMass Q m (q + 1) omega)
      (cutoffFrobeniusMassFiniteConst d * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
  let n : ℤ := m - (((q + 1 : ℕ) : ℤ))
  have hnm : n < m := by
    dsimp [n]
    omega
  have hop : IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega : CutoffSample d =>
        cubeAverage Q (streamIncrementLpDensity 2 n m omega.1))
      (streamIncrementLpMassScale M 2 n m) := by
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0)] using
      isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity_cutoffLaw
        M (p := 2) (by norm_num) hnm Q
  have hscaled := hop.const_mul (sq_nonneg (d : ℝ))
  have hcomp := hscaled.of_le
    (finiteLowerCutoffFrobeniusMass_le_operatorMass Q m q)
  apply hcomp.mono_scale
  simpa only [n] using mul_streamIncrementLpMassScale_two_le M m q

theorem isBigOWith_gammaSigma_one_cutoffFrobeniusMass
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (cutoffFrobeniusMass Q m)
      (cutoffFrobeniusMassFiniteConst d * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))) := by
  apply Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_of_ae_tendsto_uniform
      (W := fun q omega => finiteLowerCutoffFrobeniusMass Q m (q + 1) omega)
  · exact Filter.Eventually.of_forall fun omega => by
      simpa only using!
        (tendsto_finiteLowerCutoffFrobeniusMass Q m omega).comp
          (Filter.tendsto_add_atTop_nat 1)
  · intro q
    exact isBigOWith_gammaSigma_one_finiteLowerCutoffFrobeniusMass M m q Q

end

end Algsuperdiff.Section3.Provider.Stream

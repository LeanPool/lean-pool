/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffFrobeniusMassMaximum

/-!
# CutoffMassWeightedSum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weighted aggregation of cutoff Frobenius-mass maxima

This module performs the countable scalar aggregation needed by the corrected
Section 3.2 base-case route.  At descendant depth `n`, it weights the genuine
cutoff Frobenius-mass maximum by the `p = infinity`, `q = 2` Chapter 2
geometric weight and by `nu^{-2}`.  The per-depth `Gamma_1` estimates are
combined with the countable generalized triangle inequality, while
`descendantMassFactor` is summed into the adopted `baseLoss d s`.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-- The scalar majorant for the linearly weighted cutoff-mass series. -/
noncomputable def cutoffMassLinearWeightedScale
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) : ℝ :=
  Stream.cutoffFrobeniusMassFiniteConst d *
    (M.nu⁻¹ ^ 2 *
      (M.gamma⁻¹ * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))))) *
    baseLoss d s

/-- The weighted-series scalar majorant is strictly positive. -/
theorem cutoffMassLinearWeightedScale_pos
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    0 < cutoffMassLinearWeightedScale M m s := by
  rw [cutoffMassLinearWeightedScale]
  exact mul_pos
    (mul_pos (Stream.cutoffFrobeniusMassFiniteConst_pos d)
      (mul_pos (pow_pos (inv_pos.mpr M.nu_pos) 2)
        (mul_pos (inv_pos.mpr M.shellPrefix.gamma_pos)
          (Real.rpow_pos_of_pos (by norm_num) _))))
    (baseLoss_pos d s)

/-- The all-depth linearly weighted sum of genuine descendant cutoff-mass
maxima. -/
noncomputable def cutoffMassLinearWeightedSum
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) (omega : CutoffSample d) : ℝ :=
  ∑' n : ℕ, Book.Ch02.geometricWeight (s : ℝ) 2 n *
    (M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega)

/-- The all-depth linearly weighted cutoff-mass sum is nonnegative. -/
theorem cutoffMassLinearWeightedSum_nonneg
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) (omega : CutoffSample d) :
    0 ≤ cutoffMassLinearWeightedSum M Q m s omega := by
  rw [cutoffMassLinearWeightedSum]
  exact tsum_nonneg fun n =>
    mul_nonneg
      (HCPolySupport.geometricWeight_nonneg n
        (mul_nonneg (Set.mem_Ioo.mp s.2).1.le (by norm_num)))
      (mul_nonneg (sq_nonneg _)
        (Stream.cutoffFrobeniusMassMaximum_nonneg Q m n omega))

/-- The linearly weighted all-depth cutoff mass has a one-sided `Gamma_1`
tail at the scalar `baseLoss` majorant. -/
theorem isBigOWith_gammaSigma_one_cutoffMassLinearWeightedSum
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (cutoffMassLinearWeightedSum M Q m s)
      (IndependentSums.gammaTriangleConst 1 *
        cutoffMassLinearWeightedScale M m s) := by
  let A0 : ℝ := Stream.cutoffFrobeniusMassFiniteConst d *
    (M.nu⁻¹ ^ 2 *
      (M.gamma⁻¹ * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))))
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight (s : ℝ) 2 n
  let X : ℕ → CutoffSample d → ℝ := fun n omega =>
    w n * (M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega)
  let a : ℕ → ℝ := fun n => A0 * (w n * descendantMassFactor d n)
  have hs_pos : (0 : ℝ) < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hw_nonneg : ∀ n, 0 ≤ w n := fun n => by
    exact HCPolySupport.geometricWeight_nonneg n
      (mul_nonneg hs_pos.le (by norm_num))
  have hw_pos : ∀ n, 0 < w n := fun n => by
    exact HCPolySupport.geometricWeight_pos n
      (mul_pos hs_pos (by norm_num))
  have hA0_pos : 0 < A0 := by
    dsimp only [A0]
    exact mul_pos (Stream.cutoffFrobeniusMassFiniteConst_pos d)
      (mul_pos (pow_pos (inv_pos.mpr M.nu_pos) 2)
        (mul_pos (inv_pos.mpr M.shellPrefix.gamma_pos)
          (Real.rpow_pos_of_pos (by norm_num) _)))
  have hX_nonneg : ∀ n omega, 0 ≤ X n omega := fun n omega => by
    dsimp only [X]
    exact mul_nonneg (hw_nonneg n)
      (mul_nonneg (sq_nonneg _)
        (Stream.cutoffFrobeniusMassMaximum_nonneg Q m n omega))
  have hX_meas : ∀ n, Measurable (X n) := fun n => by
    dsimp only [X]
    exact
      ((Stream.measurable_cutoffFrobeniusMassMaximum Q m n).const_mul
        (M.nu⁻¹ ^ 2)).const_mul (w n)
  have ha_pos : ∀ n, 0 < a n := fun n => by
    dsimp only [a]
    exact mul_pos hA0_pos
      (mul_pos (hw_pos n) (descendantMassFactor_pos d n))
  have ha_summable : Summable a := by
    exact (summable_geometricWeight_mul_descendantMassFactor d s).mul_left A0
  have hX_tail : ∀ n, IndependentSums.IsBigOWith
      (cutoffSampleLaw M).toMeasure (IndependentSums.gammaSigma 1)
      (X n) (a n) := fun n => by
    have htail :=
      (Stream.isBigOWith_gammaSigma_one_cutoffFrobeniusMassMaximum M m n Q).const_mul
        (mul_nonneg (hw_nonneg n) (sq_nonneg M.nu⁻¹))
    simpa only [X, a, A0, w, mul_assoc, mul_left_comm, mul_comm] using htail
  have hscale : ∑' n, a n ≤ cutoffMassLinearWeightedScale M m s := by
    rw [show (∑' n, a n) = A0 *
        ∑' n, Book.Ch02.geometricWeight (s : ℝ) 2 n *
          descendantMassFactor d n by
      rw [tsum_mul_left]]
    have hsum := tsum_geometricWeight_mul_descendantMassFactor_le_baseLoss d s
    have hmul := mul_le_mul_of_nonneg_left hsum hA0_pos.le
    simpa only [A0, cutoffMassLinearWeightedScale, mul_assoc] using hmul
  have htail :=
    Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (μ := (cutoffSampleLaw M).toMeasure) (σ := 1)
      (X := X) (a := a) (B := cutoffMassLinearWeightedScale M m s)
      (by norm_num) hX_nonneg hX_meas ha_pos ha_summable hX_tail hscale
  simpa only [cutoffMassLinearWeightedSum, X, w] using! htail

end

end Algsuperdiff.Section3.Provider.Base

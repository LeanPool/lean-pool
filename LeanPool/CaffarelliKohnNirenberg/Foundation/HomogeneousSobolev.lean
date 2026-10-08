/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallTopology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormLeVecEuclidean
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Homogeneous Sobolev estimates in three dimensions

The compact-support estimate is the Gagliardo--Nirenberg--Sobolev inequality
used in the cutoff step of `lem:J-weak-div`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace CKN

/-- The cube-root volume of a three-dimensional Euclidean ball is bounded
by twice its radius. -/
theorem euclideanBall_volume_rpow_third_le {R : ℝ} (hR : 0 < R) :
    volume (CKN.euclideanBall (0 : CKN.Foundation.Parabolic.Vec3) R) ^
      (1 / 3 : ℝ) ≤ ENNReal.ofReal (2 * R) := by
  rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hR,
    CKN.Foundation.Parabolic.volume_vec3Ball_eq]
  have hconst : ENNReal.ofReal (Real.pi * 4 / 3) ≤ 8 := by
    calc
      ENNReal.ofReal (Real.pi * 4 / 3) ≤ ENNReal.ofReal 8 :=
        ENNReal.ofReal_le_ofReal (by nlinarith only [Real.pi_le_four])
      _ = 8 := by norm_num
  have hcube : ENNReal.ofReal R ^ 3 * 8 = ENNReal.ofReal (2 * R) ^ 3 := by
    rw [← ENNReal.ofReal_pow hR.le 3, ← ENNReal.ofReal_ofNat 8,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ R ^ 3),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R) 3]
    congr 1
    ring
  calc
    (ENNReal.ofReal R ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) ^ (1 / 3 : ℝ) ≤
        (ENNReal.ofReal R ^ 3 * 8) ^ (1 / 3 : ℝ) := by
      apply ENNReal.rpow_le_rpow
      · gcongr
      · norm_num
    _ = ENNReal.ofReal (2 * R) := by
      rw [hcube, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

noncomputable section

/-- The `L²` tail outside expanding Euclidean balls tends to zero. -/
theorem eLpNorm_indicator_compl_euclideanBall_tendsto_zero
    {f : CKN.Foundation.Parabolic.Vec3 → CKN.Foundation.Parabolic.Vec3}
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    Tendsto
      (fun n : ℕ => eLpNorm
        ((CKN.euclideanBall (0 : CKN.Foundation.Parabolic.Vec3) (n : ℝ))ᶜ.indicator f)
        (2 : ℝ≥0∞) volume)
      atTop (nhds 0) := by
  let tailIntegral (n : ℕ) : CKN.Foundation.Parabolic.Vec3 → ℝ≥0∞ :=
    ((CKN.euclideanBall (0 : CKN.Foundation.Parabolic.Vec3) (n : ℝ))ᶜ).indicator
      (fun x => ‖f x‖ₑ ^ (2 : ℝ))
  have hball_mono {n m : ℕ} (hnm : n ≤ m) :
      CKN.euclideanBall (0 : CKN.Foundation.Parabolic.Vec3) (n : ℝ) ⊆
        CKN.euclideanBall (0 : CKN.Foundation.Parabolic.Vec3) (m : ℝ) := by
    intro x hx
    by_cases hn : n = 0
    · subst n
      have hx' : CKN.euclideanSqDist x 0 < 0 := by
        simpa [CKN.euclideanBall] using hx
      have hdist : 0 ≤ CKN.euclideanSqDist x 0 := by
        simpa [CKN.euclideanSqDist, CKN.vecNormSq] using CKN.vecNormSq_nonneg x
      exact False.elim ((not_lt_of_ge hdist) hx')
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hnpos (by exact_mod_cast hnm)
      rw [CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hnpos] at hx
      rw [CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hmpos]
      exact hx.trans_le (by exact_mod_cast hnm)
  have hmeas (n : ℕ) : AEMeasurable (tailIntegral n) volume := by
    apply (hf.aestronglyMeasurable.enorm.pow_const 2).indicator
    exact (CKN.measurableSet_euclideanBall 0 (n : ℝ)).compl
  have hanti : ∀ᵐ x ∂(volume : Measure CKN.Foundation.Parabolic.Vec3),
      Antitone fun n => tailIntegral n x := by
    filter_upwards [] with x
    intro n m hnm
    by_cases hxm : x ∈ CKN.euclideanBall 0 (m : ℝ)
    · simp [tailIntegral, hxm]
    · have hxn : x ∉ CKN.euclideanBall 0 (n : ℝ) := by
        intro hxn
        exact hxm (hball_mono hnm hxn)
      simp [tailIntegral, hxn, hxm]
  have hpoint (x : CKN.Foundation.Parabolic.Vec3) :
      Tendsto (fun n => tailIntegral n x) atTop (nhds 0) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (CKN.vecEuclideanNorm x)
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (CKN.vecEuclideanNorm_nonneg x) hN
    have hEventually : ∀ᶠ n : ℕ in atTop, x ∈ CKN.euclideanBall 0 (n : ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hNpos (by exact_mod_cast hn)
      rw [CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hnpos]
      simpa using lt_of_lt_of_le hN (by exact_mod_cast hn)
    apply tendsto_const_nhds.congr'
    filter_upwards [hEventually] with n hn
    simp [tailIntegral, hn]
  have htotal : ∫⁻ x : CKN.Foundation.Parabolic.Vec3, ‖f x‖ₑ ^ (2 : ℝ) ∂volume < ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hf.aestronglyMeasurable).mp
        hf.eLpNorm_lt_top
    simpa using h
  have hzero : ∫⁻ x : CKN.Foundation.Parabolic.Vec3, tailIntegral 0 x ∂volume ≠ ∞ := by
    apply ne_of_lt
    calc
      ∫⁻ x : CKN.Foundation.Parabolic.Vec3, tailIntegral 0 x ∂volume ≤
          ∫⁻ x : CKN.Foundation.Parabolic.Vec3, ‖f x‖ₑ ^ (2 : ℝ) ∂volume := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ CKN.euclideanBall 0 (0 : ℝ)
        · simp [tailIntegral, hx]
        · simp [tailIntegral, hx]
      _ < ∞ := htotal
  have hIntegral : Tendsto
      (fun n => ∫⁻ x : CKN.Foundation.Parabolic.Vec3, tailIntegral n x ∂volume)
      atTop (nhds 0) := by
    simpa using lintegral_tendsto_of_tendsto_of_antitone hmeas hanti hzero
      (ae_of_all volume hpoint)
  have hformula (n : ℕ) :
      eLpNorm
          ((CKN.euclideanBall (0 : CKN.Foundation.Parabolic.Vec3) (n : ℝ))ᶜ.indicator f)
          (2 : ℝ≥0∞) volume =
        (∫⁻ x : CKN.Foundation.Parabolic.Vec3, tailIntegral n x ∂volume) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      (hf.aestronglyMeasurable.indicator (CKN.measurableSet_euclideanBall 0 (n : ℝ)).compl)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ CKN.euclideanBall 0 (n : ℝ)
    · simp [tailIntegral, Set.indicator, hx]
    · simp [tailIntegral, Set.indicator, hx]
  have hroot : Tendsto
      (fun n => (∫⁻ x : CKN.Foundation.Parabolic.Vec3, tailIntegral n x ∂volume) ^ (1 / 2 : ℝ))
      atTop (nhds 0) := by
    have htmp := hIntegral.ennrpow_const (1 / 2 : ℝ)
    simpa using htmp
  exact hroot.congr' (Filter.Eventually.of_forall fun n => (hformula n).symm)

end

end CKN

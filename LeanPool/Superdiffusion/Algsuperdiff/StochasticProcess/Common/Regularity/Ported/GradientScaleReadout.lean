/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.DyadicRadii
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.FractionalPoincare

/-!
# GradientScaleReadout

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Arbitrary-radius readout of the dyadic gradient iteration
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The dimension-only gradient-row constant in the divergence-source row. -/
def smallContrastGradientConstant (d : ℕ) : ℝ :=
  16 * ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 *
    smallContrastUnitBallVolumePrice d

theorem smallContrastGradientConstant_nonneg (d : ℕ) :
    0 ≤ smallContrastGradientConstant d := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (smallContrastUnitBallVolumePrice_nonneg d)

/-- The local Morrey-gradient row used by Poincaré and Campanato. -/
def HasInteriorSmallContrastGradientScaleBound
    (alpha K : ℝ) (u : H1Function (smallContrastUnitBall d)) : Prop :=
  ∀ z ∈ smallContrastBall d (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
    r ^ (1 - alpha) *
      vectorNormalizedL2On (euclideanBall z r) u.grad ≤ K

/-- Euclidean balls with a displaced centre remain in the ambient ball when
the centre distance plus the inner radius is below the ambient radius. -/
theorem euclideanBall_subset_of_center_distance_add_lt
    {c z : Vec d} {r R : ℝ} (hr : 0 ≤ r)
    (hcz : euclideanNorm (z - c) + r ≤ R) :
    euclideanBall z r ⊆ euclideanBall c R := by
  intro x hx
  have hrpos : 0 < R := by
    have hxnonneg : 0 ≤ euclideanNorm (z - c) := euclideanNorm_nonneg _
    have hr' : 0 < r := by
      by_contra h
      have : r = 0 := le_antisymm (le_of_not_gt h) hr
      subst r
      unfold euclideanBall at hx
      norm_num at hx
      exact (not_lt_of_ge (euclideanSqDist_nonneg x z)) hx
    exact (add_pos_of_nonneg_of_pos hxnonneg hr').trans_le hcz
  apply (mem_euclideanBall_toEuc_iff x c hrpos).1
  have hrinner : 0 < r := by
    by_contra h
    have : r = 0 := le_antisymm (le_of_not_gt h) hr
    subst r
    unfold euclideanBall at hx
    norm_num at hx
    exact (not_lt_of_ge (euclideanSqDist_nonneg x z)) hx
  have hxz := (mem_euclideanBall_toEuc_iff x z hrinner).2 hx
  rw [Metric.mem_ball] at hxz ⊢
  have hzc : dist (toEuc z) (toEuc c) = euclideanNorm (z - c) := by
    rw [dist_eq_norm]
    unfold euclideanNorm
    change ‖toEuc z - toEuc c‖ = Real.sqrt (euclideanSqDist z c)
    rw [← norm_sq_toEuc_sub z c, Real.sqrt_sq (norm_nonneg _)]
  calc
    dist (toEuc x) (toEuc c) ≤
        dist (toEuc x) (toEuc z) + dist (toEuc z) (toEuc c) :=
      dist_triangle _ _ _
    _ < r + euclideanNorm (z - c) := by
      rw [hzc]
      simpa only [add_comm] using
        (add_lt_add_right hxz (euclideanNorm (z - c)))
    _ ≤ R := by simpa only [add_comm] using hcz

theorem exists_smallContrastDyadicRadius_bracket
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R) :
    ∃ n : ℕ,
      smallContrastDyadicRadius R (n + 1) < s ∧
        s ≤ smallContrastDyadicRadius R n := by
  have hx0 : 0 < s / R := div_pos hs hR
  have hx1 : s / R ≤ 1 := (div_le_one hR).2 hsR
  obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near_of_lt_one
    hx0 hx1 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_, ?_⟩
  · rw [smallContrastDyadicRadius]
    rw [Real.rpow_natCast]
    have h := (lt_div_iff₀ hR).1 hnlow
    simpa only [mul_comm] using h
  · rw [smallContrastDyadicRadius, Real.rpow_natCast]
    simpa only [mul_comm] using (div_le_iff₀ hR).1 hnhigh

theorem sqrt_volume_ratio_euclideanBall_le_half_rpow [NeZero d]
    (z : Vec d) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (_hst : s ≤ t) (hts : t ≤ 2 * s) :
    Real.sqrt ((volume (euclideanBall z t)).toReal /
        (volume (euclideanBall z s)).toReal) ≤
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
  have hV : 0 < (volume (smallContrastUnitBall d)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num)))
  rw [volume_euclideanBall_toReal_eq_unit_mul_pow z ht,
    volume_euclideanBall_toReal_eq_unit_mul_pow z hs]
  have hs0 : s ≠ 0 := hs.ne'
  have hratio :
      ((volume (smallContrastUnitBall d)).toReal * t ^ d) /
          ((volume (smallContrastUnitBall d)).toReal * s ^ d) =
        (t / s) ^ d := by
    field_simp [hV.ne', hs0]
    rw [div_pow]
    field_simp [hs0]
  rw [hratio]
  have hts' : t / s ≤ 2 := (div_le_iff₀ hs).2 hts
  have hratio0 : 0 ≤ t / s := div_nonneg ht.le hs.le
  have hpow : (t / s) ^ d ≤ (2 : ℝ) ^ d :=
    pow_le_pow_left₀ hratio0 hts' d
  have hsqrt := Real.sqrt_le_sqrt hpow
  rw [show Real.sqrt ((2 : ℝ) ^ d) =
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) by
    rw [show Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring]
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
      Real.rpow_neg_eq_inv_rpow]
    norm_num] at hsqrt
  exact hsqrt

/-- Arbitrary-radius consequence of an already assembled dyadic scale row. -/
theorem gradientScaleBound_of_dyadic [NeZero d]
    (z : Vec d) {R alpha K : ℝ} (hR : 0 < R)
    (halpha1 : alpha < 1)
    {g : Vec d → Vec d}
    (hg : MemVectorL2 (euclideanBall z R) g)
    (hdyadic : ∀ n : ℕ,
      smallContrastDyadicRadius R n ^ (1 - alpha) *
          vectorNormalizedL2On
            (euclideanBall z (smallContrastDyadicRadius R n)) g ≤ K) :
    ∀ s : ℝ, 0 < s → s ≤ R →
      s ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z s) g ≤
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * K := by
  intro s hs hsR
  obtain ⟨n, hnlow, hnhigh⟩ :=
    exists_smallContrastDyadicRadius_bracket hR hs hsR
  let t : ℝ := smallContrastDyadicRadius R n
  have ht : 0 < t := smallContrastDyadicRadius_pos hR n
  have hst : s ≤ t := hnhigh
  have hts : t ≤ 2 * s := by
    have hsucc := smallContrastDyadicRadius_succ R n
    rw [hsucc] at hnlow
    linarith only [hnlow]
  have hsub : euclideanBall z s ⊆ euclideanBall z t := by
    rcases eq_or_lt_of_le hst with heq | hlt
    · rw [heq]
    · exact euclideanBall_subset_euclideanBall hs.le hlt
  have htg : MemLp (fun x => HilbertVec.ofVec (g x)) 2
      (volume.restrict (euclideanBall z t)) := by
    have htR : t ≤ R := smallContrastDyadicRadius_le hR.le n
    have hsubTR : euclideanBall z t ⊆ euclideanBall z R := by
      rcases eq_or_lt_of_le htR with heq | hlt
      · rw [heq]
      · exact euclideanBall_subset_euclideanBall ht.le hlt
    exact (memHilbertVectorL2_hilbertifyVecField hg).mono_measure
      (Measure.restrict_mono hsubTR le_rfl)
  have hvolR : 0 < (volume (euclideanBall z t)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z ht))
  have hvols : 0 < (volume (euclideanBall z s)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hs))
  have hnorm := vectorNormalizedL2On_le_of_subset hsub hvolR hvols htg
  have hratio := sqrt_volume_ratio_euclideanBall_le_half_rpow z hs ht hst hts
  have hgnonneg : 0 ≤ vectorNormalizedL2On (euclideanBall z t) g := Real.sqrt_nonneg _
  have hnorm' : vectorNormalizedL2On (euclideanBall z s) g ≤
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
        vectorNormalizedL2On (euclideanBall z t) g :=
    hnorm.trans (mul_le_mul_of_nonneg_right hratio hgnonneg)
  have hgap : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha1.le
  have hweight : s ^ (1 - alpha) ≤ t ^ (1 - alpha) :=
    Real.rpow_le_rpow hs.le hst hgap
  have hprod := mul_le_mul hweight hnorm'
    (Real.sqrt_nonneg _) (Real.rpow_nonneg ht.le _)
  calc
    s ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z s) g ≤
        t ^ (1 - alpha) *
          ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
            vectorNormalizedL2On (euclideanBall z t) g) := hprod
    _ = (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          (t ^ (1 - alpha) *
            vectorNormalizedL2On (euclideanBall z t) g) := by ring
    _ ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * K := by
      exact mul_le_mul_of_nonneg_left (hdyadic n)
        (Real.rpow_nonneg (by norm_num) _)

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortProfileSecond

/-!
# Derivatives of the normal transition cutoff

The fixed-width height transition has uniform first and second
derivative bounds independent of the spatial cutoff radius.
-/

public section


open CKN

noncomputable section

namespace ESS

/-- The height cutoff is the canonical profile on an affine argument
of slope two. -/
theorem buShortNormalCutoff_affine (scale : ℝ) :
    buShortNormalCutoff scale =
      fun y => smoothTransitionProfile (2 * (y - buShortYMinus scale)) := by
  funext y
  dsimp [buShortNormalCutoff]
  rw [buShortYPlus_sub_YMinus]
  ring_nf

/-- First derivative of the fixed-width height cutoff. -/
theorem buShortNormalCutoff_deriv (scale y : ℝ) :
    deriv (buShortNormalCutoff scale) y =
      2 * deriv smoothTransitionProfile
        (2 * (y - buShortYMinus scale)) := by
  have harg : HasDerivAt (fun r : ℝ =>
      2 * (r - buShortYMinus scale)) 2 y := by
    convert ((hasDerivAt_id y).sub_const (buShortYMinus scale)).const_mul 2
      using 1
    · funext r
      simp only [id_eq]
    · ring
  have hbase := (smoothTransitionProfile.smooth.differentiable (by simp)
    (2 * (y - buShortYMinus scale))).hasDerivAt.comp y harg
  calc
    deriv (buShortNormalCutoff scale) y =
        deriv (fun r => smoothTransitionProfile
          (2 * (r - buShortYMinus scale))) y := by
          rw [buShortNormalCutoff_affine]
    _ = deriv smoothTransitionProfile
          (2 * (y - buShortYMinus scale)) * 2 := by
          simpa only [Function.comp_def] using hbase.deriv
    _ = _ := by ring

/-- Second derivative of the fixed-width height cutoff. -/
theorem buShortNormalCutoff_deriv_twice (scale y : ℝ) :
    deriv (deriv (buShortNormalCutoff scale)) y =
      4 * deriv (deriv smoothTransitionProfile)
        (2 * (y - buShortYMinus scale)) := by
  have hfun : deriv (buShortNormalCutoff scale) =
      fun r => 2 * deriv smoothTransitionProfile
        (2 * (r - buShortYMinus scale)) := by
    funext r
    exact buShortNormalCutoff_deriv scale r
  rw [hfun]
  have hdiff : Differentiable ℝ (deriv smoothTransitionProfile) := by
    have h := smoothTransitionProfile.smooth.differentiable_iteratedDeriv 1
      (by simp)
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  have harg : HasDerivAt (fun r : ℝ =>
      2 * (r - buShortYMinus scale)) 2 y := by
    convert ((hasDerivAt_id y).sub_const (buShortYMinus scale)).const_mul 2
      using 1
    · funext r
      simp only [id_eq]
    · ring
  have hbase := ((hdiff _).hasDerivAt.comp y harg).const_mul 2
  calc
    deriv (fun r => 2 * deriv smoothTransitionProfile
        (2 * (r - buShortYMinus scale))) y =
        2 * (deriv (deriv smoothTransitionProfile)
          (2 * (y - buShortYMinus scale)) * 2) := by
            simpa only [Function.comp_def] using hbase.deriv
    _ = _ := by ring

/-- The first height derivative is bounded by sixteen. -/
theorem buShortNormalCutoff_abs_deriv_le (scale y : ℝ) :
    |deriv (buShortNormalCutoff scale) y| ≤ 16 := by
  rw [buShortNormalCutoff_deriv, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := smoothTransitionProfile.abs_deriv_le_eight
    (2 * (y - buShortYMinus scale))
  nlinarith only [h]

/-- The second height derivative has one global bound independent of
scale. -/
theorem buShortNormalCutoff_abs_deriv_twice_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ scale y : ℝ,
        |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := bu_short_profile_second_deriv_bound
  refine ⟨4 * C, by positivity, ?_⟩
  intro scale y
  rw [buShortNormalCutoff_deriv_twice, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left (hbound _) (by norm_num)

end ESS

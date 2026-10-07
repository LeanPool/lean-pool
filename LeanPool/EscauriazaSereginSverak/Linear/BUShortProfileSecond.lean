/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortExtDerivatives
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Second derivative bound for the transition profile

The smooth transition profile is constant outside a compact interval,
so its second derivative has one finite global bound.
-/

public section


open Filter Set CKN
open scoped Topology

noncomputable section

namespace ESS

/-- The second derivative of the canonical smooth transition profile is
bounded uniformly on the real line. -/
theorem bu_short_profile_second_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ,
        |deriv (deriv smoothTransitionProfile) x| ≤ C := by
  have hcont : Continuous (fun x : ℝ =>
      deriv (deriv smoothTransitionProfile) x) := by
    have h := smoothTransitionProfile.smooth.continuous_iteratedDeriv 2
      (by simp)
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    hcont.continuousOn
  let C := max 0 C₀
  refine ⟨C, le_max_left _ _, ?_⟩
  intro x
  by_cases hxlow : x < 0
  · have hfirst : ∀ y : ℝ, y < 0 → deriv smoothTransitionProfile y = 0 := by
      intro y hy
      have heq : smoothTransitionProfile =ᶠ[𝓝 y]
          (fun _ : ℝ => 0) := by
        filter_upwards [Iio_mem_nhds hy] with t ht
        exact smoothTransitionProfile.zero_of_nonpos ht.le
      rw [heq.deriv_eq]
      simp
    have heq : deriv smoothTransitionProfile =ᶠ[𝓝 x]
        (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hxlow] with y hy
      exact hfirst y hy
    rw [heq.deriv_eq]
    simp [C]
  · by_cases hxhigh : 1 < x
    · have hfirst : ∀ y : ℝ, 1 < y → deriv smoothTransitionProfile y = 0 := by
        intro y hy
        have heq : smoothTransitionProfile =ᶠ[𝓝 y]
            (fun _ : ℝ => 1) := by
          filter_upwards [Ioi_mem_nhds hy] with t ht
          exact smoothTransitionProfile.one_of_one_le ht.le
        rw [heq.deriv_eq]
        simp
      have heq : deriv smoothTransitionProfile =ᶠ[𝓝 x]
          (fun _ : ℝ => 0) := by
        filter_upwards [Ioi_mem_nhds hxhigh] with y hy
        exact hfirst y hy
      rw [heq.deriv_eq]
      simp [C]
    · have hx : x ∈ Icc (0 : ℝ) 1 :=
        ⟨le_of_not_gt hxlow, le_of_not_gt hxhigh⟩
      exact (hC₀ x hx).trans (le_max_right _ _)

end ESS

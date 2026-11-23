/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# A logarithmic coordinate for maximum-modulus points

A uniform exponential approximation yields a logarithmic correction with
quantitative bounds on its first two derivatives.
-/

@[expose] public section

open Filter Metric Set
open scoped ComplexConjugate

namespace Bruck

theorem slitPlane_of_close_one {z : ℂ} (hz : ‖z - 1‖ < 1) : z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.2
  left
  have h := (abs_le.mp (Complex.abs_re_le_norm (z - 1))).1
  rw [Complex.sub_re, Complex.one_re] at h
  linarith

theorem norm_log_le_of_norm_sub_one_le_half {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) :
    ‖Complex.log z‖ ≤ (3 / 2 : ℝ) * ‖z - 1‖ := by
  simpa only [add_sub_cancel] using Complex.norm_log_one_add_half_le_self hz

/-- Regularity and bounds for the logarithm of the relative error. -/
structure LogarithmicCorrection (F J : ℂ → ℂ) (z : ℂ) : Prop where
  /-- The logarithm is complex differentiable. -/
  differentiable : DifferentiableAt ℂ J z
  /-- Its first derivative is complex differentiable. -/
  differentiable_deriv : DifferentiableAt ℂ (deriv J) z
  /-- Bound on the logarithm. -/
  norm_bound : ‖J z‖ ≤ 1 / 10
  /-- Bound on the first derivative. -/
  deriv_bound : ‖deriv J z‖ ≤ 1 / 10
  /-- Bound on the second derivative. -/
  second_deriv_bound : ‖deriv (deriv J) z‖ ≤ 1 / 5
  /-- Exponentiating recovers the relative error factor. -/
  exp_eq : Complex.exp (J z) = F z

/-- The logarithm of the relative error in the exponential model. -/
theorem exists_logarithmic_correction {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 10))
    (h : ∀ z : ℂ, ‖z‖ < 10 → ‖F z - 1‖ ≤ 1 / 100) :
    ∃ J : ℂ → ℂ, ∀ z ∈ ball 0 9, LogarithmicCorrection F J z := by
  let J := fun z => Complex.log (F z)
  have hslit : ∀ z : ℂ, ‖z‖ < 10 → F z ∈ Complex.slitPlane := by
    intro z hz
    exact slitPlane_of_close_one ((h z hz).trans_lt (by norm_num))
  have hJ (z : ℂ) (hz : z ∈ ball (0 : ℂ) 10) : DifferentiableAt ℂ J z :=
    (Complex.hasDerivAt_log (hslit z (mem_ball_zero_iff.mp hz))).differentiableAt.comp z
      (hF.differentiableAt (isOpen_ball.mem_nhds hz))
  have hbound (z : ℂ) (hz : ‖z‖ < 10) : ‖J z‖ ≤ 1 / 10 := by
    apply (norm_log_le_of_norm_sub_one_le_half ((h z hz).trans (by norm_num))).trans
    linarith [h z hz]
  refine ⟨J, ?_⟩
  intro z hz
  have hz9 := mem_ball_zero_iff.mp hz
  have hz10 : z ∈ ball (0 : ℂ) 10 := mem_ball_zero_iff.mpr (by linarith)
  have hcl : ∀ w ∈ closedBall z 1, w ∈ ball (0 : ℂ) 10 := by
    intro w hw
    apply mem_ball_zero_iff.mpr
    have hw1 := mem_closedBall_iff_norm.mp hw
    have htriangle : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
    linarith
  have hD : DiffContOnCl ℂ J (ball z 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z one_ne_zero]
    exact fun w hw => (hJ w (hcl w hw)).differentiableWithinAt
  have hC : ∀ w ∈ sphere z 1, ‖J w‖ ≤ 1 / 10 :=
    fun w hw => hbound w (mem_ball_zero_iff.mp (hcl w (sphere_subset_closedBall hw)))
  have hd1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hD hC
  have hd2 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 one_pos hD hC
  have ha : AnalyticAt ℂ J z := by
    apply DifferentiableOn.analyticAt (s := ball 0 10)
    · exact fun w hw => (hJ w hw).differentiableWithinAt
    · exact isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by linarith))
  have hzbound := mem_ball_zero_iff.mp hz10
  have hFne := Complex.slitPlane_ne_zero (hslit z hzbound)
  exact ⟨hJ z hz10, ha.deriv.differentiableAt, hbound z hzbound, by simpa using hd1,
    by norm_num [iteratedDeriv_succ] at hd2 ⊢; exact hd2, Complex.exp_log hFne⟩

end Bruck

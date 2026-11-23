/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Inverting a holomorphic perturbation of the identity

A small derivative bound gives a contraction on the disk around each target
and a Lipschitz bound for the inverse on the smaller disk.
-/

@[expose] public section

open Filter Metric Set
open scoped NNReal Topology

namespace Bruck

/-- The inverse of a small perturbation of the identity on the smaller disk. -/
theorem exists_inverse_add {J : ℂ → ℂ}
    (hJ : ∀ z ∈ ball 0 9, DifferentiableAt ℂ J z)
    (hsmall : ∀ z ∈ ball 0 9, ‖J z‖ ≤ 1 / 10)
    (hderiv : ∀ z ∈ ball 0 9, ‖deriv J z‖ ≤ 1 / 10) :
    ∃ B : ℂ → ℂ, ∀ w ∈ ball 0 8,
      B w ∈ ball 0 9 ∧ ‖B w - w‖ ≤ 1 / 10 ∧ B w + J (B w) = w ∧
        HasDerivAt B (1 + deriv J (B w))⁻¹ w := by
  classical
  have hLip : ∀ u ∈ ball (0 : ℂ) 9, ∀ v ∈ ball (0 : ℂ) 9,
      ‖J u - J v‖ ≤ (1 / 10 : ℝ) * ‖u - v‖ := by
    intro u hu v hv
    exact (convex_ball (0 : ℂ) 9).norm_image_sub_le_of_norm_deriv_le hJ hderiv hv hu
  have hfixed (w : ℂ) (hw : w ∈ ball (0 : ℂ) 8) :
      ∃ z ∈ closedBall w (1 / 10), z + J z = w := by
    have hsub : closedBall w (1 / 10) ⊆ ball 0 9 := by
      intro z hz
      rw [mem_ball_zero_iff] at hw ⊢
      rw [mem_closedBall, dist_eq_norm] at hz
      have htriangle : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - w) w
      linarith
    let T : ℂ → ℂ := fun z => w - J z
    have hmaps : MapsTo T (closedBall w (1 / 10)) (closedBall w (1 / 10)) := by
      intro z hz
      simpa [T, mem_closedBall, dist_eq_norm, sub_right_comm] using hsmall z (hsub hz)
    have hcontract : ContractingWith (1 / 10 : ℝ≥0)
        (hmaps.restrict T (closedBall w (1 / 10)) (closedBall w (1 / 10))) := by
      refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
      have h := hLip u (hsub u.2) v (hsub v.2)
      change dist (T u) (T v) ≤ ((1 / 10 : ℝ≥0) : ℝ) * dist (u : ℂ) (v : ℂ)
      simp only [T, dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      rwa [show w - J (u : ℂ) - (w - J (v : ℂ)) = -(J (u : ℂ) - J (v : ℂ)) by ring,
        norm_neg]
    obtain ⟨z, hz, hzfix, _, _⟩ := hcontract.exists_fixedPoint'
      isClosed_closedBall.isComplete hmaps (x := w) (mem_closedBall_self (by norm_num))
      (edist_ne_top _ _)
    refine ⟨z, hz, ?_⟩
    change w - J z = z at hzfix
    linear_combination -hzfix
  let B : ℂ → ℂ := fun w => if hw : w ∈ ball (0 : ℂ) 8 then (hfixed w hw).choose else 0
  have hB (w : ℂ) (hw : w ∈ ball (0 : ℂ) 8) :
      B w ∈ ball 0 9 ∧ ‖B w - w‖ ≤ 1 / 10 ∧ B w + J (B w) = w := by
    have hz := (hfixed w hw).choose_spec
    have hBw : B w = (hfixed w hw).choose := by simp only [B, dite_eq_left hw]
    have hdist : ‖B w - w‖ ≤ 1 / 10 := by
      simpa only [hBw, mem_closedBall, dist_eq_norm] using hz.1
    have hw' := mem_ball_zero_iff.mp hw
    have htriangle : ‖B w‖ ≤ ‖B w - w‖ + ‖w‖ := by
      simpa only [sub_add_cancel] using norm_add_le (B w - w) w
    exact ⟨mem_ball_zero_iff.mpr (by linarith), hdist, hBw ▸ hz.2⟩
  have hBlip (u : ℂ) (hu : u ∈ ball (0 : ℂ) 8) (v : ℂ) (hv : v ∈ ball (0 : ℂ) 8) :
      ‖B u - B v‖ ≤ (10 / 9 : ℝ) * ‖u - v‖ := by
    have hJu := (hB u hu).2.2
    have hJv := (hB v hv).2.2
    have h := norm_sub_le (u - v) (J (B u) - J (B v))
    have hid : (u - v) - (J (B u) - J (B v)) = B u - B v := by
      linear_combination -hJu + hJv
    rw [hid] at h
    nlinarith only [h, hLip (B u) (hB u hu).1 (B v) (hB v hv).1]
  have hcontinuous : ContinuousOn B (ball (0 : ℂ) 8) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := (10 / 9 : ℝ≥0)) ?_).continuousOn
    intro u hu v hv
    simpa [dist_eq_norm] using hBlip u hu v hv
  refine ⟨B, fun w hw => ⟨(hB w hw).1, (hB w hw).2.1, (hB w hw).2.2, ?_⟩⟩
  have hD := (hasDerivAt_id (B w)).add (hJ (B w) (hB w hw).1).hasDerivAt
  have hne : 1 + deriv J (B w) ≠ 0 := by
    intro h
    have h1 : deriv J (B w) = -1 := by linear_combination h
    have hb := hderiv (B w) (hB w hw).1
    rw [h1, norm_neg, norm_one] at hb
    norm_num at hb
  have hnear : ∀ᶠ u in 𝓝 w, u ∈ ball (0 : ℂ) 8 := isOpen_ball.mem_nhds hw
  exact hD.of_local_left_inverse (hcontinuous.continuousAt (isOpen_ball.mem_nhds hw)) hne
    (hnear.mono fun u hu => (hB u hu).2.2)

end Bruck

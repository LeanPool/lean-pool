/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Algorithms.DampedGeneralizedAccelerated
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

lemma gronwall_unit_bound {K c : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) :
    gronwallBound 0 K c 1 ≤ c * Real.exp K := by
  by_cases hz : K = 0
  · simp [hz, gronwallBound_K0]
  · have hpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hz)
    rw [gronwallBound_of_K_ne_0 hz]
    simp only [zero_mul, zero_add, mul_one]
    have he := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg K)
      (Real.exp_pos K).le
    rw [← Real.exp_add] at he
    simp only [neg_add_cancel, Real.exp_zero] at he
    have he' : Real.exp K - 1 ≤ K * Real.exp K := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he' (div_nonneg hc hK)
    calc
      c / K * (Real.exp K - 1) ≤ c / K * (K * Real.exp K) := hm
      _ = c * Real.exp K := by field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma gradient_growth {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (x y : E) :
    ‖g x - g y‖ ≤ (L0 + L1 * ‖g y‖) *
      Real.exp (L1 * ‖x - y‖) * ‖x - y‖ := by
  let d := x - y
  let F := fun t : ℝ => g (y + t • d) - g y
  let F' := fun t : ℝ => (fderiv ℝ g (y + t • d)) d
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    simpa [F, F'] using
      (((hg (y + t • d)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const d |>.const_add y)).sub_const (g y))
  have hbound : ∀ t, ‖F' t‖ ≤ (L1 * ‖d‖) * ‖F t‖ +
      (L0 + L1 * ‖g y‖) * ‖d‖ := by
    intro t
    calc
      ‖F' t‖ ≤ ‖fderiv ℝ g (y + t • d)‖ * ‖d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L0 + L1 * ‖g (y + t • d)‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _)
      _ ≤ (L0 + L1 * (‖F t‖ + ‖g y‖)) * ‖d‖ := by
        gcongr
        exact norm_le_norm_sub_add _ _
      _ = (L1 * ‖d‖) * ‖F t‖ + (L0 + L1 * ‖g y‖) * ‖d‖ := by ring
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (show ContinuousOn F (Icc 0 1) from
      (continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)).continuousOn)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show ‖F 0‖ ≤ (0 : ℝ) by simp [F]) (fun t _ => hbound t)
    1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hb := gronwall_unit_bound (K := L1 * ‖d‖)
    (c := (L0 + L1 * ‖g y‖) * ‖d‖) (by positivity) (by positivity)
  simp only [sub_zero] at h
  have hr := h.trans hb
  simpa [F, d, mul_assoc, mul_left_comm, mul_comm] using hr

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma localCurvature_pos {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (g : E) :
    0 < localCurvature L0 L1 g := by
  unfold localCurvature
  positivity

omit [CompleteSpace E] in
lemma local_step_norm {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (y g : E) :
    ‖y - (1 / localCurvature L0 L1 g) • g - y‖ =
      ‖g‖ / localCurvature L0 L1 g := by
  have he : y - (1 / localCurvature L0 L1 g) • g - y =
      -(1 / localCurvature L0 L1 g) • g := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (one_div_pos.mpr (localCurvature_pos hL0 hL1 g))]
  ring

omit [CompleteSpace E] in
lemma local_step_gradient_error {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (y : E) :
    ‖g (y - (1 / localCurvature L0 L1 (g y)) • g y) - g y‖ ≤ ‖g y‖ / 2 := by
  have hcurv := localCurvature_pos hL0 hL1 (g y)
  have hdist := local_step_norm hL0 hL1 y (g y)
  have hsmall : L1 * (‖g y‖ / localCurvature L0 L1 (g y)) ≤ 1 / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hcurv).mpr
    unfold localCurvature
    nlinarith
  have hexp : Real.exp (L1 * (‖g y‖ / localCurvature L0 L1 (g y))) ≤ 2 := by
    apply (Real.exp_le_exp.mpr hsmall).trans
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hb := gradient_growth hL0.le hL1 hg hH
    (y - (1 / localCurvature L0 L1 (g y)) • g y) y
  rw [hdist] at hb
  calc
    _ ≤ (L0 + L1 * ‖g y‖) *
        Real.exp (L1 * (‖g y‖ / localCurvature L0 L1 (g y))) *
        (‖g y‖ / localCurvature L0 L1 (g y)) := hb
    _ ≤ (L0 + L1 * ‖g y‖) * 2 * (‖g y‖ / localCurvature L0 L1 (g y)) := by
      gcongr
    _ = ‖g y‖ / 2 := by
      have hc : L0 + L1 * ‖g y‖ ≠ 0 := ne_of_gt (by positivity)
      unfold localCurvature
      field_simp; ring

omit [CompleteSpace E] in
lemma local_step_residual {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (y : E) :
    let M := localCurvature L0 L1 (g y)
    let w := y - (1 / M) • g y
    ‖g w + M • (w - y)‖ ≤ M / 2 * ‖w - y‖ := by
  dsimp only
  have hM := localCurvature_pos hL0 hL1 (g y)
  have he : localCurvature L0 L1 (g y) •
      (y - (1 / localCurvature L0 L1 (g y)) • g y - y) = -g y := by
    match_scalars
    all_goals field_simp [hM.ne'] <;> ring
  rw [he, ← sub_eq_add_neg, local_step_norm hL0 hL1 y (g y)]
  convert local_step_gradient_error hL0 hL1 hg hH y using 1
  field_simp


omit [CompleteSpace E] in
lemma local_step_movement {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (y g : E) :
    localCurvature L0 L1 g ≤ 8 * L0 ∨
      1 / (8 * L1) ≤ ‖y - (1 / localCurvature L0 L1 g) • g - y‖ := by
  by_cases hsmall : localCurvature L0 L1 g ≤ 8 * L0
  · exact Or.inl hsmall
  · right
    rw [local_step_norm hL0 hL1.le y g]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * L1)
      (localCurvature_pos hL0 hL1.le g)).mpr
    unfold localCurvature at hsmall ⊢
    nlinarith

end LongTails.OracleTemplate.GeneralizedAccelerated

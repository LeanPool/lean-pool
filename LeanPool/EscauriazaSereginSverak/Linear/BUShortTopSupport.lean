/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEtaGapSupport

/-!
# Upper time support of the short-time cutoff

On each bounded spatial ball the normal phase tends uniformly to zero as
time approaches one. The shifted-phase cutoff therefore turns off before the
upper time face of `lem:bu-small-time`.
-/

public section


open Set CKN CKN.Foundation.Parabolic Filter
open scoped Topology

noncomputable section

namespace ESS

/-- At every fixed height, the normal phase is continuous at time one and
equals zero there. -/
theorem buShortF_continuousAt_one (y : ℝ) :
    ContinuousAt (fun s : ℝ => buShortF y s) 1 ∧ buShortF y 1 = 0 := by
  have hpow : ContinuousAt (fun s : ℝ => s ^ (-(3 / 4 : ℝ))) 1 :=
    continuousAt_id.rpow_const (Or.inl one_ne_zero)
  have hcont : ContinuousAt
      (fun s : ℝ => (1 - s) * y ^ (3 / 2 : ℝ) *
        s ^ (-(3 / 4 : ℝ))) 1 :=
    ((continuousAt_const.sub continuousAt_id).mul continuousAt_const).mul hpow
  refine ⟨hcont, ?_⟩
  simp [buShortF]

/-- On any bounded normal height range, the phase becomes smaller than a
fixed positive threshold before the upper time face. -/
theorem buShortF_small_near_one
    (scale R : ℝ) (hscale : 0 < scale) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      ∀ y s : ℝ, 0 ≤ y → y ≤ 2 * R → σ ≤ s → s < 1 →
        buShortF y s < buShortB scale / 4 := by
  have hB : 0 < buShortB scale := buShortB_pos hscale
  have hcont := (buShortF_continuousAt_one (2 * R)).1
  have hzero := (buShortF_continuousAt_one (2 * R)).2
  have hval : buShortF (2 * R) 1 < buShortB scale / 4 := by
    rw [hzero]
    positivity
  have hnhds : {s : ℝ | buShortF (2 * R) s < buShortB scale / 4} ∈ 𝓝 (1 : ℝ) := by
    exact hcont.preimage_mem_nhds
      ((isOpen_lt continuous_id continuous_const).mem_nhds hval)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let ε : ℝ := min (δ / 2) (1 / 4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεle : ε ≤ δ / 2 := min_le_left _ _
  have hεquarter : ε ≤ 1 / 4 := min_le_right _ _
  refine ⟨1 - ε, ?_, ?_, ?_⟩
  · linarith only [hεquarter]
  · linarith only [hε]
  intro y s hy hyR hs hs1
  have hs0 : 0 < s := by linarith only [hεquarter, hs]
  have hdist : dist s (1 : ℝ) < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs1.le)]
    have hupper : 1 - s ≤ ε := by linarith only [hs]
    linarith only [hupper, hεle, hδ]
  have hFtop : buShortF (2 * R) s < buShortB scale / 4 :=
    hball (Metric.mem_ball.mpr hdist)
  have hFle : buShortF y s ≤ buShortF (2 * R) s :=
    buShortF_mono_height hy hyR hs0 hs1.le
  exact lt_of_le_of_lt hFle hFtop

/-- The phase cutoff vanishes on a bounded spatial ball at times above a
fixed level below one. -/
theorem buShortEtaExt_zero_near_one
    {scale R : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      ∀ y : Vec3, y ∈ vec3Ball 0 (2 * R) →
      ∀ s : ℝ, σ ≤ s → s < 1 →
        buShortEtaExt scale (y, s) = 0 := by
  obtain ⟨σ, hσ, hσ1, hsmall⟩ := buShortF_small_near_one scale R hscale
  refine ⟨σ, hσ, hσ1, ?_⟩
  intro y hyball s hs hs1
  by_cases hy : y 2 ≤ buShortYMinus scale
  · unfold buShortEtaExt
    rw [buShortNormalCutoff_eq_zero hy]
    ring
  · have hyminus : buShortYMinus scale < y 2 := lt_of_not_ge hy
    have hy2 : 2 ≤ y 2 := by
      have h : 1 < 3 / scale := by
        apply (lt_div_iff₀ hscale).2
        linarith only [hscale1]
      have hminus : 2 < buShortYMinus scale := by
        dsimp [buShortYMinus]
        linarith only [h]
      exact (le_of_lt hminus).trans hyminus.le
    have hyR : y 2 ≤ 2 * R := by
      have hnorm : vec3EuclideanNorm y < 2 * R := by
        simpa only [sub_zero] using (mem_vec3Ball).1 hyball
      have hcoord : y 2 ≤ vec3EuclideanNorm y :=
        (le_abs_self _).trans (abs_apply_le_vec3EuclideanNorm y 2)
      exact (hcoord.trans hnorm.le)
    have hF : buShortF (y 2) s < buShortB scale / 4 :=
      hsmall (y 2) s ((by norm_num : (0 : ℝ) ≤ 2).trans hy2) hyR hs hs1
    have hB := buShortB_pos hscale
    have hphase : (buShortF (y 2) s - buShortB scale) /
        buShortB scale ≤ -(3 / 4 : ℝ) := by
      apply (div_le_iff₀ hB).2
      linarith only [hF]
    rw [buShortEtaExt_eq hscale hscale1 hyminus (le_trans hσ.le hs)]
    exact buShortCutoff_eq_zero_of_low_phase hphase

/-- The normal phase is nonpositive at all times from one onward. -/
theorem buShortF_nonpos_after_one {y s : ℝ}
    (hy : 0 ≤ y) (hs : 1 ≤ s) : buShortF y s ≤ 0 := by
  have hfirst : 1 - s ≤ 0 := sub_nonpos.mpr hs
  have hyPow : 0 ≤ y ^ (3 / 2 : ℝ) := by positivity
  have hsPow : 0 ≤ s ^ (-(3 / 4 : ℝ)) := by positivity
  dsimp [buShortF]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hfirst hyPow) hsPow

/-- The shifted-phase cutoff vanishes at and after the upper time face. -/
theorem buShortEtaExt_zero_after_one
    {scale : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (y : Vec3) {s : ℝ} (hs : 1 ≤ s) :
    buShortEtaExt scale (y, s) = 0 := by
  by_cases hy : y 2 ≤ buShortYMinus scale
  · unfold buShortEtaExt
    rw [buShortNormalCutoff_eq_zero hy]
    ring
  · have hyminus : buShortYMinus scale < y 2 := lt_of_not_ge hy
    have hy2 : 2 ≤ y 2 := by
      have h : 1 < 3 / scale := by
        apply (lt_div_iff₀ hscale).2
        linarith only [hscale1]
      have hminus : 2 < buShortYMinus scale := by
        dsimp [buShortYMinus]
        linarith only [h]
      exact (le_of_lt hminus).trans hyminus.le
    have hF := buShortF_nonpos_after_one
      ((by norm_num : (0 : ℝ) ≤ 2).trans hy2) hs
    have hB := buShortB_pos hscale
    have hphase : (buShortF (y 2) s - buShortB scale) /
        buShortB scale ≤ -(3 / 4 : ℝ) := by
      apply (div_le_iff₀ hB).2
      linarith only [hF, hB]
    rw [buShortEtaExt_eq hscale hscale1 hyminus
      (le_trans (by norm_num : (1 / 2 : ℝ) ≤ 1) hs)]
    exact buShortCutoff_eq_zero_of_low_phase hphase

end ESS

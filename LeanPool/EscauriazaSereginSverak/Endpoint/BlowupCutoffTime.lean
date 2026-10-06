/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureUniform
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile

/-!
# Blowup Cutoff Time

Cutoff bounds used to localize the rescaled endpoint sequence.
-/

public section

open MeasureTheory Set
open CKN
noncomputable section
namespace ESS

/-- A smooth time cutoff equal to one on `[a,b]`, supported strictly below
zero, with a fixed rising transition and a movable falling transition. -/
@[expose] def blowupTimeCutoff (a b t : ℝ) : ℝ :=
  smoothTransitionProfile (t - (a - 1)) *
    smoothTransitionProfile ((b / 2 - t) / (-b / 2))

/-- The time cutoff is smooth when the upper plateau endpoint is negative. -/
theorem blowupTimeCutoff_smooth (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (blowupTimeCutoff a b) := by
  unfold blowupTimeCutoff
  have hleft : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t - (a - 1)) := by
    fun_prop
  have hright : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (b / 2 - t) / (-b / 2)) := by
    fun_prop
  exact (smoothTransitionProfile.smooth.comp hleft).mul
    (smoothTransitionProfile.smooth.comp hright)

/-- The cutoff takes values in `[0,1]`. -/
theorem blowupTimeCutoff_bounds (a b t : ℝ) :
    0 ≤ blowupTimeCutoff a b t ∧ blowupTimeCutoff a b t ≤ 1 := by
  unfold blowupTimeCutoff
  constructor
  · exact mul_nonneg (smoothTransitionProfile.nonneg _)
      (smoothTransitionProfile.nonneg _)
  · exact (mul_le_mul_of_nonneg_right (smoothTransitionProfile.le_one _)
      (smoothTransitionProfile.nonneg _)).trans (by
        simpa only [one_mul] using smoothTransitionProfile.le_one
          ((b / 2 - t) / (-b / 2)))

/-- The cutoff equals one throughout its intended time interval. -/
theorem blowupTimeCutoff_eq_one
    {a b t : ℝ} (hb : b < 0) (hat : a ≤ t) (htb : t ≤ b) :
    blowupTimeCutoff a b t = 1 := by
  have hleft : 1 ≤ t - (a - 1) := by linarith only [hat]
  have hden : 0 < -b / 2 := by linarith only [hb]
  have hright : 1 ≤ (b / 2 - t) / (-b / 2) := by
    apply (le_div_iff₀ hden).2
    linarith only [htb]
  simp only [blowupTimeCutoff,
    smoothTransitionProfile.one_of_one_le hleft,
    smoothTransitionProfile.one_of_one_le hright, one_mul]

/-- The cutoff vanishes to the left of its fixed rising transition. -/
theorem blowupTimeCutoff_zero_left
    {a b t : ℝ} (ht : t ≤ a - 1) :
    blowupTimeCutoff a b t = 0 := by
  have harg : t - (a - 1) ≤ 0 := by linarith only [ht]
  simp only [blowupTimeCutoff,
    smoothTransitionProfile.zero_of_nonpos harg, zero_mul]

/-- The cutoff vanishes beyond the upper transition. -/
theorem blowupTimeCutoff_zero_right
    {a b t : ℝ} (hb : b < 0) (ht : b / 2 ≤ t) :
    blowupTimeCutoff a b t = 0 := by
  have hden : 0 < -b / 2 := by linarith only [hb]
  have harg : (b / 2 - t) / (-b / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith only [ht]) hden.le
  simp only [blowupTimeCutoff,
    smoothTransitionProfile.zero_of_nonpos harg, mul_zero]

/-- The cutoff has compact support inside the source past interval. -/
theorem blowupTimeCutoff_hasCompactSupport (a b : ℝ) (hb : b < 0) :
    HasCompactSupport (blowupTimeCutoff a b) := by
  refine HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Icc (a - 1) (b / 2))) ?_
  intro t ht
  by_cases hleft : t ≤ a - 1
  · exact blowupTimeCutoff_zero_left hleft
  · have hright : b / 2 < t := by
      by_contra h
      exact ht ⟨le_of_lt (lt_of_not_ge hleft), le_of_not_gt h⟩
    exact blowupTimeCutoff_zero_right hb hright.le

/-- The closed support of the cutoff stays a positive distance from time
zero. -/
theorem blowupTimeCutoff_tsupport_subset
    (a b : ℝ) (hb : b < 0) :
    tsupport (blowupTimeCutoff a b) ⊆ Icc (a - 1) (b / 2) := by
  have hsupp : Function.support (blowupTimeCutoff a b) ⊆
      Icc (a - 1) (b / 2) := by
    intro t ht
    constructor
    · by_contra h
      exact ht (blowupTimeCutoff_zero_left (le_of_not_ge h))
    · by_contra h
      exact ht (blowupTimeCutoff_zero_right hb (le_of_not_ge h))
  exact closure_minimal hsupp isClosed_Icc

/-- The support is strictly inside any past interval beginning one unit
before the rising transition. -/
theorem blowupTimeCutoff_tsupport_subset_open
    (a b : ℝ) (hb : b < 0) :
    tsupport (blowupTimeCutoff a b) ⊆ Ioo (a - 2) 0 := by
  intro t ht
  have h := blowupTimeCutoff_tsupport_subset a b hb ht
  exact ⟨by linarith only [h.1], by linarith only [h.2, hb]⟩

/-- The positive time derivative of the cutoff is bounded independently of
the upper transition width. -/
theorem blowupTimeCutoff_deriv_le_eight
    (a b t : ℝ) (hb : b < 0) :
    deriv (blowupTimeCutoff a b) t ≤ 8 := by
  let L : ℝ → ℝ := fun s => smoothTransitionProfile (s - (a - 1))
  let U : ℝ → ℝ := fun s =>
    smoothTransitionProfile ((b / 2 - s) / (-b / 2))
  have hden : 0 < -b / 2 := by linarith only [hb]
  have hLarg : HasDerivAt (fun s : ℝ => s - (a - 1)) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (a - 1)
  have hUarg : HasDerivAt (fun s : ℝ => (b / 2 - s) / (-b / 2))
      (-1 / (-b / 2)) t := by
    convert (((hasDerivAt_const t (b / 2)).sub (hasDerivAt_id t)).div_const
      (-b / 2)) using 1
    · funext s
      simp only [Pi.sub_apply, id_eq]
    · ring
  have hLprof : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile (t - (a - 1)))
      (t - (a - 1)) :=
    (smoothTransitionProfile.smooth.differentiable (by simp) _).hasDerivAt
  have hUprof : HasDerivAt smoothTransitionProfile
      (deriv smoothTransitionProfile ((b / 2 - t) / (-b / 2)))
      ((b / 2 - t) / (-b / 2)) :=
    (smoothTransitionProfile.smooth.differentiable (by simp) _).hasDerivAt
  have hLd : HasDerivAt L
      (deriv smoothTransitionProfile (t - (a - 1))) t := by
    simpa only [L, Function.comp_def, mul_one] using hLprof.comp t hLarg
  have hUd : HasDerivAt U
      (deriv smoothTransitionProfile ((b / 2 - t) / (-b / 2)) *
        (-1 / (-b / 2))) t := by
    simpa only [U, Function.comp_def] using hUprof.comp t hUarg
  have hLnonneg : 0 ≤ L t := smoothTransitionProfile.nonneg _
  have hUnonneg : 0 ≤ U t := smoothTransitionProfile.nonneg _
  have hUle : U t ≤ 1 := smoothTransitionProfile.le_one _
  have hLdnonneg : 0 ≤ deriv L t := by
    rw [hLd.deriv]
    exact Real.smoothTransition.monotone.deriv_nonneg
  have hLdle : deriv L t ≤ 8 := by
    rw [hLd.deriv]
    exact le_trans (le_abs_self _) (by
      simpa only [smoothTransitionProfile] using
        smoothTransitionProfile.abs_deriv_le_eight (t - (a - 1)))
  have hUdnonpos : deriv U t ≤ 0 := by
    rw [hUd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Real.smoothTransition.monotone.deriv_nonneg)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le)
  have hformula : deriv (blowupTimeCutoff a b) t =
      deriv L t * U t + L t * deriv U t := by
    change deriv (fun s => L s * U s) t = _
    exact deriv_mul hLd.differentiableAt hUd.differentiableAt
  rw [hformula]
  calc
    deriv L t * U t + L t * deriv U t ≤ deriv L t * U t + 0 :=
      add_le_add le_rfl (mul_nonpos_of_nonneg_of_nonpos hLnonneg hUdnonpos)
    _ = deriv L t * U t := by ring
    _ ≤ 8 * U t := mul_le_mul_of_nonneg_right hLdle hUnonneg
    _ ≤ 8 := by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hUle (by norm_num : (0 : ℝ) ≤ 8)

end ESS

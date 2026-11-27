/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import LeanPool.VenNullClockRoundRates.RoundAreaUpperHemisphere
public import LeanPool.VenNullClockRoundRates.VenRateUpperStrips
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local cutoffs for the positive and negative Cartesian strips
-/

@[expose] public section
noncomputable section

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace VenRateUpper

theorem continuous_graphHeight : Continuous graphHeight := by
  unfold graphHeight
  fun_prop

theorem contDiff_chartEnergy : ContDiff ℝ ∞ chartEnergy := by
  unfold chartEnergy
  fun_prop

theorem contDiff_chartGap (θ b : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ chartGap θ b p.1 p.2) := by
  unfold chartGap chartEnergy
  fun_prop

/-- Choose one shared horizontal interval and fixed transverse intervals with
strict sign and positive hemisphere height margins. -/
theorem exists_chartStripRectangles {θ b : ℝ}
    (hθ : 0 < 1 - Real.cos θ ^ 2) (hb : 0 < b) :
    ∃ l u yp ym rp rm δ z : ℝ, 0 < l ∧ l < u ∧ u < 1 ∧
      0 < rp ∧ 0 < rm ∧ 0 < δ ∧ 0 < z ∧
      (∀ p ∈ Icc l u ×ˢ Metric.closedBall yp rp,
        δ < chartGap θ b p.1 p.2 ∧ z < graphHeight p) ∧
      (∀ p ∈ Icc l u ×ˢ Metric.closedBall ym rm,
        δ < -chartGap θ b p.1 p.2 ∧ z < graphHeight p) := by
  obtain ⟨x, yp, ym, hx, hdP, hdM, hP, hM⟩ := opposite_chart_points hθ hb
  have hDiskP : (x, yp) ∈ graphDisk := by
    change 0 < 1 - x ^ 2 - yp ^ 2
    linarith
  have hDiskM : (x, ym) ∈ graphDisk := by
    change 0 < 1 - x ^ 2 - ym ^ 2
    linarith
  let δ := min (chartGap θ b x yp) (-chartGap θ b x ym) / 2
  let z := min (graphHeight (x, yp)) (graphHeight (x, ym)) / 2
  have hδ : 0 < δ := div_pos (lt_min hP (by linarith)) (by norm_num)
  have hz : 0 < z := div_pos (lt_min (graphHeight_pos hDiskP) (graphHeight_pos hDiskM)) (by
    norm_num)
  have hδlt : δ < min (chartGap θ b x yp) (-chartGap θ b x ym) := by dsimp [δ] at *; linarith
  have hzlt : z < min (graphHeight (x, yp)) (graphHeight (x, ym)) := by dsimp [z] at *; linarith
  let A : Set (ℝ × ℝ) := {p | δ < chartGap θ b p.1 p.2 ∧ z < graphHeight p}
  let B : Set (ℝ × ℝ) := {p | δ < -chartGap θ b p.1 p.2 ∧ z < graphHeight p}
  have hA : IsOpen A :=
    (isOpen_lt continuous_const (contDiff_chartGap θ b).continuous).inter
      (isOpen_lt continuous_const continuous_graphHeight)
  have hB : IsOpen B :=
    (isOpen_lt continuous_const (contDiff_chartGap θ b).continuous.neg).inter
      (isOpen_lt continuous_const continuous_graphHeight)
  have hxA : (x, yp) ∈ A :=
    ⟨hδlt.trans_le (min_le_left _ _), hzlt.trans_le (min_le_left _ _)⟩
  have hxB : (x, ym) ∈ B :=
    ⟨hδlt.trans_le (min_le_right _ _), hzlt.trans_le (min_le_right _ _)⟩
  obtain ⟨Xp, hXp, Yp, hYp, hXYp⟩ := mem_nhds_prod_iff.mp (hA.mem_nhds hxA)
  obtain ⟨Xm, hXm, Ym, hYm, hXYm⟩ := mem_nhds_prod_iff.mp (hB.mem_nhds hxB)
  have hX : Xp ∩ Xm ∩ Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
    inter_mem (inter_mem hXp hXm) (isOpen_Ioo.mem_nhds hx)
  obtain ⟨rx, hrx, hRX⟩ := Metric.mem_nhds_iff.mp hX
  let l := x - rx / 2
  let u := x + rx / 2
  have hlu : l < u := by dsimp [l, u]; linarith
  have hI : Icc l u ⊆ Xp ∩ Xm ∩ Ioo (0 : ℝ) 1 := by
    intro v hv
    apply hRX
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [show x - rx / 2 ≤ v from hv.1],
      by linarith [show v ≤ x + rx / 2 from hv.2]⟩
  obtain ⟨rp, hrp, hp⟩ := Metric.mem_nhds_iff.mp hYp
  obtain ⟨rm, hrm, hm⟩ := Metric.mem_nhds_iff.mp hYm
  refine ⟨l, u, yp, ym, rp / 2, rm / 2, δ, z,
    (hI (left_mem_Icc.mpr hlu.le)).2.1, hlu, (hI (right_mem_Icc.mpr hlu.le)).2.2,
    by positivity, by positivity, hδ, hz, ?_, ?_⟩
  · intro p hp'
    exact hXYp ⟨(hI hp'.1).1.1, hp (Metric.closedBall_subset_ball (by linarith) hp'.2)⟩
  · intro p hp'
    exact hXYm ⟨(hI hp'.1).1.2, hm (Metric.closedBall_subset_ball (by linarith) hp'.2)⟩

/-- A positive globally smooth denominator equal to its argument above `δ`. -/
def cutoffDenominator (δ x : ℝ) : ℝ :=
  δ * (1 - Real.smoothTransition (x / δ)) + x * Real.smoothTransition (x / δ)

theorem cutoffDenominator_pos {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 < cutoffDenominator δ x := by
  unfold cutoffDenominator
  by_cases hx : x ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hδ.le)]
    simpa using hδ
  · let t := Real.smoothTransition (x / δ)
    have ht0 : 0 ≤ t := Real.smoothTransition.nonneg _
    have ht1 : t ≤ 1 := Real.smoothTransition.le_one _
    rcases lt_or_eq_of_le ht1 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos hδ (sub_pos.mpr h))
        (mul_nonneg (le_of_lt (lt_of_not_ge hx)) ht0)
    · change 0 < δ * (1 - t) + x * t
      simpa [h] using (lt_of_not_ge hx)

theorem cutoffDenominator_eq_self {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    cutoffDenominator δ x = x := by
  unfold cutoffDenominator
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hδ).2 hx)]
  ring

theorem contDiff_cutoffDenominator (δ : ℝ) : ContDiff ℝ ∞ (cutoffDenominator δ) := by
  unfold cutoffDenominator
  have ht : ContDiff ℝ ∞ (fun x : ℝ ↦ Real.smoothTransition (x / δ)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)
  exact (contDiff_const.mul (contDiff_const.sub ht)).add (contDiff_id.mul ht)

/-- Fixed normalized nonnegative smooth transverse function within the specified interval. -/
theorem exists_transverse_bump (y r : ℝ) (hr : 0 < r) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ x ∉ Metric.closedBall y r, β x = 0) ∧ (∫ x, β x) = 1 := by
  let B : ContDiffBump y := ⟨r / 2, r, by positivity, by linarith⟩
  have hB : 0 < ∫ x, B x :=
    B.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      B.hasCompactSupport B.nonneg' (by rw [B.one_of_mem_closedBall
        (Metric.mem_closedBall_self B.rIn_pos.le)]; norm_num)
  refine ⟨fun x ↦ (∫ v, B v)⁻¹ * B x, contDiff_const.mul B.contDiff,
    fun x ↦ mul_nonneg (inv_nonneg.mpr hB.le) (B.nonneg' x), ?_, ?_⟩
  · intro x hx
    change (∫ v, B v)⁻¹ * B x = 0
    rw [B.zero_of_le_dist (le_of_lt (lt_of_not_ge hx)), mul_zero]
  · rw [integral_const_mul, inv_mul_cancel₀ hB.ne']

/-- The same compact smooth cutoff in the first Cartesian coordinate is used on both signs. -/
theorem exists_height_cutoff {l u : ℝ} (hl : 0 < l) (hlu : l < u) (hu : u < 1) :
    ∃ h₀ h₁ : ℝ, 0 < h₀ ∧ h₀ < h₁ ∧ h₁ < 1 ∧
      ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ t, 0 ≤ η t) ∧
        (∀ t ∉ Icc l u, η t = 0) ∧ (∀ t ∈ Icc h₀ h₁, η t = 1) := by
  let c := (l + u) / 2
  let r := (u - l) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  let E : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  have h₁ : l < c - r := by dsimp [c, r]; linarith
  have h₂ : c + r < u := by dsimp [c, r]; linarith
  refine ⟨c - r / 2, c + r / 2, by linarith, by linarith, by linarith,
    E, E.contDiff, E.hasCompactSupport, E.nonneg', ?_, ?_⟩
  · intro t ht
    apply E.zero_of_le_dist
    change r ≤ dist t c
    rw [Real.dist_eq]
    by_contra! hn
    apply ht
    have H := abs_lt.mp hn
    exact ⟨by linarith, by linarith⟩
  · intro t ht
    apply E.one_of_mem_closedBall
    change dist t c ≤ r / 2
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

end VenRateUpper

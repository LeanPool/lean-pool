/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.PathConnected

/-!
# Moving an entry curve into the interior of a disc

For the VI (3.6) application in XII (3.2), pages 247--248,
region paths must avoid the surface boundary between their ends.
In unit-disc coordinates, move each point a small distance radially
inward. The distance to the complement of the open region controls
the move. Multiplying this distance by the time parameter fixes the
initial point, even when that point is outside the open region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric

private theorem exists_continuous_safe_radius
    {O : Set EuclideanPlane} (hO : IsOpen O) :
    ∃ ε : EuclideanPlane → ℝ, Continuous ε ∧
      (∀ z, 0 ≤ ε z ∧ ε z ≤ 1 / 2) ∧
      ∀ z ∈ O, 0 < ε z ∧ ∀ w, dist w z ≤ ε z → w ∈ O := by
  by_cases hempty : Oᶜ = ∅
  · refine ⟨fun _ => 1 / 2, continuous_const, fun _ => ⟨by norm_num, le_rfl⟩, ?_⟩
    intro z _
    refine ⟨by norm_num, fun w _ => ?_⟩
    by_contra hw
    exact Set.notMem_empty w (hempty ▸ hw)
  · have hne : Oᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    let ε : EuclideanPlane → ℝ := fun z => min (1 / 2) (infDist z Oᶜ / 2)
    have hc : Continuous ε := continuous_const.min ((continuous_infDist_pt Oᶜ).div_const 2)
    refine ⟨ε, hc, fun z => ⟨le_min (by norm_num) (div_nonneg infDist_nonneg (by norm_num)),
      min_le_left _ _⟩, ?_⟩
    intro z hz
    have hd : 0 < infDist z Oᶜ := (infDist_pos_iff_notMem_closure hne).mp (by
      rw [hO.isClosed_compl.closure_eq]
      exact not_not.mpr hz)
    have hepos : 0 < ε z := lt_min (by norm_num) (half_pos hd)
    refine ⟨hepos, ?_⟩
    intro w hw
    by_contra hwO
    have hbound := infDist_le_dist_of_mem (x := z) (s := Oᶜ) (y := w) hwO
    have hsmall : ε z < infDist z Oᶜ := (min_le_right _ _).trans_lt (half_lt_self hd)
    rw [dist_comm z w] at hbound
    exact (hw.trans_lt hsmall).not_ge hbound

/-- An entry curve in a relatively open part of the closed unit disc
can be moved radially inward while fixing its initial point. -/
theorem exists_interior_disc_entry
    {O : Set EuclideanPlane} (hO : IsOpen O) (f : C(unitInterval, ClosedUnitDisc))
    (hfO : ∀ t : unitInterval, 0 < t.val → (f t).val ∈ O) :
    ∃ g : C(unitInterval, ClosedUnitDisc), g 0 = f 0 ∧
      ∀ t : unitInterval, 0 < t.val → (g t).val ∈ O ∧ ‖(g t).val‖ < 1 := by
  obtain ⟨ε, hεc, hε, hεO⟩ := exists_continuous_safe_radius hO
  let ρ : unitInterval → ℝ := fun t => t.val * ε (f t).val
  have hρ : ∀ t, 0 ≤ ρ t ∧ ρ t ≤ ε (f t).val ∧ ρ t ≤ 1 / 2 := by
    intro t
    have hle : ρ t ≤ ε (f t).val := mul_le_of_le_one_left (hε _).1 t.property.2
    exact ⟨mul_nonneg t.property.1 (hε _).1, hle, hle.trans (hε _).2⟩
  have hfN : ∀ t, ‖(f t).val‖ ≤ 1 := fun t => mem_closedBall_zero_iff.mp (f t).property
  let a : unitInterval → EuclideanPlane := fun t => (1 - ρ t) • (f t).val
  have haN : ∀ t, ‖a t‖ ≤ 1 - ρ t := by
    intro t
    have hcoef : 0 ≤ 1 - ρ t := by linarith [(hρ t).2.2]
    simpa only [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, mul_one] using
      mul_le_mul_of_nonneg_left (hfN t) hcoef
  have haD : ∀ t, a t ∈ ClosedUnitDisc := by
    intro t
    apply mem_closedBall_zero_iff.mpr
    exact (haN t).trans (sub_le_self _ (hρ t).1)
  let g : C(unitInterval, ClosedUnitDisc) := ⟨fun t => ⟨a t, haD t⟩, by
    apply Continuous.subtype_mk
    dsimp only [a, ρ]
    exact (continuous_const.sub (continuous_subtype_val.mul
      (hεc.comp (continuous_subtype_val.comp f.continuous)))).smul
      (continuous_subtype_val.comp f.continuous)⟩
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    change a 0 = (f 0).val
    simp only [a, ρ, Icc.coe_zero, zero_mul, sub_zero, one_smul]
  · intro t ht
    have hpos : 0 < ρ t := mul_pos ht (hεO _ (hfO t ht)).1
    have hdist : dist (a t) (f t).val ≤ ε (f t).val := by
      have hdiff : a t - (f t).val = -(ρ t) • (f t).val := by
        dsimp only [a]
        rw [sub_smul, one_smul, sub_sub_cancel_left, neg_smul]
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hρ t).1]
      exact (mul_le_of_le_one_right (hρ t).1 (hfN t)).trans (hρ t).2.1
    exact ⟨(hεO _ (hfO t ht)).2 _ hdist, (haN t).trans_lt (sub_lt_self 1 hpos)⟩


/-- Move the interior of a disc curve off the disc boundary, keeping
both endpoints fixed and staying in its prescribed open set. -/
theorem exists_interior_disc_curve
    {O : Set EuclideanPlane} (hO : IsOpen O) (f : C(unitInterval, ClosedUnitDisc))
    (hfO : ∀ t : unitInterval, 0 < t.val → t.val < 1 → (f t).val ∈ O) :
    ∃ g : C(unitInterval, ClosedUnitDisc), g 0 = f 0 ∧ g 1 = f 1 ∧
      ∀ t : unitInterval, 0 < t.val → t.val < 1 → (g t).val ∈ O ∧ ‖(g t).val‖ < 1 := by
  obtain ⟨ε, hεc, hε, hεO⟩ := exists_continuous_safe_radius hO
  let ρ : unitInterval → ℝ := fun t => (t.val * (1 - t.val)) * ε (f t).val
  have hρ : ∀ t, 0 ≤ ρ t ∧ ρ t ≤ ε (f t).val ∧ ρ t ≤ 1 / 2 := by
    intro t
    have hc0 : 0 ≤ t.val * (1 - t.val) := mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)
    have hc1 : t.val * (1 - t.val) ≤ 1 := by nlinarith [t.property.1, t.property.2]
    have hle : ρ t ≤ ε (f t).val := mul_le_of_le_one_left (hε _).1 hc1
    exact ⟨mul_nonneg hc0 (hε _).1, hle, hle.trans (hε _).2⟩
  have hfN : ∀ t, ‖(f t).val‖ ≤ 1 := fun t => mem_closedBall_zero_iff.mp (f t).property
  let a : unitInterval → EuclideanPlane := fun t => (1 - ρ t) • (f t).val
  have haN : ∀ t, ‖a t‖ ≤ 1 - ρ t := by
    intro t
    have hcoef : 0 ≤ 1 - ρ t := by linarith [(hρ t).2.2]
    simpa only [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, mul_one] using
      mul_le_mul_of_nonneg_left (hfN t) hcoef
  have haD : ∀ t, a t ∈ ClosedUnitDisc := by
    intro t
    apply mem_closedBall_zero_iff.mpr
    exact (haN t).trans (sub_le_self _ (hρ t).1)
  let g : C(unitInterval, ClosedUnitDisc) := ⟨fun t => ⟨a t, haD t⟩, by
    apply Continuous.subtype_mk
    dsimp only [a, ρ]
    fun_prop⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change a 0 = (f 0).val
    simp only [a, ρ, Icc.coe_zero, zero_mul, sub_zero, one_smul]
  · apply Subtype.ext
    change a 1 = (f 1).val
    simp only [a, ρ, Icc.coe_one, sub_self, mul_zero, zero_mul, sub_zero, one_smul]
  · intro t ht ht1
    have hpos : 0 < ρ t := mul_pos (mul_pos ht (sub_pos.mpr ht1)) (hεO _ (hfO t ht ht1)).1
    have hdist : dist (a t) (f t).val ≤ ε (f t).val := by
      have hdiff : a t - (f t).val = -(ρ t) • (f t).val := by
        dsimp only [a]
        rw [sub_smul, one_smul, sub_sub_cancel_left, neg_smul]
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hρ t).1]
      exact (mul_le_of_le_one_right (hρ t).1 (hfN t)).trans (hρ t).2.1
    exact ⟨(hεO _ (hfO t ht ht1)).2 _ hdist, (haN t).trans_lt (sub_lt_self 1 hpos)⟩

end GraphMinor.GM12

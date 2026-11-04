/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyMoments
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Positivity

/-! # Comparison between the maximum and integral moments

The maximum window is covered by two adjacent windows. Integrating this
cover over one unit of translation proves the lower half of (2.6) in the
weighted Hooley mean argument, with the sharp factor `2^(q-1)` used there.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory

theorem divisorWindow_le_adjacent (n : ℕ) {u v : ℝ}
    (hv₀ : u - 1 ≤ v) (hvu : v ≤ u) :
    divisorWindow n u ≤ divisorWindow n v + divisorWindow n (v + 1) := by
  classical
  let S := n.divisors.filter (fun d : ℕ => v < Real.log d ∧ Real.log d ≤ v + 1)
  let T := n.divisors.filter (fun d : ℕ => v + 1 < Real.log d ∧ Real.log d ≤ (v + 1) + 1)
  calc
    _ ≤ (S ∪ T).card := by
      apply card_le_card
      intro d hd
      obtain ⟨hdn, hdu, hdu₁⟩ := mem_filter.mp hd
      by_cases hdv : Real.log d ≤ v + 1
      · exact mem_union_left T (mem_filter.mpr ⟨hdn, by linarith, hdv⟩)
      · exact mem_union_right S (mem_filter.mpr ⟨hdn, lt_of_not_ge hdv, by linarith⟩)
    _ ≤ S.card + T.card := card_union_le S T

/-- A window value is bounded by the moment on its two-unit neighborhood. -/
theorem hooleyWindow_pow_le_localIntegral (n : ℕ) {q : ℕ} (hq : 0 < q) (u : ℝ) :
    hooleyWindow n u ^ q ≤ (2 : ℝ) ^ (q - 1) *
      ∫ v in (u - 1)..(u + 1), hooleyWindow n v ^ q := by
  have hf := integrable_hooleyWindow_pow n hq
  have hg := hf.comp_add_right 1
  have hcover (v : ℝ) (hv : v ∈ Set.Icc (u - 1) u) :
      hooleyWindow n u ^ q ≤
        (2 : ℝ) ^ (q - 1) * (hooleyWindow n v ^ q + hooleyWindow n (v + 1) ^ q) := by
    have H : hooleyWindow n u ≤ hooleyWindow n v + hooleyWindow n (v + 1) := by
      unfold hooleyWindow
      exact_mod_cast divisorWindow_le_adjacent n hv.1 hv.2
    exact (pow_le_pow_left₀ (hooleyWindow_nonneg n u) H q).trans
      (add_pow_le (hooleyWindow_nonneg n v) (hooleyWindow_nonneg n (v + 1)) q)
  have H := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    intervalIntegrable_const ((hf.add hg).const_mul ((2 : ℝ) ^ (q - 1))).intervalIntegrable hcover
  have Hidentity :
      (∫ v in (u - 1)..u,
        (2 : ℝ) ^ (q - 1) * (hooleyWindow n v ^ q + hooleyWindow n (v + 1) ^ q)) =
      (2 : ℝ) ^ (q - 1) * ∫ v in (u - 1)..(u + 1), hooleyWindow n v ^ q := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hf.intervalIntegrable hg.intervalIntegrable,
      intervalIntegral.integral_comp_add_right (fun v => hooleyWindow n v ^ q) 1,
      sub_add_cancel,
      intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable]
  simp only [Pi.add_apply] at H
  rw [Hidentity, intervalIntegral.integral_const,
    show u - (u - 1) = 1 by ring, one_smul] at H
  exact H

/-- Each maximum window is bounded by the integral moment. This argument
also handles the zero integer and does not assume the maximum is unique. -/
theorem hooleyDelta_pow_le_moment (n : ℕ) {q : ℕ} (hq : 0 < q) :
    (hooleyDelta n : ℝ) ^ q ≤ (2 : ℝ) ^ (q - 1) * hooleyMoment q n := by
  obtain ⟨u, hu⟩ := hooleyDelta_attained n
  have H := hooleyWindow_pow_le_localIntegral n hq u
  have Heq : hooleyWindow n u = (hooleyDelta n : ℝ) := by
    exact congrArg (fun m : ℕ => (m : ℝ)) hu
  rw [Heq] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [intervalIntegral.integral_of_le (by linarith : u - 1 ≤ u + 1)]
  exact setIntegral_le_integral (integrable_hooleyWindow_pow n hq)
    (Filter.Eventually.of_forall fun v => pow_nonneg (hooleyWindow_nonneg n v) q)

theorem card_divisors_le_hooleyMoment (n : ℕ) {q : ℕ} (hq : 0 < q) :
    (n.divisors.card : ℝ) ≤ hooleyMoment q n := by
  have H := integral_mono (integrable_hooleyWindow n) (integrable_hooleyWindow_pow n hq)
    (fun u => show hooleyWindow n u ≤ hooleyWindow n u ^ q from by
      by_cases h : divisorWindow n u = 0
      · simp [hooleyWindow, h, hq.ne']
      · apply le_self_pow₀ _ hq.ne'
        change (1 : ℝ) ≤ (divisorWindow n u : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
  simpa only [integral_hooleyWindow, hooleyMoment] using H

theorem hooleyMoment_pos {n q : ℕ} (hn : n ≠ 0) (hq : 0 < q) :
    0 < hooleyMoment q n := by
  have H : 0 < n.divisors.card := card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  exact (show (0 : ℝ) < n.divisors.card by exact_mod_cast H).trans_le
    (card_divisors_le_hooleyMoment n hq)

end NairTenenbaum

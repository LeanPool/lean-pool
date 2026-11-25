/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/


module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Positive cyclic order on the circle
-/

@[expose] public section

namespace GraphMinor.CircleOrder

/-- The positive cyclic order of three points of the circle: going around from `a` in the positive
direction, we reach `b` before `c`, and both before coming back to `a`. -/
def CircleCyclic (a b c : Circle) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 2 * Real.pi ∧ b = a * Circle.exp s ∧ c = a * Circle.exp t

/-- Each point of the circle other than `1` has an angle strictly between `0` and `2π`. -/
theorem exists_angle {z : Circle} (hz : z ≠ 1) :
    ∃ s : ℝ, 0 < s ∧ s < 2 * Real.pi ∧ z = Circle.exp s := by
  have harg : Circle.exp (Complex.arg z) = z := Circle.exp_arg z
  have h0 : Complex.arg z ≠ 0 := fun h ↦ hz (by rw [← harg, h, Circle.exp_zero])
  have hlo := Complex.neg_pi_lt_arg (z : ℂ)
  have hhi := Complex.arg_le_pi (z : ℂ)
  have hpi := Real.pi_pos
  rcases lt_or_gt_of_ne h0 with h | h
  · refine ⟨Complex.arg z + 2 * Real.pi, by linarith, by linarith, ?_⟩
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one, harg]
  · exact ⟨Complex.arg z, h, by linarith, harg.symm⟩

/-- Three distinct points of the circle occur in one of the two cyclic orders. -/
theorem circleCyclic_or {a b c : Circle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircleCyclic a b c ∨ CircleCyclic a c b := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_angle (z := a⁻¹ * b) (fun h ↦ hab (by
    rw [inv_mul_eq_one] at h
    exact h))
  obtain ⟨t, ht0, ht1, ht⟩ := exists_angle (z := a⁻¹ * c) (fun h ↦ hac (by
    rw [inv_mul_eq_one] at h
    exact h))
  have hb : b = a * Circle.exp s := by rw [← hs]; simp
  have hc : c = a * Circle.exp t := by rw [← ht]; simp
  rcases lt_trichotomy s t with h | h | h
  · exact Or.inl ⟨s, t, hs0, h, ht1, hb, hc⟩
  · exact absurd (by rw [hb, hc, h]) hbc
  · exact Or.inr ⟨t, s, ht0, h, hs1, hc, hb⟩

theorem exp_eq_of_angles {s t : ℝ} (hs : 0 < s) (hs' : s < 2 * Real.pi) (ht : 0 < t)
    (ht' : t < 2 * Real.pi) (h : Circle.exp s = Circle.exp t) : s = t := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h
  have hpi := Real.pi_pos
  have h1 : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
  have h2 : -(2 * Real.pi) < (m : ℝ) * (2 * Real.pi) := by linarith
  have h3 : (m : ℝ) < 1 := by nlinarith
  have h4 : (-1 : ℝ) < m := by nlinarith
  have h5 : m = 0 := by
    have h6 : m < 1 := by exact_mod_cast h3
    have h7 : -1 < m := by exact_mod_cast h4
    omega
  rw [hm, h5]
  simp

/-- Three points of the circle do not lie in both cyclic orders. -/
theorem not_circleCyclic_both {a b c : Circle} (h : CircleCyclic a b c)
    (h' : CircleCyclic a c b) : False := by
  obtain ⟨s, t, hs, hst, ht, hb, hc⟩ := h
  obtain ⟨s', t', hs', hst', ht', hc', hb'⟩ := h'
  have h1 : Circle.exp s = Circle.exp t' := mul_left_cancel (hb.symm.trans hb')
  have h2 : Circle.exp t = Circle.exp s' := mul_left_cancel (hc.symm.trans hc')
  have hpos : 0 < t' := hs'.trans hst'
  have hpos' : 0 < t := hs.trans hst
  have e1 := exp_eq_of_angles hs (hst.trans ht) hpos ht' h1
  have e2 := exp_eq_of_angles hpos' ht hs' (hst'.trans ht') h2
  linarith

theorem circleCyclic_inv {a b c : Circle} (h : CircleCyclic a b c) :
    CircleCyclic a⁻¹ c⁻¹ b⁻¹ := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := h
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi - t, 2 * Real.pi - s, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [Circle.exp_sub, Circle.exp_two_pi]
    simp [mul_comm]
  · rw [Circle.exp_sub, Circle.exp_two_pi]
    simp [mul_comm]

theorem exists_angle_of_circle (a : Circle) : ∃ α : ℝ, a = Circle.exp α :=
  ⟨Complex.arg a, (Circle.exp_arg a).symm⟩

end GraphMinor.CircleOrder

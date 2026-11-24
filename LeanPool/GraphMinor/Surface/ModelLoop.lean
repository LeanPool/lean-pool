/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelDisc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The boundary loop of the upper half of a model surface

`axS` runs along the real axis so that the circles are crossed at the same speed. `angL` is the
angle of a loop on
the unit circle: it runs along the axis and then through the point at infinity. The polygon lemma
gives a map of the
unit disc with these boundary values (`exists_modelPoly`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

open scoped OnePoint

/-- The speed along the axis. -/
noncomputable def axPhi (t : ℝ) : ℝ := 3 * t / 2 - 1 + (1 - Real.cos (Real.pi * t)) / 4

/-- The position on the axis. -/
noncomputable def axS (y : ℝ) : ℝ := axPhi (y - 1)

theorem continuous_axPhi : Continuous axPhi := by
  unfold axPhi
  fun_prop

theorem continuous_axS : Continuous axS := continuous_axPhi.comp (by fun_prop)

theorem strictMono_axPhi : StrictMono axPhi := by
  intro x y h
  have h1 := Real.abs_cos_sub_cos_le (Real.pi * x) (Real.pi * y)
  have h2 : |Real.pi * x - Real.pi * y| = Real.pi * (y - x) := by
    rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos, abs_sub_comm, abs_of_pos (sub_pos.mpr h)]
  rw [h2] at h1
  have h3 := (abs_le.mp h1).1
  have h4 := Real.pi_lt_four
  unfold axPhi
  nlinarith [sub_pos.mpr h]

theorem strictMono_axS : StrictMono axS := fun _ _ h => strictMono_axPhi (by linarith)

theorem axPhi_zero : axPhi 0 = -1 := by norm_num [axPhi]

theorem axPhi_one : axPhi 1 = 1 := by norm_num [axPhi]

theorem axPhi_neg (t : ℝ) : axPhi (1 - t) = - axPhi t := by
  unfold axPhi
  rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.cos_pi_sub]
  ring

theorem axPhi_period (t : ℝ) (k : ℕ) : axPhi (t + 2 * k) = axPhi t + 3 * k := by
  unfold axPhi
  rw [show Real.pi * (t + 2 * k) = Real.pi * t + k * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]
  ring

theorem axS_hole (k : ℕ) (t : ℝ) : axS (2 * k + 1 + t) = 3 * k + axPhi t := by
  unfold axS
  rw [show (2 * (k : ℝ) + 1 + t - 1) = t + 2 * k by ring, axPhi_period]
  ring

theorem axS_even (k : ℕ) : axS (2 * k) = 3 * k - 2 := by
  have h : (2 * (k : ℝ) - 1) = -1 + 2 * k := by ring
  unfold axS
  rw [h, axPhi_period]
  have : axPhi (-1) = -2 := by norm_num [axPhi]
  rw [this]
  ring

theorem axS_odd (k : ℕ) : axS (2 * k + 1) = 3 * k - 1 := by
  have := axS_hole k 0
  rw [add_zero, axPhi_zero] at this
  rw [this]
  ring

/-- The height on the segments of the axis is zero. -/
theorem hgt_seg {n k : ℕ} {y : ℝ} (h0 : 2 * (k : ℝ) ≤ y) (h1 : y ≤ 2 * k + 1) : hgt n (axS y) = 0
  := by
  have h2 : 3 * (k : ℝ) - 2 ≤ axS y := by rw [← axS_even]; exact strictMono_axS.monotone h0
  have h3 : axS y ≤ 3 * (k : ℝ) - 1 := by rw [← axS_odd]; exact strictMono_axS.monotone h1
  refine hgt_eq_zero fun i _ => ?_
  rcases lt_trichotomy i k with h | rfl | h
  · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
    rw [le_abs]
    left
    linarith
  · rw [le_abs]
    right
    linarith
  · have : (k : ℝ) + 1 ≤ i := by exact_mod_cast h
    rw [le_abs]
    right
    linarith

theorem hgt_large {n : ℕ} {x : ℝ} (h : 3 * (n : ℝ) - 2 ≤ x) : hgt n x = 0 := by
  refine hgt_eq_zero fun i hi => ?_
  have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  rw [le_abs]
  left
  linarith

theorem hgt_small {n : ℕ} {x : ℝ} (h : x ≤ -2) : hgt n x = 0 := by
  refine hgt_eq_zero fun i _ => ?_
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [le_abs]
  right
  linarith

/-- The angle of the loop. -/
noncomputable def angL (n : ℕ) (y : ℝ) : ℝ :=
  if y ≤ 2 * n then angT (axS y)
  else angT (axS (2 * n)) + (y - 2 * n) / 2 * (2 * Real.pi + angT (axS 0) - angT (axS (2 * n)))

theorem angL_le {n : ℕ} {y : ℝ} (h : y ≤ 2 * n) : angL n y = angT (axS y) := ite_eq_left h

theorem angL_ge {n : ℕ} {y : ℝ} (h : 2 * (n : ℝ) ≤ y) :
    angL n y = angT (axS (2 * n)) + (y - 2 * n) / 2 * (2 * Real.pi + angT (axS 0) - angT (axS
      (2 * n))) := by
  rcases eq_or_lt_of_le h with rfl | h
  · simp [angL]
  · exact ite_eq_right (not_le.mpr h)

theorem continuous_angL (n : ℕ) : Continuous (angL n) := by
  refine Continuous.if_le (continuous_angT.comp continuous_axS) ?_ continuous_id continuous_const
    fun y hy => ?_
  · fun_prop
  · have : y = 2 * n := hy
    simp [this]

theorem angL_gap (n : ℕ) : 0 < 2 * Real.pi + angT (axS 0) - angT (axS (2 * n)) := by
  have h1 := (angT_mem (axS 0)).1
  have h2 := (angT_mem (axS (2 * n))).2
  linarith

theorem strictMono_angL (n : ℕ) : StrictMono (angL n) := by
  have hg := angL_gap n
  intro x y h
  rcases le_total y (2 * n) with h1 | h1
  · rw [angL_le h1, angL_le (h.le.trans h1)]
    exact strictMono_angT (strictMono_axS h)
  rcases le_total x (2 * n) with h2 | h2
  · rw [angL_le h2, angL_ge h1]
    have h3 : angT (axS x) ≤ angT (axS (2 * n)) := strictMono_angT.monotone
      (strictMono_axS.monotone h2)
    rcases eq_or_lt_of_le h1 with h4 | h4
    · have h5 : angT (axS x) < angT (axS (2 * n)) := strictMono_angT (strictMono_axS (by linarith))
      rw [← h4]
      simpa using h5
    · have : 0 < (y - 2 * n) / 2 * (2 * Real.pi + angT (axS 0) - angT (axS (2 * n))) :=
        mul_pos (by linarith) hg
      linarith
  · rw [angL_ge h1, angL_ge h2]
    have : (x - 2 * n) / 2 < (y - 2 * n) / 2 := by linarith
    nlinarith

theorem angL_zero (n : ℕ) : angL n 0 = angT (axS 0) := angL_le (by positivity)

theorem angL_top (n : ℕ) : angL n ((2 * n + 2 : ℕ) : ℝ) = angT (axS 0) + 2 * Real.pi := by
  have : 2 * (n : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by push_cast; linarith
  rw [angL_ge this]
  push_cast
  ring

theorem cis'_injOn_Ico (a : ℝ) : InjOn cis' (Ico a (a + 2 * Real.pi)) := by
  intro x hx y hy he
  have h1 : Circle.exp x = Circle.exp y := Circle.ext (by simpa [cis', Circle.coe_exp] using he)
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h1
  have hpi := Real.pi_pos
  have h3 : (k : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by nlinarith [hx.2, hy.1]
  have h4 : (-1 : ℝ) * (2 * Real.pi) < k * (2 * Real.pi) := by nlinarith [hx.1, hy.2]
  have h5 : (k : ℝ) < 1 := lt_of_mul_lt_mul_right h3 (by positivity)
  have h6 : (-1 : ℝ) < k := lt_of_mul_lt_mul_right h4 (by positivity)
  have h7 : k < 1 := by exact_mod_cast h5
  have h8 : -1 < k := by exact_mod_cast h6
  obtain rfl : k = 0 := by omega
  simpa using hk

theorem exists_cis'_angle (a : ℝ) {z : ℂ} (hz : ‖z‖ = 1) : ∃ x ∈ Icc a (a + 2 * Real.pi), cis' x
  = z := by
  have ha : ∃ θ, cis' θ = z := ⟨_, cis'_arg hz⟩
  obtain ⟨θ, rfl⟩ := ha
  have hpi := Real.pi_pos
  let k : ℤ := ⌈(a - θ) / (2 * Real.pi)⌉
  have h1 : (a - θ) / (2 * Real.pi) ≤ k := Int.le_ceil _
  have h2 : (k : ℝ) < (a - θ) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at h1
  have h3 : (k : ℝ) * (2 * Real.pi) < a - θ + 2 * Real.pi := by
    have := mul_lt_mul_of_pos_right h2 (show 0 < 2 * Real.pi by positivity)
    rw [add_mul, div_mul_cancel₀ _ (by positivity)] at this
    linarith
  refine ⟨θ + k * (2 * Real.pi), ⟨by linarith, by linarith⟩, ?_⟩
  simp only [cis']
  push_cast
  rw [add_mul, Complex.exp_add]
  have : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I) = 1 := by
    rw [show (k : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I = k * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [this, mul_one]

theorem cis'_add_two_pi (x : ℝ) : cis' (x + 2 * Real.pi) = cis' x := cis'_period x

/-- The polygon map of the upper half. -/
theorem exists_modelPoly (n : ℕ) :
    ∃ Φ Φ' : ℂ → ℂ, BdMatch (closedBall 0 1) (closedBall 0 1) Φ Φ' ∧
      ∀ x ∈ Icc (0 : ℝ) (2 * n + 2 : ℕ), Φ (per (2 * n + 2) x) = cis' (angL n x) := by
  have hmono := strictMono_angL n
  refine exists_polygon_map isClosedDisc_closedBall.1 (by omega) (β := fun x => cis' (angL n x))
    (continuous_cis'.comp (continuous_angL n)).continuousOn ?_ ?_ ?_
  · intro x hx y hy he
    have h1 (z : ℝ) (hz : z ∈ Ico 0 ((2 * n + 2 : ℕ) : ℝ)) :
        angL n z ∈ Ico (angT (axS 0)) (angT (axS 0) + 2 * Real.pi) := by
      refine ⟨?_, ?_⟩
      · rw [← angL_zero n]
        exact hmono.monotone hz.1
      · rw [← angL_top n]
        exact hmono hz.2
    exact hmono.injective (cis'_injOn_Ico _ (h1 x hx) (h1 y hy) he)
  · rw [angL_zero, angL_top, cis'_add_two_pi]
  · rw [isClosedDisc_closedBall.2]
    ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      exact cis'_mem_sphere _
    · intro hz
      obtain ⟨θ, hθ, rfl⟩ := exists_cis'_angle (angT (axS 0)) (mem_sphere_zero_iff_norm.mp hz)
      have hiv := intermediate_value_Icc (a := 0) (b := ((2 * n + 2 : ℕ) : ℝ)) (by positivity)
        (continuous_angL n).continuousOn
      rw [angL_zero, angL_top] at hiv
      obtain ⟨x, hx, rfl⟩ := hiv hθ
      exact ⟨x, hx, rfl⟩

end GraphMinor.Surface

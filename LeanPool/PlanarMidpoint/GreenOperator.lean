/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum

/-! Coarse Dirichlet estimates for vector-valued curves on the unit interval. -/

@[expose] public section
namespace PlanarMidpoint

open Set MeasureTheory
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Bounded acceleration controls velocity relative to its endpoint secant. -/
theorem velocity_secant_bound (x v a : ℝ → V) (M : ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖v t - (x 1 - x 0)‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (a 0)).trans (ha 0 (by norm_num))
  have hvc : ContinuousOn v (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hv s hs).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable v volume 0 1 :=
    hvc.intervalIntegrable_of_Icc (by norm_num)
  have hFTC : (∫ s in (0 : ℝ)..1, v s) = x 1 - x 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hvi
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
  have hid : (∫ s in (0 : ℝ)..1, (v t - v s)) = v t - (x 1 - x 0) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hvi,
      intervalIntegral.integral_const, hFTC]
    simp
  rw [← hid]
  have hbound : ∀ s ∈ Ι (0 : ℝ) 1, ‖v t - v s‖ ≤ M := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      have hs'' : s ∈ Ioc (0 : ℝ) 1 := by simpa using hs
      exact ⟨le_of_lt hs''.1, hs''.2⟩
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu ↦ (hv u hu).hasDerivWithinAt) ha (convex_Icc (0 : ℝ) 1) hs' ht
    have hdist : ‖t - s‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1, hs'.2], by linarith [ht.2, hs'.1]⟩
    exact hmean.trans ((mul_le_mul_of_nonneg_left hdist hM).trans_eq (mul_one M))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- The corresponding position differs from its affine chord by at most `M`. -/
theorem position_chord_bound (x v a : ℝ → V) (M : ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖x t - ((1 - t) • x 0 + t • x 1)‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (a 0)).trans (ha 0 (by norm_num))
  let y : ℝ → V := fun s ↦ x s - (x 0 + s • (x 1 - x 0))
  have hy : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt y (v s - (x 1 - x 0)) (Icc (0 : ℝ) 1) s := by
    intro s hs
    simpa [y] using ((hx s hs).fun_sub ((hasDerivAt_id s).smul_const (x 1 - x 0) |>.const_add (x
        0))).hasDerivWithinAt
  have hb : ∀ s ∈ Icc (0 : ℝ) 1, ‖v s - (x 1 - x 0)‖ ≤ M :=
    fun s hs ↦ velocity_secant_bound x v a M hx hv ha s hs
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hy hb
    (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ht
  have hform : y t - y 0 = x t - ((1 - t) • x 0 + t • x 1) := by
    dsimp [y]
    module
  rw [hform] at hmean
  have hdist : ‖t - 0‖ ≤ (1 : ℝ) := by simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  exact hmean.trans ((mul_le_mul_of_nonneg_left hdist hM).trans_eq (mul_one M))

/-- Zero endpoint data convert the secant estimate to a velocity estimate. -/
theorem dirichlet_velocity_bound (x v a : ℝ → V) (M : ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t‖ ≤ M)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖v t‖ ≤ M := by
  simpa only [hx0, hx1, sub_self, sub_zero] using
    velocity_secant_bound x v a M hx hv ha t ht

/-- Zero endpoint data convert the chord estimate to a position estimate. -/
theorem dirichlet_position_bound (x v a : ℝ → V) (M : ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (a t) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖a t‖ ≤ M)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖x t‖ ≤ M := by
  simpa only [hx0, hx1, smul_zero, add_zero, sub_zero] using
    position_chord_bound x v a M hx hv ha t ht

/-- A curve with zero acceleration and zero endpoints vanishes identically. -/
theorem dirichlet_unique (x v : ℝ → V)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v 0 t)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x t = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm
    (dirichlet_position_bound x v (fun _ ↦ 0) 0 hx hv (by simp) hx0 hx1 t ht)
    (norm_nonneg _)

end PlanarMidpoint

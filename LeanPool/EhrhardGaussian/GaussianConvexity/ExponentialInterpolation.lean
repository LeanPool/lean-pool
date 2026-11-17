/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The two-crossing interpolation algebra

For the three-exponential comparison in FMP25 §3, dividing by the lowest
exponential and setting `u = exp(d t)` reduces the sign calculation to the
concavity of `u ↦ u^θ`, `0 ≤ θ ≤ 1`. The explicit chord has the required sign
on and outside its crossing interval. This avoids the compressed induction and
sign-switch assertion in FMP25 Appendix A. It does not assume that the crossing
interval of two laws is nonempty or bounded.
-/

@[expose] public section

open Set

namespace EhrhardGaussian.GaussianConvexity

/-- A concave function lies above its chord inside the interpolation interval. -/
theorem chord_le_of_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {u v x : ℝ} (hu : u ∈ s) (hv : v ∈ s) (huv : u < v) (hx : x ∈ Icc u v) :
    ((v - x) * f u + (x - u) * f v) / (v - u) ≤ f x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hux
  · simp only [sub_self, zero_mul, add_zero,
      mul_div_cancel_left₀ _ (sub_ne_zero.mpr huv.ne'), le_refl]
  rcases eq_or_lt_of_le hx.2 with rfl | hxv
  · simp only [sub_self, zero_mul, zero_add,
      mul_div_cancel_left₀ _ (sub_ne_zero.mpr huv.ne'), le_refl]
  have h := hf.neg.secant_mono_aux1 hu hv hux hxv
  simp only [Pi.neg_apply] at h
  apply (div_le_iff₀ (sub_pos.mpr huv)).mpr
  nlinarith only [h]

/-- To the left of the interval a concave function lies below the extrapolated chord. -/
theorem le_chord_of_le_left_of_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {u v x : ℝ} (hx : x ∈ s) (hv : v ∈ s) (huv : u < v) (hxu : x ≤ u) :
    f x ≤ ((v - x) * f u + (x - u) * f v) / (v - u) := by
  rcases eq_or_lt_of_le hxu with rfl | hxu
  · simp only [sub_self, zero_mul, add_zero,
      mul_div_cancel_left₀ _ (sub_ne_zero.mpr huv.ne'), le_refl]
  have h := hf.neg.secant_mono_aux1 hx hv hxu huv
  simp only [Pi.neg_apply] at h
  apply (le_div_iff₀ (sub_pos.mpr huv)).mpr
  nlinarith only [h]

/-- To the right of the interval a concave function lies below the extrapolated chord. -/
theorem le_chord_of_right_le_of_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {u v x : ℝ} (hu : u ∈ s) (hx : x ∈ s) (huv : u < v) (hvx : v ≤ x) :
    f x ≤ ((v - x) * f u + (x - u) * f v) / (v - u) := by
  rcases eq_or_lt_of_le hvx with rfl | hvx
  · simp only [sub_self, zero_mul, zero_add,
      mul_div_cancel_left₀ _ (sub_ne_zero.mpr huv.ne'), le_refl]
  have h := hf.neg.secant_mono_aux1 hu hx huv hvx
  simp only [Pi.neg_apply] at h
  apply (le_div_iff₀ (sub_pos.mpr huv)).mpr
  nlinarith only [h]

/-- The power interpolant has nonnegative difference inside and nonpositive difference outside. -/
theorem rpow_chord_sign {θ u v x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : 0 ≤ u) (huv : u < v) (hx : 0 ≤ x) :
    (x ∈ Icc u v → 0 ≤ x ^ θ - ((v - x) * u ^ θ + (x - u) * v ^ θ) / (v - u)) ∧
    (x ≤ u ∨ v ≤ x → x ^ θ - ((v - x) * u ^ θ + (x - u) * v ^ θ) / (v - u) ≤ 0) := by
  have hf := Real.concaveOn_rpow hθ0 hθ1
  have hv : 0 ≤ v := hu.trans huv.le
  constructor
  · intro hinside
    exact sub_nonneg.mpr (chord_le_of_concave hf hu hv huv hinside)
  · intro houtside
    rcases houtside with hleft | hright
    · exact sub_nonpos.mpr (le_chord_of_le_left_of_concave hf hx hv huv hleft)
    · exact sub_nonpos.mpr (le_chord_of_right_le_of_concave hf hu hx huv hright)

/-- Writing the interpolation chord as a constant plus a linear term gives explicit coefficients. -/
theorem chord_eq_affine (u v U V x : ℝ) :
    ((v - x) * U + (x - u) * V) / (v - u) =
      (v * U - u * V) / (v - u) + (V - U) / (v - u) * x := by
  field_simp
  ring

/-- Normalizing three exponentials produces a power-interpolation difference. -/
theorem three_exponential_factorization (a d θ A B t : ℝ) :
    Real.exp ((a + d * θ) * t) - A * Real.exp (a * t) - B * Real.exp ((a + d) * t) =
      Real.exp (a * t) * ((Real.exp (d * t)) ^ θ - A - B * Real.exp (d * t)) := by
  rw [← Real.exp_mul]
  have hmid : (a + d * θ) * t = a * t + d * t * θ := by ring
  have hhigh : (a + d) * t = a * t + d * t := by ring
  rw [hmid, hhigh, Real.exp_add, Real.exp_add]
  ring

end EhrhardGaussian.GaussianConvexity

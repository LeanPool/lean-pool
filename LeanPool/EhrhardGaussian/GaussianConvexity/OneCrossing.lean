/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cancellation with at most one sign change

Two distinct exponential moments cannot both vanish for a nonzero function
whose sign changes at most once. This disposes of the unbounded crossing sets
in the FMP25 comparison, without assuming finite crossing endpoints.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace EhrhardGaussian.GaussianConvexity

/-- A function of one sign with a vanishing exponentially weighted integral vanishes a.e. -/
theorem ae_eq_zero_of_nonpos_of_exp_integral_eq_zero {f : ℝ → ℝ} {p : ℝ}
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0) (hf : ∀ᶠ t in ae volume, f t ≤ 0) :
    f =ᵐ[volume] 0 := by
  have hnonneg : ∀ᵐ t ∂volume, 0 ≤ -(Real.exp (p * t) * f t) := by
    filter_upwards [hf] with t ht
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ht)
  have hint : ∫ t, -(Real.exp (p * t) * f t) = 0 := by rw [integral_neg, hz, neg_zero]
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi.neg).mp hint
  filter_upwards [heq] with t ht
  have hmul : Real.exp (p * t) * f t = 0 := neg_eq_zero.mp ht
  exact (mul_eq_zero.mp hmul).resolve_left (Real.exp_ne_zero _)

/-- A difference of exponentials factors into a positive factor and a monotone difference. -/
theorem exponential_crossing_factorization (p q c t : ℝ) :
    Real.exp (q * t) - Real.exp ((q - p) * c) * Real.exp (p * t) =
      Real.exp (p * t) * (Real.exp ((q - p) * t) - Real.exp ((q - p) * c)) := by
  have hq : q * t = p * t + (q - p) * t := by ring
  rw [hq, Real.exp_add]
  ring

/-- Two zero exponential moments force a function with a single upward sign change to vanish. -/
theorem ae_eq_zero_of_one_upward_crossing {f : ℝ → ℝ} {p q c : ℝ} (hpq : p < q)
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hj : Integrable (fun t => Real.exp (q * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0)
    (hw : ∫ t, Real.exp (q * t) * f t = 0)
    (hleft : ∀ t, t < c → f t ≤ 0) (hright : ∀ t, c < t → 0 ≤ f t) :
    f =ᵐ[volume] 0 := by
  let K := Real.exp ((q - p) * c)
  let ψ := fun t => Real.exp (q * t) - K * Real.exp (p * t)
  have hfact : ∀ t, ψ t = Real.exp (p * t) *
      (Real.exp ((q - p) * t) - Real.exp ((q - p) * c)) :=
    exponential_crossing_factorization p q c
  have hsign : ∀ t, 0 ≤ ψ t * f t := by
    intro t
    rw [hfact]
    rcases lt_trichotomy t c with ht | rfl | ht
    · have he : Real.exp ((q - p) * t) - Real.exp ((q - p) * c) ≤ 0 :=
        sub_nonpos.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le (sub_pos.mpr hpq).le))
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le he) (hleft t ht)
    · rw [sub_self, mul_zero, zero_mul]
    · have he : 0 ≤ Real.exp ((q - p) * t) - Real.exp ((q - p) * c) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le (sub_pos.mpr hpq).le))
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le he) (hright t ht)
  have hfun : (fun t => ψ t * f t) = fun t =>
      Real.exp (q * t) * f t - K * (Real.exp (p * t) * f t) := by
    funext t
    dsimp [ψ]
    ring
  have hint : Integrable (fun t => ψ t * f t) := by
    rw [hfun]
    exact hj.sub (hi.const_mul K)
  have hzero : ∫ t, ψ t * f t = 0 := by
    rw [hfun, integral_sub hj (hi.const_mul K), integral_const_mul, hz, hw, mul_zero, sub_zero]
  have heq := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hsign) hint).mp hzero
  filter_upwards [heq, volume.ae_ne c] with t ht htc
  have hψ : ψ t ≠ 0 := by
    rw [hfact]
    apply mul_ne_zero (Real.exp_ne_zero _)
    intro he
    have he' := Real.exp_injective (sub_eq_zero.mp he)
    exact htc ((mul_left_cancel₀ (sub_ne_zero.mpr hpq.ne') he'))
  exact (mul_eq_zero.mp ht).resolve_left hψ

/-- The downward sign-change case follows by negating the function. -/
theorem ae_eq_zero_of_one_downward_crossing {f : ℝ → ℝ} {p q c : ℝ} (hpq : p < q)
    (hi : Integrable (fun t => Real.exp (p * t) * f t))
    (hj : Integrable (fun t => Real.exp (q * t) * f t))
    (hz : ∫ t, Real.exp (p * t) * f t = 0)
    (hw : ∫ t, Real.exp (q * t) * f t = 0)
    (hleft : ∀ t, t < c → 0 ≤ f t) (hright : ∀ t, c < t → f t ≤ 0) :
    f =ᵐ[volume] 0 := by
  have hi' : Integrable (fun t => Real.exp (p * t) * -f t) := by
    apply hi.neg.congr
    exact ae_of_all _ fun t => (mul_neg (Real.exp (p * t)) (f t)).symm
  have hj' : Integrable (fun t => Real.exp (q * t) * -f t) := by
    apply hj.neg.congr
    exact ae_of_all _ fun t => (mul_neg (Real.exp (q * t)) (f t)).symm
  have hz' : ∫ t, Real.exp (p * t) * -f t = 0 := by
    simp only [mul_neg, integral_neg, hz, neg_zero]
  have hw' : ∫ t, Real.exp (q * t) * -f t = 0 := by
    simp only [mul_neg, integral_neg, hw, neg_zero]
  have heq := ae_eq_zero_of_one_upward_crossing hpq hi' hj' hz' hw'
    (fun t ht => neg_nonpos.mpr (hleft t ht)) (fun t ht => neg_nonneg.mpr (hright t ht))
  filter_upwards [heq] with t ht
  exact neg_eq_zero.mp ht

end EhrhardGaussian.GaussianConvexity

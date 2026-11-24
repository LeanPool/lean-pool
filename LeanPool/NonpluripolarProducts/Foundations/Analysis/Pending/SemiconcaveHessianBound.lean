/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Hessian bounds from one-sided second differences and plurisubharmonicity

Let `f` be a `C²` function on `ℂⁿ`.

* If `f (z + h) + f (z - h) - 2 f z ≤ K ‖h‖²` for all small `h`, then
  `D²f(z)(v, v) ≤ K ‖v‖²` (second-order Taylor expansion along `t ↦ z ± t v`).
* If moreover the Levi form `(D²f(z)(v,v) + D²f(z)(iv,iv))/4` is nonnegative (e.g. `f`
  plurisubharmonic), then `D²f(z)(v,v) ≥ -D²f(z)(iv,iv) ≥ -K ‖v‖²`, so
  `|D²f(z)(v,v)| ≤ K ‖v‖²`, and by polarization `‖D²f(z)‖ ≤ 2K`.

This is the pointwise core of Błocki, *The complex Monge–Ampère operator in pluripotential
theory*, lecture notes, Proposition 2.3.3.
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- A one-sided second-difference bound near `z` bounds the diagonal of the real Hessian. -/
theorem realHessian_le_of_secondDifference_le {f : ComplexModel n → ℝ}
    (hf : ContDiff ℝ 2 f) {z : ComplexModel n} {K : ℝ}
    (hK : ∀ᶠ h in 𝓝 (0 : ComplexModel n), f (z + h) + f (z - h) - 2 * f z ≤ K * ‖h‖ ^ 2)
    (v : ComplexModel n) : realHessian f z v v ≤ K * ‖v‖ ^ 2 := by
  have hdiff : ∀ x ∈ interior (univ : Set (ComplexModel n)),
      HasFDerivAt f (fderiv ℝ f x) x := fun x _ ↦
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hf' : HasFDerivWithinAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z)
      (interior (univ : Set (ComplexModel n))) z := by
    have : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact (this.differentiable (by norm_num)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hT (w : ComplexModel n) := convex_univ.taylor_approx_two_segment hdiff (mem_univ z) hf'
    (v := 0) (w := w) (by simp) (by simp)
  have hsum := (hT v).add (hT (-v))
  set D := fderiv ℝ (fderiv ℝ f) z
  have heq : (fun h : ℝ ↦ (f (z + h • (0 : ComplexModel n) + h • v) - f (z + h • 0) -
        h • fderiv ℝ f z v - h ^ 2 • D 0 v - (h ^ 2 / 2) • D v v) +
      (f (z + h • (0 : ComplexModel n) + h • -v) - f (z + h • 0) -
        h • fderiv ℝ f z (-v) - h ^ 2 • D 0 (-v) - (h ^ 2 / 2) • D (-v) (-v))) =
      fun h : ℝ ↦ (f (z + h • v) + f (z - h • v) - 2 * f z) - h ^ 2 * D v v := by
    funext h
    simp only [smul_zero, add_zero, map_zero, _root_.zero_apply, map_neg,
      _root_.neg_apply, neg_neg, smul_eq_mul, smul_neg, ← sub_eq_add_neg]
    ring
  rw [heq] at hsum
  by_contra hlt
  push Not at hlt
  have hc : 0 < (D v v - K * ‖v‖ ^ 2) / 2 := by
    rw [realHessian_eq_fderiv] at hlt
    linarith
  have hsmall := (hsum.def hc)
  have hvnhds : Tendsto (fun h : ℝ ↦ h • v) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h : ℝ ↦ h • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) :=
      (continuous_id.smul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨h, ⟨hh1, hh2⟩, hh3⟩ :=
    ((hsmall.and (hvnhds.eventually hK)).and self_mem_nhdsWithin).exists
  have hh3 : 0 < h := hh3
  simp only [Real.norm_eq_abs, abs_pow, sq_abs] at hh1
  have hh2' : f (z + h • v) + f (z - h • v) - 2 * f z ≤ K * ‖v‖ ^ 2 * h ^ 2 := by
    have : ‖h • v‖ ^ 2 = h ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [this] at hh2
    linarith
  rw [realHessian_eq_fderiv] at hlt
  have hh1' := (abs_le.mp hh1).1
  have hpos : 0 < h ^ 2 := by positivity
  nlinarith

/-- With a nonnegative Levi form, the second-difference bound controls the diagonal of the
real Hessian from both sides. -/
theorem abs_realHessian_le_of_secondDifference_le {f : ComplexModel n → ℝ}
    (hf : ContDiff ℝ 2 f) {z : ComplexModel n} {K : ℝ}
    (hK : ∀ᶠ h in 𝓝 (0 : ComplexModel n), f (z + h) + f (z - h) - 2 * f z ≤ K * ‖h‖ ^ 2)
    (hlevi : ∀ v, 0 ≤ leviForm f z v) (v : ComplexModel n) :
    |realHessian f z v v| ≤ K * ‖v‖ ^ 2 := by
  have h1 := realHessian_le_of_secondDifference_le hf hK v
  have h2 := realHessian_le_of_secondDifference_le hf hK (Complex.I • v)
  have h3 := hlevi v
  rw [norm_smul, Complex.norm_I, one_mul] at h2
  rw [leviForm] at h3
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Polarization: a symmetric bilinear form whose quadratic form is bounded by `K ‖v‖²`
satisfies `|B v w| ≤ 2 K ‖v‖ ‖w‖`. -/
theorem abs_apply_le_of_abs_apply_self_le
    {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, B v w = B w v) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ v, |B v v| ≤ K * ‖v‖ ^ 2) (v w : ComplexModel n) :
    |B v w| ≤ 2 * K * (‖v‖ * ‖w‖) := by
  have hpol : ∀ x y : ComplexModel n, |B x y| ≤ K * (‖x‖ + ‖y‖) ^ 2 / 2 := by
    intro x y
    have hid : B x y = (B (x + y) (x + y) - B (x - y) (x - y)) / 4 := by
      simp only [map_add, map_sub, add_apply, sub_apply, hsymm y x]
      ring
    have h1 := hB (x + y)
    have h2 := hB (x - y)
    have h5 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have h6 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    have h1' := (abs_le.mp h1)
    have h2' := (abs_le.mp h2)
    rw [hid, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num : (0 : ℝ)
      < 4)]
    have := abs_sub (B (x + y) (x + y)) (B (x - y) (x - y))
    have hxy : |B (x + y) (x + y)| + |B (x - y) (x - y)| ≤ 2 * (K * (‖x‖ + ‖y‖) ^ 2) := by
      have := mul_le_mul_of_nonneg_left h5 hK
      have := mul_le_mul_of_nonneg_left h6 hK
      linarith [h1, h2]
    linarith
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set t : ℝ := Real.sqrt (‖w‖ / ‖v‖) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hwn hvn)
  have ht2 : t ^ 2 = ‖w‖ / ‖v‖ := Real.sq_sqrt (div_pos hwn hvn).le
  have hscale : B (t • v) (t⁻¹ • w) = B v w := by
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
  have hnorms : t * ‖v‖ = t⁻¹ * ‖w‖ := by
    rw [eq_comm, inv_mul_eq_div, div_eq_iff ht.ne']
    have : t * ‖v‖ * t = t ^ 2 * ‖v‖ := by ring
    rw [this, ht2]
    field_simp
  have hbound := hpol (t • v) (t⁻¹ • w)
  rw [hscale, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ht, abs_of_pos (inv_pos.mpr ht)] at hbound
  have hprod : (t * ‖v‖) * (t⁻¹ * ‖w‖) = ‖v‖ * ‖w‖ := by
    field_simp
  have : (t * ‖v‖ + t⁻¹ * ‖w‖) ^ 2 = 4 * (‖v‖ * ‖w‖) := by
    rw [← hnorms] at hprod ⊢
    nlinarith [hprod]
  rw [this] at hbound
  linarith

/-- Polarization: a symmetric bilinear form whose quadratic form is bounded by `K ‖v‖²` has
operator norm at most `2K`. -/
theorem norm_le_of_abs_apply_self_le {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, B v w = B w v) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ v, |B v v| ≤ K * ‖v‖ ^ 2) : ‖B‖ ≤ 2 * K := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  have := abs_apply_le_of_abs_apply_self_le hsymm hK hB v w
  rw [Real.norm_eq_abs]
  nlinarith [norm_nonneg v, norm_nonneg w]

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

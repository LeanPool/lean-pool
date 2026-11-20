/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ModifiedBesselIIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Gaussian coordinates for the order-one I integral

We first integrate the cosine representation of `I₁` by parts.  The substitution
`x = 2 sin (θ / 2)` then produces a nonsingular Gaussian amplitude

`x² sqrt (1 - x² / 4)`.

Mathlib's totalized square root makes this amplitude vanish for `x ≥ 2`, so the finite
angular integral becomes an exact half-line integral.  The module ends with the elementary
bounds on `√(1 - x²/4)` that compare the amplitude with `x²`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Real
open scoped Interval

namespace FastDynamo.ModifiedBessel

/-- On `(0, π)` the totalized square root `sqrt (1 - sin²(θ/2))` equals `cos (θ/2)`, since the
half-angle stays in `(0, π/2)` where the cosine is positive.  This identifies the Jacobian of the
substitution `x = 2 sin (θ/2)`. -/
private lemma sqrt_one_sub_sin_sq_half {theta : ℝ}
    (htheta : theta ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.sqrt (1 - Real.sin (theta / 2) ^ 2) = Real.cos (theta / 2) := by
  rw [← Real.cos_sq']
  rw [Real.sqrt_sq_eq_abs, abs_of_pos]
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htheta.1, Real.pi_pos], by linarith [htheta.2]⟩

/-- Nonsingular amplitude obtained by angular integration by parts. -/
noncomputable def I1QuadraticGaussianAmplitude (x : ℝ) : ℝ :=
  x ^ 2 * Real.sqrt (1 - x ^ 2 / 4)

/-- Gaussian kernel with the nonsingular quadratic amplitude. -/
noncomputable def I1QuadraticGaussianKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-z * (x : ℂ) ^ 2 / 2) * I1QuadraticGaussianAmplitude x

/-- Integration by parts removes the sign-changing cosine amplitude. -/
theorem integral_exp_mul_cos_eq_z_mul_integral_exp_mul_sin_sq (z : ℂ) :
    (∫ theta : ℝ in 0..Real.pi,
        Complex.exp (z * (Real.cos theta : ℂ)) * (Real.cos theta : ℂ)) =
      z * ∫ theta : ℝ in 0..Real.pi,
        Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2 := by
  let u : ℝ → ℂ := fun theta ↦ Complex.exp (z * (Real.cos theta : ℂ))
  let v : ℝ → ℂ := fun theta ↦ (Real.sin theta : ℂ)
  let u' : ℝ → ℂ := fun theta ↦
    (-z * (Real.sin theta : ℂ)) * Complex.exp (z * (Real.cos theta : ℂ))
  let v' : ℝ → ℂ := fun theta ↦ (Real.cos theta : ℂ)
  have hu : ∀ theta ∈ [[(0 : ℝ), Real.pi]], HasDerivAt u (u' theta) theta := by
    intro theta _
    have hcos : HasDerivAt (fun s : ℝ ↦ (Real.cos s : ℂ))
        (-(Real.sin theta : ℂ)) theta := by
      simpa using (Real.hasDerivAt_cos theta).ofReal_comp
    dsimp [u, u']
    convert (hcos.const_mul z).cexp using 1
    all_goals ring
  have hv : ∀ theta ∈ [[(0 : ℝ), Real.pi]], HasDerivAt v (v' theta) theta := by
    intro theta _
    dsimp [v, v']
    simpa using (Real.hasDerivAt_sin theta).ofReal_comp
  have hu' : IntervalIntegrable u' volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [u']
    fun_prop
  have hv' : IntervalIntegrable v' volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [v']
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := u) (v := v) (u' := u') (v' := v') hu hv hu' hv'
  dsimp [u, v, u', v'] at hparts
  simp only [Real.sin_pi, Real.sin_zero, Complex.ofReal_zero, mul_zero, sub_self,
    zero_sub] at hparts
  calc
    (∫ theta : ℝ in 0..Real.pi,
        Complex.exp (z * (Real.cos theta : ℂ)) * (Real.cos theta : ℂ)) =
        -∫ theta : ℝ in 0..Real.pi,
          ((-z * (Real.sin theta : ℂ)) *
            Complex.exp (z * (Real.cos theta : ℂ))) * (Real.sin theta : ℂ) := hparts
    _ = z * ∫ theta : ℝ in 0..Real.pi,
        Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2 := by
      calc
        -∫ theta : ℝ in 0..Real.pi,
            ((-z * (Real.sin theta : ℂ)) *
              Complex.exp (z * (Real.cos theta : ℂ))) * (Real.sin theta : ℂ) =
            ∫ theta : ℝ in 0..Real.pi,
              -(((-z * (Real.sin theta : ℂ)) *
                Complex.exp (z * (Real.cos theta : ℂ))) * (Real.sin theta : ℂ)) := by
          rw [intervalIntegral.integral_neg]
        _ = ∫ theta : ℝ in 0..Real.pi,
            z * (Complex.exp (z * (Real.cos theta : ℂ)) *
              (Real.sin theta : ℂ) ^ 2) := by
          apply intervalIntegral.integral_congr
          intro theta _
          ring
        _ = z * ∫ theta : ℝ in 0..Real.pi,
            Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2 := by
          rw [intervalIntegral.integral_const_mul]

/-- Exact nonsingular kernel identity under `x = 2 sin (theta / 2)`. -/
lemma I1QuadraticGaussianKernel_substitution (z : ℂ) {theta : ℝ}
    (htheta : theta ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.cos (theta / 2) •
        I1QuadraticGaussianKernel z (2 * Real.sin (theta / 2)) =
      Complex.exp (-z) *
        (Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2) := by
  rw [I1QuadraticGaussianKernel, I1QuadraticGaussianAmplitude]
  have hsqrt :
      Real.sqrt (1 - (2 * Real.sin (theta / 2)) ^ 2 / 4) =
        Real.cos (theta / 2) := by
    rw [show (2 * Real.sin (theta / 2)) ^ 2 / 4 =
        Real.sin (theta / 2) ^ 2 by ring]
    exact sqrt_one_sub_sin_sq_half htheta
  have hphase :
      -z * (((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ 2) / 2 =
        -z + z * (Real.cos theta : ℂ) := by
    have hcos :
        (((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ 2 / 2) =
          1 - (Real.cos theta : ℂ) := by
      norm_cast
      calc
        (2 * Real.sin (theta / 2)) ^ 2 / 2 =
            2 * Real.sin (theta / 2) ^ 2 := by ring
        _ = 1 - Real.cos (2 * (theta / 2)) := by
          rw [Real.cos_two_mul, Real.cos_sq']
          ring
        _ = 1 - Real.cos theta := by ring_nf
    rw [show -z * (((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ 2) / 2 =
        -z * ((((2 * Real.sin (theta / 2) : ℝ) : ℂ) ^ 2) / 2) by ring,
      hcos]
    ring
  have hsin :
      (2 * Real.sin (theta / 2)) ^ 2 * Real.cos (theta / 2) ^ 2 =
        Real.sin theta ^ 2 := by
    rw [show theta = 2 * (theta / 2) by ring, Real.sin_two_mul]
    ring_nf
  rw [hsqrt, hphase, Complex.exp_add, Complex.real_smul]
  have hsinC :
      (((2 * Real.sin (theta / 2)) ^ 2 * Real.cos (theta / 2) ^ 2 : ℝ) : ℂ) =
        (Real.sin theta : ℂ) ^ 2 := by
    exact_mod_cast hsin
  calc
    (Real.cos (theta / 2) : ℂ) *
          (Complex.exp (-z) * Complex.exp (z * (Real.cos theta : ℂ)) *
            ((2 * Real.sin (theta / 2)) ^ 2 * Real.cos (theta / 2) : ℝ)) =
        Complex.exp (-z) * Complex.exp (z * (Real.cos theta : ℂ)) *
          (((2 * Real.sin (theta / 2)) ^ 2 * Real.cos (theta / 2) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = Complex.exp (-z) * Complex.exp (z * (Real.cos theta : ℂ)) *
          (Real.sin theta : ℂ) ^ 2 := by rw [hsinC]
    _ = _ := by ring

/-- The substitution map `u ↦ 2 sin (u/2)` has derivative `cos (θ/2)` at `θ`. -/
private lemma hasDerivAt_two_mul_sin_half (theta : ℝ) :
    HasDerivAt (fun u : ℝ ↦ 2 * Real.sin (u / 2))
      (Real.cos (theta / 2)) theta := by
  have hdiv : HasDerivAt (fun u : ℝ ↦ u / 2) (1 / 2) theta :=
    (hasDerivAt_id theta).div_const 2
  have hsin0 : HasDerivAt Real.sin (Real.cos (theta / 2)) (theta / 2) :=
    Real.hasDerivAt_sin (theta / 2)
  have hsin := hsin0.comp theta hdiv
  change HasDerivAt
    (fun u : ℝ ↦ (2 : ℝ) * (Real.sin ∘ fun v : ℝ ↦ v / 2) u)
    (Real.cos (theta / 2)) theta
  apply (hsin.const_mul 2).congr_deriv
  ring

/-- The angular `sin²` integral becomes the nonsingular finite Gaussian integral. -/
theorem integral_normalized_exp_mul_sin_sq_eq_I1QuadraticGaussianKernel (z : ℂ) :
    (∫ theta : ℝ in 0..Real.pi,
        Complex.exp (-z) *
          (Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2)) =
      ∫ x : ℝ in 0..2, I1QuadraticGaussianKernel z x := by
  let f : ℝ → ℝ := fun theta ↦ 2 * Real.sin (theta / 2)
  let f' : ℝ → ℝ := fun theta ↦ Real.cos (theta / 2)
  have hf : ContinuousOn f [[(0 : ℝ), Real.pi]] := by
    apply Continuous.continuousOn
    dsimp [f]
    fun_prop
  have hff' : ∀ theta ∈ Set.Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi),
      HasDerivAt f (f' theta) theta := by
    intro theta _
    exact hasDerivAt_two_mul_sin_half theta
  have hf' : ∀ theta ∈ Set.Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi),
      0 ≤ f' theta := by
    intro theta htheta
    rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at htheta
    dsimp [f']
    exact Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [htheta.1, Real.pi_pos], by linarith [htheta.2]⟩
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := I1QuadraticGaussianKernel z) hf hff' hf'
  have hsub' :
      (∫ theta : ℝ in 0..Real.pi,
          f' theta • I1QuadraticGaussianKernel z (f theta)) =
        ∫ x : ℝ in 0..2, I1QuadraticGaussianKernel z x := by
    simpa [f] using hsub
  calc
    (∫ theta : ℝ in 0..Real.pi,
        Complex.exp (-z) *
          (Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2)) =
        ∫ theta : ℝ in 0..Real.pi,
          f' theta • I1QuadraticGaussianKernel z (f theta) := by
      symm
      apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
      intro theta htheta
      exact I1QuadraticGaussianKernel_substitution z htheta
    _ = ∫ x : ℝ in 0..2, I1QuadraticGaussianKernel z x := hsub'

/-- Exact finite nonsingular Gaussian representation of `I1`. -/
theorem exp_neg_mul_pi_mul_I1_eq_z_mul_integral_quadraticKernel (z : ℂ) :
    Complex.exp (-z) * ((Real.pi : ℂ) * I1 z) =
      z * ∫ x : ℝ in 0..2, I1QuadraticGaussianKernel z x := by
  calc
    Complex.exp (-z) * ((Real.pi : ℂ) * I1 z) =
        Complex.exp (-z) *
          (∫ theta : ℝ in 0..Real.pi,
            Complex.exp (z * (Real.cos theta : ℂ)) * (Real.cos theta : ℂ)) := by
      rw [integral_exp_mul_cos_eq_pi_mul_I1]
    _ = Complex.exp (-z) *
        (z * ∫ theta : ℝ in 0..Real.pi,
          Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2) := by
      rw [integral_exp_mul_cos_eq_z_mul_integral_exp_mul_sin_sq]
    _ = z * ∫ theta : ℝ in 0..Real.pi,
        Complex.exp (-z) *
          (Complex.exp (z * (Real.cos theta : ℂ)) * (Real.sin theta : ℂ) ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = z * ∫ x : ℝ in 0..2, I1QuadraticGaussianKernel z x := by
      rw [integral_normalized_exp_mul_sin_sq_eq_I1QuadraticGaussianKernel]

/-- The totalized square-root amplitude vanishes identically above the finite endpoint. -/
lemma I1QuadraticGaussianKernel_eq_zero_of_two_le (z : ℂ) {x : ℝ} (hx : 2 ≤ x) :
    I1QuadraticGaussianKernel z x = 0 := by
  rw [I1QuadraticGaussianKernel, I1QuadraticGaussianAmplitude]
  have hnonpos : 1 - x ^ 2 / 4 ≤ 0 := by nlinarith
  rw [Real.sqrt_eq_zero_of_nonpos hnonpos]
  simp

/-- The finite transformed integral equals the half-line integral because the amplitude vanishes
for `x ≥ 2`. -/
theorem integral_I1QuadraticGaussianKernel_Ioi_eq_interval (z : ℂ) :
    (∫ x : ℝ in Set.Ioi 0, I1QuadraticGaussianKernel z x) =
      ∫ x : ℝ in 0..2, I1QuadraticGaussianKernel z x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
  · intro x hx
    exact hx.1
  · intro x hx
    apply I1QuadraticGaussianKernel_eq_zero_of_two_le
    have hxNot : ¬x ∈ Set.Ioc (0 : ℝ) 2 := hx.2
    have hxPos : 0 < x := hx.1
    simp only [Set.mem_Ioc, hxPos, true_and, not_le] at hxNot
    exact hxNot.le

/-- Exact half-line nonsingular Gaussian representation. -/
theorem exp_neg_mul_pi_mul_I1_eq_z_mul_integral_quadraticKernel_Ioi (z : ℂ) :
    Complex.exp (-z) * ((Real.pi : ℂ) * I1 z) =
      z * ∫ x : ℝ in Set.Ioi 0, I1QuadraticGaussianKernel z x := by
  rw [integral_I1QuadraticGaussianKernel_Ioi_eq_interval]
  exact exp_neg_mul_pi_mul_I1_eq_z_mul_integral_quadraticKernel z

/-- The totalized square-root factor lies in `[0,1]`. -/
lemma sqrt_one_sub_quarter_sq_mem_Icc (x : ℝ) :
    Real.sqrt (1 - x ^ 2 / 4) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Real.sqrt_nonneg _
  · rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg x]

/-- Two-sided estimate for the deviation of the square-root amplitude factor from one on `[0, 2]`:
`0 ≤ 1 - sqrt (1 - x²/4) ≤ x²/4`. -/
private lemma one_sub_sqrt_one_sub_quarter_sq_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 - Real.sqrt (1 - x ^ 2 / 4) ∧
      1 - Real.sqrt (1 - x ^ 2 / 4) ≤ x ^ 2 / 4 := by
  have hx_sq : x ^ 2 ≤ 4 := by nlinarith [sq_nonneg x]
  have hrad0 : 0 ≤ 1 - x ^ 2 / 4 := by linarith
  have hsqrt_bounds := sqrt_one_sub_quarter_sq_mem_Icc x
  constructor
  · linarith [hsqrt_bounds.2]
  · have hrad_le_sqrt :
        1 - x ^ 2 / 4 ≤ Real.sqrt (1 - x ^ 2 / 4) := by
      rw [Real.le_sqrt hrad0 hrad0]
      nlinarith [sq_nonneg (1 - x ^ 2 / 4)]
    linarith

/-- Globally on the positive half-line, the square-root factor differs from one by at most
`x² / 4`. -/
lemma abs_sqrt_one_sub_quarter_sq_sub_one_le
    {x : ℝ} (hx0 : 0 ≤ x) :
    |Real.sqrt (1 - x ^ 2 / 4) - 1| ≤ x ^ 2 / 4 := by
  rcases le_total x 2 with hx2 | hx2
  · have hlocal := one_sub_sqrt_one_sub_quarter_sq_le hx0 hx2
    rw [abs_of_nonpos (by
      linarith [sqrt_one_sub_quarter_sq_mem_Icc x |>.2])]
    linarith
  · have hrad : 1 - x ^ 2 / 4 ≤ 0 := by nlinarith [sq_nonneg x]
    rw [Real.sqrt_eq_zero_of_nonpos hrad]
    norm_num
    nlinarith [sq_nonneg x]

end FastDynamo.ModifiedBessel

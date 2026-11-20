/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselKRecurrence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian coordinates for the order-one K integral

This module isolates the exact kernel algebra underlying the large-argument estimate for
`z I₁(z) K₁(z)`.  Under `x = 2 sinh (t/2)`, the order-one hyperbolic kernel becomes a complex
Gaussian times an explicit amplitude.  We bound that amplitude's remainder pointwise.

The final theorem carries out the global improper change of variables, including the endpoint
and integrability bookkeeping, and identifies this Gaussian-coordinate integral exactly with
`K₁`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Real

namespace FastDynamo.ModifiedBessel

/-- The exact amplitude produced by `x = 2 sinh (t/2)` in the `K₁` integral. -/
noncomputable def K1GaussianAmplitude (x : ℝ) : ℝ :=
  (1 + x ^ 2 / 2) / Real.sqrt (1 + x ^ 2 / 4)

/-- The `e⁻ᶻ`-normalized Gaussian-coordinate kernel for `K₁`. -/
noncomputable def K1NormalizedGaussianKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-z * (x : ℂ) ^ 2 / 2) * K1GaussianAmplitude x

/-- The totalized square root `sqrt (1 + sinh² u)` equals `cosh u`, the Jacobian identity behind
the substitution `x = 2 sinh (t/2)`. -/
private lemma sqrt_one_add_sinh_sq (u : ℝ) :
    Real.sqrt (1 + Real.sinh u ^ 2) = Real.cosh u := by
  rw [← Real.cosh_sq']
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos u)]

/-- Value of the `K₁` Gaussian amplitude along the substitution `x = 2 sinh (t/2)`:
it equals `cosh t / cosh (t/2)`. -/
lemma K1GaussianAmplitude_two_mul_sinh_half (t : ℝ) :
    K1GaussianAmplitude (2 * Real.sinh (t / 2)) =
      Real.cosh t / Real.cosh (t / 2) := by
  rw [K1GaussianAmplitude]
  have hsq : (2 * Real.sinh (t / 2)) ^ 2 / 4 = Real.sinh (t / 2) ^ 2 := by ring
  have hnum : 1 + (2 * Real.sinh (t / 2)) ^ 2 / 2 = Real.cosh t := by
    calc
      1 + (2 * Real.sinh (t / 2)) ^ 2 / 2 =
          1 + 2 * Real.sinh (t / 2) ^ 2 := by ring
      _ = Real.cosh (2 * (t / 2)) := by
        rw [Real.cosh_two_mul, Real.cosh_sq']
        ring
      _ = Real.cosh t := by ring_nf
  rw [hsq, hnum, sqrt_one_add_sinh_sq]

/-- Exact pointwise kernel identity for the substitution `x = 2 sinh (t/2)`. -/
lemma K1NormalizedGaussianKernel_substitution (z : ℂ) (t : ℝ) :
    Complex.exp (-z) * K1NormalizedGaussianKernel z (2 * Real.sinh (t / 2)) *
        Real.cosh (t / 2) = K1Integrand z t := by
  rw [K1NormalizedGaussianKernel, K1GaussianAmplitude_two_mul_sinh_half,
    K1Integrand]
  have hcosh :
      ((2 * Real.sinh (t / 2) : ℝ) : ℂ) ^ 2 / 2 =
        (Real.cosh t : ℂ) - 1 := by
    norm_cast
    calc
      (2 * Real.sinh (t / 2)) ^ 2 / 2 = 2 * Real.sinh (t / 2) ^ 2 := by ring
      _ = Real.cosh (2 * (t / 2)) - 1 := by
        rw [Real.cosh_two_mul, Real.cosh_sq']
        ring
      _ = Real.cosh t - 1 := by ring_nf
  have hexp :
      -z * ((2 * Real.sinh (t / 2) : ℝ) : ℂ) ^ 2 / 2 =
        -z * ((Real.cosh t : ℂ) - 1) := by
    calc
      -z * ((2 * Real.sinh (t / 2) : ℝ) : ℂ) ^ 2 / 2 =
          -z * (((2 * Real.sinh (t / 2) : ℝ) : ℂ) ^ 2 / 2) := by ring
      _ = -z * ((Real.cosh t : ℂ) - 1) := by rw [hcosh]
  rw [hexp]
  have hhalf : (Real.cosh (t / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cosh_pos (t / 2)).ne'
  have hratio :
      (Real.cosh t / Real.cosh (t / 2) : ℝ) * Real.cosh (t / 2) = Real.cosh t := by
    field_simp
  have hsum : -z + -z * ((Real.cosh t : ℂ) - 1) = -z * Real.cosh t := by ring
  calc
    Complex.exp (-z) *
          (Complex.exp (-z * ((Real.cosh t : ℂ) - 1)) *
            (Real.cosh t / Real.cosh (t / 2) : ℝ)) * Real.cosh (t / 2) =
        (Complex.exp (-z) * Complex.exp (-z * ((Real.cosh t : ℂ) - 1))) *
          (((Real.cosh t / Real.cosh (t / 2) : ℝ) : ℂ) *
            (Real.cosh (t / 2) : ℂ)) := by ring
    _ = Complex.exp (-z + -z * ((Real.cosh t : ℂ) - 1)) *
          (((Real.cosh t / Real.cosh (t / 2) : ℝ) : ℂ) *
            (Real.cosh (t / 2) : ℂ)) := by rw [Complex.exp_add]
    _ = Complex.exp (-z * Real.cosh t) * Real.cosh t := by
      rw [hsum]
      rw [← Complex.ofReal_mul, hratio]

/-- The `K₁` Gaussian amplitude is at least `1` everywhere, so the transformed kernel never
falls below the pure complex Gaussian in modulus. -/
lemma one_le_K1GaussianAmplitude (x : ℝ) : 1 ≤ K1GaussianAmplitude x := by
  rw [K1GaussianAmplitude]
  have hs0 : 0 ≤ x ^ 2 / 4 := by positivity
  have hsqrt0 : 0 < Real.sqrt (1 + x ^ 2 / 4) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hsqrt0]
  have hsqrt_le : Real.sqrt (1 + x ^ 2 / 4) ≤ 1 + x ^ 2 / 4 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith [sq_nonneg (x ^ 2 / 4)]
  linarith

/-- The `K₁` Gaussian amplitude exceeds `1` by at most `x²/2`; this quadratic deviation is what
the Gaussian second moment integrates in the sector estimate. -/
lemma K1GaussianAmplitude_sub_one_le (x : ℝ) :
    K1GaussianAmplitude x - 1 ≤ x ^ 2 / 2 := by
  rw [K1GaussianAmplitude]
  have hsqrt1 : 1 ≤ Real.sqrt (1 + x ^ 2 / 4) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg x]
  have hsqrt0 : 0 < Real.sqrt (1 + x ^ 2 / 4) := lt_of_lt_of_le zero_lt_one hsqrt1
  rw [div_sub_one hsqrt0.ne', div_le_iff₀ hsqrt0]
  have hnonneg : 0 ≤ x ^ 2 / 2 := by positivity
  calc
    1 + x ^ 2 / 2 - Real.sqrt (1 + x ^ 2 / 4) ≤ x ^ 2 / 2 := by linarith
    _ ≤ x ^ 2 / 2 * Real.sqrt (1 + x ^ 2 / 4) := by nlinarith

/-- The transformed K-kernel differs from the complex Gaussian by a quadratic-amplitude
remainder.  This is the pointwise estimate needed before one Gaussian moment integration. -/
lemma norm_K1NormalizedGaussianKernel_sub_gaussian_le (z : ℂ) (x : ℝ) :
    ‖K1NormalizedGaussianKernel z x - Complex.exp (-z * (x : ℂ) ^ 2 / 2)‖ ≤
      Real.exp (-z.re * x ^ 2 / 2) * (x ^ 2 / 2) := by
  rw [K1NormalizedGaussianKernel]
  have hfactor :
      Complex.exp (-z * (x : ℂ) ^ 2 / 2) * (K1GaussianAmplitude x : ℂ) -
          Complex.exp (-z * (x : ℂ) ^ 2 / 2) =
        Complex.exp (-z * (x : ℂ) ^ 2 / 2) *
          ((K1GaussianAmplitude x : ℂ) - 1) := by ring
  rw [hfactor, norm_mul, Complex.norm_exp]
  have hamp0 : 0 ≤ K1GaussianAmplitude x - 1 := sub_nonneg.2 (one_le_K1GaussianAmplitude x)
  have hnormamp : ‖(K1GaussianAmplitude x : ℂ) - 1‖ = K1GaussianAmplitude x - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hamp0]
  rw [hnormamp]
  have hre : (-z * (x : ℂ) ^ 2 / 2).re = -z.re * x ^ 2 / 2 := by
    norm_num [Complex.div_re, Complex.mul_re, Complex.normSq]
    rw [show ((x : ℂ) ^ 2).im = 0 by simp [pow_two, Complex.mul_im],
      show ((x : ℂ) ^ 2).re = x ^ 2 by simp [pow_two, Complex.mul_re]]
    ring
  rw [hre]
  exact mul_le_mul_of_nonneg_left (K1GaussianAmplitude_sub_one_le x) (Real.exp_pos _).le

/-- The `K₁` Gaussian amplitude `(1 + x²/2) / sqrt (1 + x²/4)` is continuous, its denominator
being bounded away from zero. -/
private theorem continuous_K1GaussianAmplitude :
    Continuous K1GaussianAmplitude := by
  unfold K1GaussianAmplitude
  have hden : Continuous (fun x : ℝ ↦ Real.sqrt (1 + x ^ 2 / 4)) := by fun_prop
  have hden0 : ∀ x : ℝ, Real.sqrt (1 + x ^ 2 / 4) ≠ 0 := fun x ↦ by
    exact (Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])).ne'
  have hnum : Continuous (fun x : ℝ ↦ 1 + x ^ 2 / 2) := by fun_prop
  exact hnum.div₀ hden hden0

/-- The normalized Gaussian-coordinate kernel for `K₁` is continuous in the radial variable. -/
private theorem continuous_K1NormalizedGaussianKernel (z : ℂ) :
    Continuous (K1NormalizedGaussianKernel z) := by
  unfold K1NormalizedGaussianKernel
  apply Continuous.mul
  · fun_prop
  · exact Complex.continuous_ofReal.comp continuous_K1GaussianAmplitude

/-- The quadratic Gaussian majorant is integrable on the whole line when `Re z > 0`. -/
private theorem integrable_K1GaussianRemainderMajorant {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun x : ℝ ↦ Real.exp (-z.re * x ^ 2 / 2) * (x ^ 2 / 2)) := by
  have hb : 0 < z.re / 2 := by linarith
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb
    (s := (2 : ℝ)) (by norm_num)).const_mul (1 / 2 : ℝ)
  have heq :
      (fun x : ℝ ↦ Real.exp (-z.re * x ^ 2 / 2) * (x ^ 2 / 2)) =
        fun x : ℝ ↦ (1 / 2 : ℝ) *
          (x ^ (2 : ℝ) * Real.exp (-(z.re / 2) * x ^ 2)) := by
    funext x
    rw [Real.rpow_two]
    have hexp : -z.re * x ^ 2 / 2 = -(z.re / 2) * x ^ 2 := by ring
    rw [hexp]
    ring
  rw [heq]
  exact h

/-- For `Re z > 0` the normalized Gaussian-coordinate kernel for `K₁` is integrable on the whole
line, by comparison with the pure complex Gaussian plus the quadratic majorant. -/
private theorem integrable_K1NormalizedGaussianKernel {z : ℂ} (hz : 0 < z.re) :
    Integrable (K1NormalizedGaussianKernel z) := by
  let e : ℝ → ℂ := fun x ↦
    K1NormalizedGaussianKernel z x - Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let m : ℝ → ℝ := fun x ↦ Real.exp (-z.re * x ^ 2 / 2) * (x ^ 2 / 2)
  have hm : Integrable m := integrable_K1GaussianRemainderMajorant hz
  have he_meas : AEStronglyMeasurable e := by
    apply Continuous.aestronglyMeasurable
    dsimp [e]
    exact (continuous_K1NormalizedGaussianKernel z).sub (by fun_prop)
  have he : Integrable e := by
    apply Integrable.mono hm he_meas
    exact Filter.Eventually.of_forall fun x ↦ by
      have h := norm_K1NormalizedGaussianKernel_sub_gaussian_le z x
      dsimp [e, m]
      convert h using 1
      have hx : 0 ≤ x ^ 2 / 2 := by positivity
      exact abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hx)
  have hg : Integrable (fun x : ℝ ↦ Complex.exp (-z * (x : ℂ) ^ 2 / 2)) := by
    have hzhalf : 0 < (z / 2).re := by simpa [Complex.div_re] using (half_pos hz)
    have h := integrable_cexp_neg_mul_sq hzhalf
    convert h using 1 with x
    ring_nf
  have hsum := he.add hg
  apply hsum.congr (ae_of_all _ fun x ↦ ?_)
  dsimp [e]
  ring

/-- The substitution map `t ↦ 2 sinh (t/2)` tends to `+∞` as `t → +∞`, so it takes the half-line
integral onto the half-line integral in the Gaussian variable. -/
private theorem tendsto_two_mul_sinh_half_atTop :
    Tendsto (fun t : ℝ ↦ 2 * Real.sinh (t / 2)) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show ∀ᶠ t : ℝ in atTop, t ≤ 2 * Real.sinh (t / 2) by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hhalf : t / 2 ≤ Real.sinh (t / 2) :=
        Real.self_le_sinh_iff.2 (by linarith)
      linarith)
    tendsto_id

/-- The exact improper-integral substitution `x = 2 sinh (t / 2)` for the integral definition of
`K1`. The right-half-plane hypothesis supplies absolute integrability at both infinite
endpoints. -/
theorem K1_eq_exp_neg_mul_integral_normalizedGaussianKernel
    {z : ℂ} (hz : 0 < z.re) :
    K1 z = Complex.exp (-z) *
      ∫ x in Ioi (0 : ℝ), K1NormalizedGaussianKernel z x := by
  let f : ℝ → ℝ := fun t ↦ 2 * Real.sinh (t / 2)
  let f' : ℝ → ℝ := fun t ↦ Real.cosh (t / 2)
  let g : ℝ → ℂ := fun x ↦ Complex.exp (-z) * K1NormalizedGaussianKernel z x
  have hf : ContinuousOn f (Ici 0) := by
    exact (by dsimp [f]; fun_prop : Continuous f).continuousOn
  have hft : Tendsto f atTop atTop := by
    simpa only [f] using tendsto_two_mul_sinh_half_atTop
  have hff' : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Ioi t) t := by
    intro t _
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    have h := ((Real.hasDerivAt_sinh (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).const_mul 2
    have hcoef : 2 * (Real.cosh (t / 2) * (1 / 2 : ℝ)) = Real.cosh (t / 2) := by ring
    simpa only [Function.comp_apply, id_eq] using h.congr_deriv hcoef
  have hg_cont : ContinuousOn g (f '' Ioi (0 : ℝ)) := by
    exact (Continuous.const_mul (continuous_K1NormalizedGaussianKernel z)
      (Complex.exp (-z))).continuousOn
  have hg1 : IntegrableOn g (f '' Ici (0 : ℝ)) := by
    have hglobal : Integrable g :=
      (integrable_K1NormalizedGaussianKernel hz).const_mul (Complex.exp (-z))
    exact hglobal.integrableOn
  have hg2 : IntegrableOn (fun t ↦ f' t • (g ∘ f) t) (Ici (0 : ℝ)) := by
    have hk : IntegrableOn (K1Integrand z) (Ici (0 : ℝ)) :=
      (integrableOn_Ici_iff_integrableOn_Ioi
        (f := K1Integrand z) (b := (0 : ℝ))).2 (integrableOn_K1Integrand hz)
    apply hk.congr_fun _ measurableSet_Ici
    intro t _
    dsimp [f, f', g, Function.comp_def]
    symm
    rw [mul_comm (Real.cosh (t / 2) : ℂ)]
    exact K1NormalizedGaussianKernel_substitution z t
  have hchange := integral_deriv_smul_comp_Ioi hf hft hff' hg_cont hg1 hg2
  have hleft :
      (∫ t in Ioi (0 : ℝ), f' t • (g ∘ f) t) = K1 z := by
    change (∫ t in Ioi (0 : ℝ), f' t • (g ∘ f) t) =
      ∫ t in Ioi (0 : ℝ), K1Integrand z t
    apply integral_congr_ae
    filter_upwards with t
    dsimp [f, f', g, Function.comp_def]
    rw [mul_comm (Real.cosh (t / 2) : ℂ)]
    exact K1NormalizedGaussianKernel_substitution z t
  have hright :
      (∫ x in Ioi (f 0), g x) =
        Complex.exp (-z) * ∫ x in Ioi (0 : ℝ), K1NormalizedGaussianKernel z x := by
    have hf0 : f 0 = 0 := by simp [f]
    rw [hf0]
    exact integral_const_mul _ _
  rw [hleft, hright] at hchange
  exact hchange

end FastDynamo.ModifiedBessel

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ModifiedBesselIRecurrence
public import LeanPool.FastDynamo.Local.ModifiedBesselKRecurrence
public import LeanPool.FastDynamo.Local.PonomarenkoDispersionAnalytic

/-!
# Normalized modified-Bessel Wronskians

This module combines the order-one recurrence API with a direct small-positive-real
normalization of the hyperbolic `K1` integral.  The normalization uses only improper FTC and
the elementary identity `cosh t - sinh t = exp (-t)`; no asymptotic expansion is used.
-/

@[expose] public section

noncomputable section

namespace FastDynamo.ModifiedBessel

open Complex MeasureTheory Set Filter Topology

/-! ## Small-positive-real normalization of `K1` -/

/-- The kernel `exp (-x cosh t) sinh t`, the part of the `K₁` hyperbolic kernel that has an
elementary primitive. -/
private def KSinhIntegrand (x : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ) * Real.cosh t) * (Real.sinh t : ℂ)

/-- The primitive `exp (-x cosh t)` of `-x · KSinhIntegrand x`, used for the improper
fundamental theorem of calculus in `t`. -/
private def KSinhPrimitive (x : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ) * Real.cosh t)

/-- The `t`-derivative `-x · KSinhIntegrand x t` of `KSinhPrimitive x`. -/
private def KSinhDeriv (x : ℝ) (t : ℝ) : ℂ :=
  -(x : ℂ) * KSinhIntegrand x t

/-- `KSinhPrimitive x` is differentiable in `t` with derivative `KSinhDeriv x t`. -/
private lemma hasDerivAt_KSinhPrimitive (x t : ℝ) :
    HasDerivAt (KSinhPrimitive x) (KSinhDeriv x t) t := by
  have hcosh : HasDerivAt (fun s : ℝ ↦ (Real.cosh s : ℂ))
      (Real.sinh t : ℂ) t := (Real.hasDerivAt_cosh t).ofReal_comp
  have hinner : HasDerivAt (fun s : ℝ ↦ -(x : ℂ) * (Real.cosh s : ℂ))
      (-(x : ℂ) * (Real.sinh t : ℂ)) t := hcosh.const_mul (-(x : ℂ))
  apply hinner.cexp.congr_deriv
  unfold KSinhDeriv KSinhIntegrand
  ring

/-- For `x > 0` the kernel `exp (-x cosh t) sinh t` is integrable on the positive half-line,
being dominated by the order-one kernel since `|sinh t| ≤ cosh t`. -/
private theorem integrableOn_KSinhIntegrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (KSinhIntegrand x) (Ioi 0) := by
  apply MeasureTheory.Integrable.mono
    (integrableOn_K1Integrand (z := (x : ℂ)) (by simpa))
  · exact (by unfold KSinhIntegrand; fun_prop :
      Continuous (KSinhIntegrand x)).aestronglyMeasurable.restrict
  · apply ae_of_all
    intro t
    rw [KSinhIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      K1Integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [abs_of_pos (Real.cosh_pos t)]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos _).le).mp
    rw [sq_abs, Real.cosh_sq']
    exact le_add_of_nonneg_left zero_le_one

/-- For `x > 0` the derivative kernel `KSinhDeriv x` is integrable on the positive half-line. -/
private theorem integrableOn_KSinhDeriv {x : ℝ} (hx : 0 < x) :
    IntegrableOn (KSinhDeriv x) (Ioi 0) := by
  have h := (integrableOn_KSinhIntegrand hx).const_mul (-(x : ℂ))
  exact h.congr (ae_of_all _ fun _ ↦ rfl)

/-- For `x > 0` the primitive `exp (-x cosh t)` is integrable on the positive half-line, being
the `K₀` kernel at the real point `x`. -/
private theorem integrableOn_KSinhPrimitive {x : ℝ} (hx : 0 < x) :
    IntegrableOn (KSinhPrimitive x) (Ioi 0) := by
  exact (integrableOn_K0Integrand (z := (x : ℂ)) (by simpa)).congr
    (ae_of_all _ fun _ ↦ rfl)

/-- For `x > 0` the primitive `exp (-x cosh t)` tends to `0` as `t → ∞`, the boundary condition
needed at the infinite endpoint. -/
private theorem tendsto_KSinhPrimitive_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (KSinhPrimitive x) atTop (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t _ ↦ hasDerivAt_KSinhPrimitive x t)
    (integrableOn_KSinhDeriv hx) (integrableOn_KSinhPrimitive hx)

/-- Improper fundamental theorem of calculus for `KSinhDeriv`: its integral over `(0, ∞)` is
`-exp (-x)`, the negative of the value of the primitive at `t = 0`. -/
private theorem integral_KSinhDeriv {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), KSinhDeriv x t) = -Complex.exp (-(x : ℂ)) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (f := KSinhPrimitive x) (f' := KSinhDeriv x)
    (fun t _ ↦ hasDerivAt_KSinhPrimitive x t)
    (integrableOn_KSinhDeriv hx) (tendsto_KSinhPrimitive_atTop hx)
  simpa [KSinhPrimitive] using h

/-- The elementary evaluation `x ∫₀^∞ exp (-x cosh t) sinh t dt = exp (-x)` for `x > 0`. -/
private theorem x_mul_integral_KSinhIntegrand {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * (∫ t in Ioi (0 : ℝ), KSinhIntegrand x t) = Complex.exp (-(x : ℂ)) := by
  have h := integral_KSinhDeriv hx
  have hc := integral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
    (-(x : ℂ)) (KSinhIntegrand x)
  change (∫ t in Ioi (0 : ℝ), -(x : ℂ) * KSinhIntegrand x t) =
    -(x : ℂ) * ∫ t in Ioi (0 : ℝ), KSinhIntegrand x t at hc
  change (∫ t in Ioi (0 : ℝ), -(x : ℂ) * KSinhIntegrand x t) =
    -Complex.exp (-(x : ℂ)) at h
  rw [hc] at h
  linear_combination -h

/-- The complementary part `exp (-x cosh t) e^{-t}` of the `K₁` kernel, obtained from
`cosh t = sinh t + e^{-t}`. -/
private def K1RemainderIntegrand (x : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ) * Real.cosh t) * (Real.exp (-t) : ℂ)

/-- Splitting the order-one kernel at a real argument as `cosh t = sinh t + e^{-t}`:
`K1Integrand x t = KSinhIntegrand x t + K1RemainderIntegrand x t`. -/
private lemma K1Integrand_eq_sinh_add_remainder (x t : ℝ) :
    K1Integrand (x : ℂ) t = KSinhIntegrand x t + K1RemainderIntegrand x t := by
  unfold K1Integrand KSinhIntegrand K1RemainderIntegrand
  rw [← Real.cosh_sub_sinh t]
  push_cast
  ring

/-- For `x > 0` the complementary kernel is bounded by `e^{-t}`, since `exp (-x cosh t) ≤ 1`. -/
private lemma norm_K1RemainderIntegrand_le (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖K1RemainderIntegrand x t‖ ≤ Real.exp (-t) := by
  change ‖K0Integrand (x : ℂ) t * (Real.exp (-t) : ℂ)‖ ≤ Real.exp (-t)
  rw [norm_mul, norm_K0Integrand, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [ofReal_re]
  have he : Real.exp (-x * Real.cosh t) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.cosh_pos t]
  nlinarith [Real.exp_pos (-t)]

/-- For `x > 0` the complementary kernel is integrable on the positive half-line, dominated by
`e^{-t}`. -/
private theorem integrableOn_K1RemainderIntegrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (K1RemainderIntegrand x) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
  · exact (by unfold K1RemainderIntegrand; fun_prop :
      Continuous (K1RemainderIntegrand x)).aestronglyMeasurable.restrict
  · exact ae_of_all _ fun t ↦ norm_K1RemainderIntegrand_le x hx t

/-- The integral of the complementary kernel over `(0, ∞)` has norm at most `1`, since
`∫₀^∞ e^{-t} dt = 1`.  This is the error term in the small-`x` normalization of `K₁`. -/
private theorem norm_integral_K1RemainderIntegrand_le_one {x : ℝ} (hx : 0 < x) :
    ‖∫ t in Ioi (0 : ℝ), K1RemainderIntegrand x t‖ ≤ 1 := by
  calc
    ‖∫ t in Ioi (0 : ℝ), K1RemainderIntegrand x t‖ ≤
        ∫ t in Ioi (0 : ℝ), ‖K1RemainderIntegrand x t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-t) := by
      apply setIntegral_mono_on (integrableOn_K1RemainderIntegrand hx).norm
        (integrableOn_exp_neg_Ioi 0) measurableSet_Ioi
      intro t _
      exact norm_K1RemainderIntegrand_le x hx t
    _ = 1 := integral_exp_neg_Ioi_zero

/-- Additive splitting of `K₁` at a positive real argument into the elementary `sinh`-integral
and the complementary remainder integral. -/
private theorem K1_eq_sinhIntegral_add_remainder {x : ℝ} (hx : 0 < x) :
    K1 (x : ℂ) = (∫ t in Ioi (0 : ℝ), KSinhIntegrand x t) +
      ∫ t in Ioi (0 : ℝ), K1RemainderIntegrand x t := by
  unfold K1
  rw [show (∫ t in Ioi (0 : ℝ), K1Integrand (x : ℂ) t) =
      ∫ t in Ioi (0 : ℝ), KSinhIntegrand x t + K1RemainderIntegrand x t from
    integral_congr_ae (ae_of_all _ fun t ↦ K1Integrand_eq_sinh_add_remainder x t)]
  exact integral_add (integrableOn_KSinhIntegrand hx)
    (integrableOn_K1RemainderIntegrand hx)

/-- Quantitative small-positive-real normalization of the integral `K1`. -/
theorem norm_x_mul_K1_sub_exp_le {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) * K1 (x : ℂ) - Complex.exp (-(x : ℂ))‖ ≤ x := by
  rw [K1_eq_sinhIntegral_add_remainder hx, mul_add,
    x_mul_integral_KSinhIntegrand hx, add_sub_cancel_left]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  exact mul_le_of_le_one_right hx.le (norm_integral_K1RemainderIntegrand_le_one hx)

/-- The normalization `x K1(x) → 1` as `x ↓ 0`. -/
theorem tendsto_x_mul_K1_nhdsWithin_zero :
    Tendsto (fun x : ℝ ↦ (x : ℂ) * K1 (x : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hid : Tendsto (fun x : ℝ ↦ x) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have hnorm : Tendsto
      (fun x : ℝ ↦ ‖(x : ℂ) * K1 (x : ℂ) - Complex.exp (-(x : ℂ))‖)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      exact norm_x_mul_K1_sub_exp_le hx
    · exact hid
  have hdiff : Tendsto
      (fun x : ℝ ↦ (x : ℂ) * K1 (x : ℂ) - Complex.exp (-(x : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hexp : Tendsto (fun x : ℝ ↦ Complex.exp (-(x : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ Complex.exp (-(x : ℂ))) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hexp

/-- At a real argument the order-one kernel is a nonnegative real number, so it coincides with
its own norm. -/
private lemma K1Integrand_ofReal_eq_norm (x t : ℝ) :
    K1Integrand (x : ℂ) t = (‖K1Integrand (x : ℂ) t‖ : ℂ) := by
  rw [norm_K1Integrand]
  unfold K1Integrand
  simp only [Complex.ofReal_re]
  rw [show -(x : ℂ) * (Real.cosh t : ℂ) = ((-x * Real.cosh t : ℝ) : ℂ) by
    push_cast; ring]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

/-- Consequently `K₁` at a positive real argument is real, equal to the integral of the norms of
its kernel. -/
private theorem K1_ofReal_eq_ofReal_integral_norm {x : ℝ} :
    K1 (x : ℂ) = Complex.ofReal
      (∫ t in Ioi (0 : ℝ), ‖K1Integrand (x : ℂ) t‖) := by
  unfold K1
  calc
    (∫ t in Ioi (0 : ℝ), K1Integrand (x : ℂ) t) =
        ∫ t in Ioi (0 : ℝ), (‖K1Integrand (x : ℂ) t‖ : ℂ) := by
      exact integral_congr_ae (ae_of_all _ fun t ↦ K1Integrand_ofReal_eq_norm x t)
    _ = Complex.ofReal (∫ t in Ioi (0 : ℝ), ‖K1Integrand (x : ℂ) t‖) := integral_ofReal

/-- For `x > 0` the order-zero value is dominated by the order-one value at the same real point,
since `‖K0Integrand‖ ≤ ‖K1Integrand‖` and the latter integral is real and nonnegative. -/
private theorem norm_K0_le_norm_K1_ofReal {x : ℝ} (hx : 0 < x) :
    ‖K0 (x : ℂ)‖ ≤ ‖K1 (x : ℂ)‖ := by
  have hnorm0 := norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (K0Integrand (x : ℂ))
  change ‖K0 (x : ℂ)‖ ≤ ∫ t in Ioi (0 : ℝ), ‖K0Integrand (x : ℂ) t‖ at hnorm0
  have hmono : (∫ t in Ioi (0 : ℝ), ‖K0Integrand (x : ℂ) t‖) ≤
      ∫ t in Ioi (0 : ℝ), ‖K1Integrand (x : ℂ) t‖ := by
    apply setIntegral_mono_on
      (integrableOn_K0Integrand (z := (x : ℂ)) (by simpa)).norm
      (integrableOn_K1Integrand (z := (x : ℂ)) (by simpa)).norm measurableSet_Ioi
    intro t _
    rw [norm_K0Integrand, norm_K1Integrand]
    calc
      Real.exp (-(x : ℂ).re * Real.cosh t) =
          Real.exp (-(x : ℂ).re * Real.cosh t) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-(x : ℂ).re * Real.cosh t) * Real.cosh t :=
        mul_le_mul_of_nonneg_left (Real.one_le_cosh t) (Real.exp_pos _).le
  calc
    ‖K0 (x : ℂ)‖ ≤ ∫ t in Ioi (0 : ℝ), ‖K0Integrand (x : ℂ) t‖ := hnorm0
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖K1Integrand (x : ℂ) t‖ := hmono
    _ = ‖K1 (x : ℂ)‖ := by
      rw [K1_ofReal_eq_ofReal_integral_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ fun t ↦ norm_nonneg _))]

/-- A uniform bound sufficient to eliminate the `I1(x) · x K0(x)` boundary term. -/
theorem norm_x_mul_K0_le_two {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖(x : ℂ) * K0 (x : ℂ)‖ ≤ 2 := by
  calc
    ‖(x : ℂ) * K0 (x : ℂ)‖ = x * ‖K0 (x : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    _ ≤ x * ‖K1 (x : ℂ)‖ := by
      gcongr
      exact norm_K0_le_norm_K1_ofReal hx
    _ = ‖(x : ℂ) * K1 (x : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    _ ≤ ‖Complex.exp (-(x : ℂ))‖ + x := by
      have h := norm_x_mul_K1_sub_exp_le hx
      exact (norm_le_norm_add_norm_sub' _ _).trans (add_le_add_right h _)
    _ ≤ 2 := by
      rw [Complex.norm_exp]
      simp only [neg_re, ofReal_re]
      have he : Real.exp (-x) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith

/-! ## Conservation of the order-zero Wronskian -/

/-- The derivative-free form of the order-zero modified-Bessel Wronskian. -/
noncomputable def orderZeroWronskian (z : ℂ) : ℂ :=
  I1 z * K0 z + I0 z * K1 z

/-- Differentiability of `W₀(z) = I₁ z K₀ z + I₀ z K₁ z` on the open right half-plane, with the
derivative obtained from the first-order recurrences of both kinds. -/
private theorem hasDerivAt_orderZeroWronskian {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt orderZeroWronskian
      ((I0 z + I2 z) / 2 * K0 z + I1 z * (-K1 z) +
        (I1 z * K1 z + I0 z * (-(K0 z + K2 z) / 2))) z := by
  have h := ((I1_hasDerivAt z).mul (hasDerivAt_K0_eq_neg_K1 hz)).add
    ((I0_hasDerivAt_I1 z).mul (hasDerivAt_K1_eq_neg_K0_add_K2 hz))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The scaled order-zero Wronskian has zero derivative in the open right half-plane. -/
theorem hasDerivAt_mul_orderZeroWronskian {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ ↦ w * orderZeroWronskian w) 0 z := by
  have h := (hasDerivAt_id z).mul (hasDerivAt_orderZeroWronskian hz)
  apply h.congr_deriv
  simp only [id_eq]
  rw [orderZeroWronskian, I1_eq_half_mul_I0_sub_I2,
    K1_eq_z_div_two_mul_K2_sub_K0 hz]
  ring

/-- `z · W₀(z)` is constant throughout the open right half-plane. -/
theorem mul_orderZeroWronskian_eq {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    z * orderZeroWronskian z = w * orderZeroWronskian w := by
  let s : Set ℂ := {u : ℂ | 0 < u.re}
  let f : ℂ → ℂ := fun u ↦ u * orderZeroWronskian u
  have hopen : IsOpen s := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hpre : IsPreconnected s := (convex_halfSpace_re_gt 0).isPreconnected
  have hderiv : ∀ u ∈ s, HasDerivAt f 0 u := by
    intro u hu
    simpa only [f] using hasDerivAt_mul_orderZeroWronskian hu
  have hdiff : DifferentiableOn ℂ f s := by
    intro u hu
    exact (hderiv u hu).differentiableAt.differentiableWithinAt
  have hzero : s.EqOn (deriv f) 0 := by
    intro u hu
    exact (hderiv u hu).deriv
  exact hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hz hw

/-- The order-zero first-kind function takes the value `1` at the origin. -/
@[simp] theorem I0_zero : I0 0 = 1 := by
  unfold I0 regularizedHGFun regularizedHGFunSeries
  norm_num
  change FormalMultilinearSeries.ofScalarsSum (E := ℂ)
    (regularizedHGFunCoeff (0 : Multiset ℂ) {(1 : ℂ)}) 0 = 1
  simp [regularizedHGFunCoeff]

/-- The order-one first-kind function vanishes at the origin. -/
@[simp] theorem I1_zero : I1 0 = 0 := by
  simp [I1]

/-- Along the positive real axis, `I₀ (x) → 1` as `x ↓ 0`. -/
private theorem tendsto_I0_ofReal_zero :
    Tendsto (fun x : ℝ ↦ I0 (x : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hcomp : ContinuousAt (fun x : ℝ ↦ I0 (x : ℂ)) 0 :=
    (I0_analyticAt 0).continuousAt.comp_of_eq
      Complex.continuous_ofReal.continuousAt (by norm_num)
  simpa using hcomp.tendsto.mono_left
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)

/-- Along the positive real axis, `I₁ (x) → 0` as `x ↓ 0`. -/
private theorem tendsto_I1_ofReal_zero :
    Tendsto (fun x : ℝ ↦ I1 (x : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcomp : ContinuousAt (fun x : ℝ ↦ I1 (x : ℂ)) 0 :=
    (I1_hasDerivAt 0).continuousAt.comp_of_eq
      Complex.continuous_ofReal.continuousAt (by norm_num)
  simpa using hcomp.tendsto.mono_left
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)

/-- The product `x K₀ (x)` stays bounded (by `2`) as `x ↓ 0` along the positive reals; the
logarithmic blow-up of `K₀` is killed by the factor `x`. -/
private theorem isBoundedUnder_norm_x_mul_K0 :
    IsBoundedUnder (· ≤ ·) (nhdsWithin (0 : ℝ) (Ioi 0))
      ((‖·‖) ∘ fun x : ℝ ↦ (x : ℂ) * K0 (x : ℂ)) := by
  apply isBoundedUnder_of_eventually_le (a := 2)
  have hle_nhds : ∀ᶠ x in nhds (0 : ℝ), x ≤ 1 := Iic_mem_nhds (by norm_num)
  have hle : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0), x ≤ 1 :=
    hle_nhds.filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hle] with x hx hx1
  exact norm_x_mul_K0_le_two hx hx1

/-- The term `I₁ (x) · (x K₀ (x))` of the scaled Wronskian tends to `0` as `x ↓ 0`, the vanishing
factor `I₁` beating the bounded factor `x K₀`. -/
private theorem tendsto_I1_mul_xK0_zero :
    Tendsto (fun x : ℝ ↦ I1 (x : ℂ) * ((x : ℂ) * K0 (x : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_I1_ofReal_zero.zero_mul_isBoundedUnder_le isBoundedUnder_norm_x_mul_K0

/-- The term `I₀ (x) · (x K₁ (x))` of the scaled Wronskian tends to `1` as `x ↓ 0`; this supplies
the boundary value in the Wronskian identity `z W₀(z) = 1`. -/
private theorem tendsto_I0_mul_xK1_one :
    Tendsto (fun x : ℝ ↦ I0 (x : ℂ) * ((x : ℂ) * K1 (x : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  simpa using tendsto_I0_ofReal_zero.mul tendsto_x_mul_K1_nhdsWithin_zero

/-- The scaled order-zero Wronskian has boundary value one on the positive real axis. -/
theorem tendsto_x_mul_orderZeroWronskian :
    Tendsto (fun x : ℝ ↦ (x : ℂ) * orderZeroWronskian (x : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have h := tendsto_I1_mul_xK0_zero.add tendsto_I0_mul_xK1_one
  simpa only [zero_add, orderZeroWronskian] using h.congr'
    (Filter.Eventually.of_forall fun x ↦ by ring)

/-- The normalized order-zero Wronskian identity on the open right half-plane. -/
theorem orderZeroWronskian_eq_one_div {z : ℂ} (hz : 0 < z.re) :
    orderZeroWronskian z = 1 / z := by
  have heq : (fun x : ℝ ↦ (x : ℂ) * orderZeroWronskian (x : ℂ)) =ᶠ[
      nhdsWithin 0 (Ioi 0)] (fun _ : ℝ ↦ z * orderZeroWronskian z) := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact (mul_orderZeroWronskian_eq hz (by simpa using hx)).symm
  have hconst : Tendsto (fun _ : ℝ ↦ z * orderZeroWronskian z)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
    tendsto_x_mul_orderZeroWronskian.congr' heq
  have hmul : z * orderZeroWronskian z = 1 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  rw [eq_div_iff hz0]
  simpa [mul_comm] using hmul

/-- The order-zero Wronskian expressed by the order-zero/order-two cross product. -/
theorem orderZeroWronskian_eq_half_mul_cross {z : ℂ} (hz : 0 < z.re) :
    orderZeroWronskian z = z / 2 * (I0 z * K2 z - I2 z * K0 z) := by
  rw [orderZeroWronskian, I1_eq_half_mul_I0_sub_I2,
    K1_eq_z_div_two_mul_K2_sub_K0 hz]
  ring

/-- The normalized cross identity used in the Ponomarenko dispersion relation. -/
theorem besselCross_eq_two_div_sq {z : ℂ} (hz : 0 < z.re) :
    I0 z * K2 z - I2 z * K0 z = 2 / z ^ 2 := by
  have h := orderZeroWronskian_eq_one_div hz
  rw [orderZeroWronskian_eq_half_mul_cross hz] at h
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have h2 : z ^ 2 * (I0 z * K2 z - I2 z * K0 z) = 2 := by
    field_simp [hz0] at h
    exact h
  apply (eq_div_iff (pow_ne_zero 2 hz0)).2
  simpa [mul_comm] using h2

/-- The normalized order-zero derivative Wronskian. -/
theorem deriv_I0_mul_K0_sub_I0_mul_deriv_K0_eq_one_div
    {z : ℂ} (hz : 0 < z.re) :
    deriv I0 z * K0 z - I0 z * deriv K0 z = 1 / z := by
  rw [(I0_hasDerivAt_I1 z).deriv, (hasDerivAt_K0_eq_neg_K1 hz).deriv]
  simpa [orderZeroWronskian, sub_eq_add_neg] using orderZeroWronskian_eq_one_div hz

/-- The normalized order-two derivative Wronskian. -/
theorem deriv_I2_mul_K2_sub_I2_mul_deriv_K2_eq_one_div
    {z : ℂ} (hz : 0 < z.re) :
    deriv I2 z * K2 z - I2 z * deriv K2 z = 1 / z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  rw [deriv_I2 z hz0, (hasDerivAt_K2_eq_K0_sub_K2 hz).deriv,
    I1_eq_half_mul_I0_sub_I2]
  calc
    (z / 2 * (I0 z - I2 z) - 2 * I2 z / z) * K2 z -
        I2 z * (z / 2 * (K0 z - K2 z) - 2 / z * K2 z) =
        z / 2 * (I0 z * K2 z - I2 z * K0 z) := by
      field_simp [hz0]
      ring
    _ = orderZeroWronskian z := (orderZeroWronskian_eq_half_mul_cross hz).symm
    _ = 1 / z := orderZeroWronskian_eq_one_div hz

/-- Derivative of the central `I1 K1` product in terms of the concrete dispersion. -/
theorem hasDerivAt_I1_mul_K1 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ ↦ I1 w * K1 w)
      (-(z / 2) * FastDynamo.ponomarenkoDispersion z) z := by
  apply ((I1_hasDerivAt z).mul (hasDerivAt_K1_eq_neg_K0_add_K2 hz)).congr_deriv
  rw [I1_eq_half_mul_I0_sub_I2, K1_eq_z_div_two_mul_K2_sub_K0 hz,
    FastDynamo.ponomarenkoDispersion_apply]
  ring

/-- Exact product-derivative representation of the concrete dispersion. -/
theorem ponomarenkoDispersion_eq_neg_two_div_mul_deriv_I1_mul_K1
    {z : ℂ} (hz : 0 < z.re) :
    FastDynamo.ponomarenkoDispersion z =
      -(2 / z) * deriv (fun w : ℂ ↦ I1 w * K1 w) z := by
  rw [(hasDerivAt_I1_mul_K1 hz).deriv]
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  field_simp [hz0]

end FastDynamo.ModifiedBessel

/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Centered Gaussian kernels and laws

Finite-dimensional real Gaussian kernels `exp (-s * ‖x‖²)` and their normalized
laws, including dimension zero. Definitions are total in `s`; probability and
integrability results explicitly require `s > 0`. The variance is `1 / (2 * s)`.
This is shared support for BKL arXiv:2610.05474v1, Section 2 and Theorem 3.1.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FunctionalInequalities.Probability.Gaussian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Unnormalized Gaussian smoothing kernel with inverse variance parameter `s`. -/
def kernel (s : ℝ) (x : V) : ℝ := Real.exp (-s * ‖x‖ ^ 2)

/-- The Gaussian kernel has the usual finite-dimensional mass, including
the zero-dimensional case. -/
theorem integral_kernel {s : ℝ} (hs : 0 < s) :
    ∫ x : V, kernel s x = (Real.pi / s) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  simpa only [kernel] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) hs

theorem integrable_kernel {s : ℝ} (hs : 0 < s) :
    Integrable (kernel (V := V) s) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (s : ℂ))
    (by simpa using hs) 0 (0 : V)
  have hnorm := h.norm
  convert hnorm using 1
  funext x
  simp only [kernel, neg_mul, inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero,
    Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Real.exp_eq_exp, neg_inj, mul_eq_mul_left_iff]
  left
  norm_cast

/-- Total mass of the unnormalized Gaussian at inverse variance `s`. -/
def mass (s : ℝ) : ℝ :=
  (Real.pi / s) ^ ((Module.finrank ℝ V : ℝ) / 2)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem mass_pos {s : ℝ} (hs : 0 < s) : 0 < mass (V := V) s := by
  unfold mass
  positivity

/-- The explicit nonnegative Gaussian probability density. -/
def normalizedKernel (s : ℝ) (x : V) : ℝ := kernel s x / mass (V := V) s

section GaussianKernelBounds

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem normalizedKernel_pos {s : ℝ} (hs : 0 < s) (x : V) :
    0 < normalizedKernel s x :=
  div_pos (Real.exp_pos _) (mass_pos hs)

theorem normalizedKernel_le_inv_mass {s : ℝ} (hs : 0 < s) (x : V) :
    normalizedKernel s x ≤ (mass (V := V) s)⁻¹ := by
  have hk : kernel s x ≤ 1 := by
    unfold kernel
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (sq_nonneg _)
  calc
    normalizedKernel s x = kernel s x / mass (V := V) s := rfl
    _ ≤ 1 / mass (V := V) s := div_le_div_of_nonneg_right hk (mass_pos hs).le
    _ = _ := one_div _

end GaussianKernelBounds

theorem integrable_normalizedKernel {s : ℝ} (hs : 0 < s) :
    Integrable (normalizedKernel (V := V) s) :=
  (integrable_kernel hs).div_const _

theorem integral_normalizedKernel {s : ℝ} (hs : 0 < s) :
    ∫ x : V, normalizedKernel s x = 1 := by
  rw [show (fun x : V => normalizedKernel s x) =
    (fun x => kernel s x / mass (V := V) s) from rfl,
    integral_div, integral_kernel hs]
  exact div_self (mass_pos hs).ne'

omit [FiniteDimensional ℝ V] in
theorem normalizedKernel_measurable (s : ℝ) :
    Measurable (normalizedKernel (V := V) s) := by
  unfold normalizedKernel kernel
  fun_prop

/-- The centered Gaussian law with inverse variance parameter `s`. -/
def law (s : ℝ) : Measure V :=
  (volume : Measure V).withDensity
    (fun x => ENNReal.ofReal (normalizedKernel s x))

theorem law_probability {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (law (V := V) s) := by
  rw [isProbabilityMeasure_iff]
  change (volume : Measure V).withDensity
    (fun x => ENNReal.ofReal (normalizedKernel s x)) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_normalizedKernel hs)
    (Filter.Eventually.of_forall fun x => (normalizedKernel_pos hs x).le)]
  rw [integral_normalizedKernel hs]
  simp

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kernel_pos (s : ℝ) (x : V) : 0 < kernel s x := Real.exp_pos _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem kernel_measurable (s : ℝ) : Measurable (kernel (V := V) s) := by
  unfold kernel
  fun_prop

section KernelConcavity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
/-- The Gaussian factor is log-concave for every nonnegative inverse variance. -/
theorem kernel_logConcave {s : ℝ} (hs : 0 ≤ s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    kernel s x ^ t * kernel s y ^ (1 - t) ≤
      kernel s (t • x + (1 - t) • y) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  have hcv : ConvexOn ℝ univ (fun z : V => ‖z‖ ^ 2) :=
    (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2)
  have hnorm := hcv.2 (mem_univ x) (mem_univ y) ht0.le ht1'
    (by linarith : t + (1 - t) = 1)
  have hmul := mul_le_mul_of_nonneg_left hnorm hs
  simp only [smul_eq_mul] at hmul
  have harg : (-s * ‖x‖ ^ 2) * t + (-s * ‖y‖ ^ 2) * (1 - t) ≤
      -s * ‖t • x + (1 - t) • y‖ ^ 2 := by
    calc
      (-s * ‖x‖ ^ 2) * t + (-s * ‖y‖ ^ 2) * (1 - t)
          = -(s * (t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2)) := by ring
      _ ≤ -(s * ‖t • x + (1 - t) • y‖ ^ 2) := neg_le_neg hmul
      _ = _ := by ring
  unfold kernel
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr harg

theorem normalizedKernel_logConcave {s : ℝ} (hs : 0 < s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedKernel s x ^ t * normalizedKernel s y ^ (1 - t) ≤
      normalizedKernel s (t • x + (1 - t) • y) := by
  let m := mass (V := V) s
  have hm : 0 < m := mass_pos hs
  have hden : m ^ t * m ^ (1 - t) = m := by
    rw [← Real.rpow_add hm]
    simp
  unfold normalizedKernel
  rw [Real.div_rpow (kernel_pos s x).le hm.le,
    Real.div_rpow (kernel_pos s y).le hm.le]
  calc
    kernel s x ^ t / m ^ t * (kernel s y ^ (1 - t) / m ^ (1 - t))
        = (kernel s x ^ t * kernel s y ^ (1 - t)) /
            (m ^ t * m ^ (1 - t)) := by ring
    _ = (kernel s x ^ t * kernel s y ^ (1 - t)) / m := by rw [hden]
    _ ≤ kernel s (t • x + (1 - t) • y) / m :=
      div_le_div_of_nonneg_right (kernel_logConcave hs.le x y ht0 ht1) hm.le

end KernelConcavity

/-- The extended-real Gaussian factor, in the convention of the convolution integral. -/
def ekernel (s : ℝ) (x : V) : ENNReal := ENNReal.ofReal (kernel s x)

/-- The extended-real normalized Gaussian factor. -/
def normalizedEkernel (s : ℝ) (x : V) : ENNReal :=
  ENNReal.ofReal (normalizedKernel s x)

section ExtendedKernelBounds

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem ekernel_pos (s : ℝ) (x : V) : 0 < ekernel s x :=
  ENNReal.ofReal_pos.mpr (kernel_pos s x)

theorem ekernel_le_one {s : ℝ} (hs : 0 ≤ s) (x : V) : ekernel s x ≤ 1 := by
  rw [ekernel, ENNReal.ofReal_le_one]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _)

end ExtendedKernelBounds

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem ekernel_measurable (s : ℝ) : Measurable (ekernel (V := V) s) :=
  (kernel_measurable s).ennreal_ofReal

omit [FiniteDimensional ℝ V] in
theorem normalizedEkernel_measurable (s : ℝ) :
    Measurable (normalizedEkernel (V := V) s) :=
  (normalizedKernel_measurable s).ennreal_ofReal

section ExtendedKernelConcavity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem ekernel_logConcave {s : ℝ} (hs : 0 ≤ s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ekernel s x ^ t * ekernel s y ^ (1 - t) ≤
      ekernel s (t • x + (1 - t) • y) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  rw [ekernel, ekernel, ekernel,
    ENNReal.ofReal_rpow_of_nonneg (kernel_pos s x).le ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (kernel_pos s y).le ht1',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (kernel_pos s x).le t)]
  exact ENNReal.ofReal_le_ofReal (kernel_logConcave hs x y ht0 ht1)

theorem normalizedEkernel_logConcave {s : ℝ} (hs : 0 < s) (x y : V)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedEkernel s x ^ t * normalizedEkernel s y ^ (1 - t) ≤
      normalizedEkernel s (t • x + (1 - t) • y) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  rw [normalizedEkernel, normalizedEkernel, normalizedEkernel,
    ENNReal.ofReal_rpow_of_nonneg (normalizedKernel_pos hs x).le ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (normalizedKernel_pos hs y).le ht1',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (normalizedKernel_pos hs x).le t)]
  exact ENNReal.ofReal_le_ofReal (normalizedKernel_logConcave hs x y ht0 ht1)

end ExtendedKernelConcavity

end FunctionalInequalities.Probability.Gaussian

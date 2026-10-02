/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Zero-mass logarithmic energy inequality for finite measures on `ℂ`
(the proof notes (12), GLOBAL-INTEGRAL-v1 §4): for finite measures `μ_k` and real weights `w_k` with
`Σ w_k μ_k(ℂ) = 0`, integrable `log|z − w|` and null diagonals,
`Σ_{k,l} w_k w_l ∫∫ log|z − w| dμ_k dμ_l ≤ 0`.

Gaussian positivity for the truncated kernel `L_{a,b}(r) = ½∫_a^b (e^{-s} − e^{-s r²})/s ds`,
then dominated
convergence `L_{1/(n+1), n+1} → log`. The scalar kernel facts and the Gaussian convolution on
`ℂ` are
adapted from the Li₂(1/2) formalization (Li2Unified/Modular/Positive/Packed/P183–P185,
themselves a port of
mo271/Zeta5 Apery/Gaussian, Kernel, ZeroMass, EnergyLimit, Apache-2.0); the measure-level
Gaussian positivity is
new here (the Li₂ version needs bounded continuous curve densities; our comparison density is
unbounded). -/

@[expose] public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-! ### The truncated kernel (adapted from Li2Unified/Modular/Positive/Packed/P184–P185) -/

/-- The truncated logarithmic kernel `L_{a,b}(r)`. -/
def Ltr (a b r : ℝ) : ℝ :=
  (1 / 2) * ∫ s in a..b, (Real.exp (-s) - Real.exp (-s * r ^ 2)) / s

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma integral_exp_neg_mul' {k : ℝ} (hk : k ≠ 0) (c d : ℝ) :
    ∫ x in c..d, Real.exp (-k * x) = (Real.exp (-k * c) - Real.exp (-k * d)) / k := by
  have h : ∀ x ∈ uIcc c d, HasDerivAt (fun x => -Real.exp (-k * x) / k) (Real.exp (-k * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -k * x) (-k) x := by
      simpa using! (hasDerivAt_id x).const_mul (-k)
    have h2 := (h1.exp.neg).div_const k
    refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h2
      (Filter.Eventually.of_forall fun _ => rfl)) ?_
    field_simp
  rw [integral_eq_sub_of_hasDerivAt h (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

-- adapted from Li2Unified/Modular/Positive/Packed/P183.lean
lemma intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuousOn

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma intervalIntegral_swap_of_continuous' {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    (a b c d : ℝ) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · exact intervalIntegral_swap_of_continuous hf hab hcd
  · rw [integral_symm d c]
    simp_rw [integral_symm d c, intervalIntegral.integral_neg]
    rw [intervalIntegral_swap_of_continuous hf hab hcd]
  · rw [integral_symm b a]
    simp_rw [integral_symm b a]
    rw [intervalIntegral.integral_neg, intervalIntegral_swap_of_continuous hf hab hcd]
  · rw [integral_symm b a, integral_symm d c]
    simp_rw [integral_symm b a, integral_symm d c, intervalIntegral.integral_neg]
    rw [intervalIntegral_swap_of_continuous hf hab hcd]

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma Ltr_eq_v {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    Ltr a b r = (1 / 2) * ∫ v in (1 : ℝ)..r ^ 2, (Real.exp (-a * v) - Real.exp (-b * v)) / v := by
  unfold Ltr
  congr 1
  have e1 : ∀ s ∈ uIcc a b, (Real.exp (-s) - Real.exp (-s * r ^ 2)) / s =
      ∫ v in (1 : ℝ)..r ^ 2, Real.exp (-s * v) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    rw [integral_exp_neg_mul' (ha.trans_le hs.1).ne', mul_one]
  rw [integral_congr e1]
  rw [intervalIntegral_swap_of_continuous' (f := fun s v => Real.exp (-s * v)) (by fun_prop)]
  apply integral_congr
  intro v hv
  have hv0 : 0 < v := by
    rcases le_total 1 (r ^ 2) with h | h
    · rw [uIcc_of_le h] at hv; linarith [hv.1]
    · rw [uIcc_of_ge h] at hv; exact lt_of_lt_of_le (by positivity) hv.1
  simp only
  simp_rw [show ∀ s : ℝ, -s * v = -v * s from fun s => by ring]
  rw [integral_exp_neg_mul' hv0.ne']

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma Ltr_integrand_bounds {a b v : ℝ} (ha : 0 < a) (hab : a ≤ b) (hv : 0 < v) :
    0 ≤ (Real.exp (-a * v) - Real.exp (-b * v)) / v ∧
      (Real.exp (-a * v) - Real.exp (-b * v)) / v ≤ 1 / v := by
  constructor
  · apply div_nonneg _ hv.le
    rw [sub_nonneg]
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply div_le_div_of_nonneg_right _ hv.le
    have := Real.exp_pos (-b * v)
    have := Real.exp_le_one_iff.mpr (show -a * v ≤ 0 by nlinarith)
    linarith

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma intervalIntegrable_of_pos {F : ℝ → ℝ} (hF : Continuous F) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) : IntervalIntegrable (fun v => F v / v) volume c d := by
  apply ContinuousOn.intervalIntegrable
  refine hF.continuousOn.div continuousOn_id fun v hv => ?_
  rcases le_total c d with h | h
  · rw [uIcc_of_le h] at hv; exact (hc.trans_le hv.1).ne'
  · rw [uIcc_of_ge h] at hv; exact (hd.trans_le hv.1).ne'

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma log_eq_half_integral {r : ℝ} (hr : 0 < r) :
    Real.log r = (1 / 2) * ∫ v in (1 : ℝ)..r ^ 2, 1 / v := by
  rw [integral_one_div_of_pos one_pos (by positivity), div_one, Real.log_pow]
  push_cast; ring

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
/-- `|L_{a,b}(r)| ≤ |log r|` for `r > 0`. -/
lemma abs_Ltr_le {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    |Ltr a b r| ≤ |Real.log r| := by
  rw [Ltr_eq_v ha hab hr]
  have hlog := log_eq_half_integral hr
  have hF : ∀ c d : ℝ, 0 < c → 0 < d → IntervalIntegrable
      (fun v => (Real.exp (-a * v) - Real.exp (-b * v)) / v) volume c d :=
    fun c d hc hd => intervalIntegrable_of_pos (by fun_prop) hc hd
  have hG : ∀ c d : ℝ, 0 < c → 0 < d → IntervalIntegrable (fun v : ℝ => 1 / v) volume c d :=
    fun c d hc hd => intervalIntegrable_of_pos continuous_const hc hd
  have hr2 : 0 < r ^ 2 := by positivity
  rcases le_total 1 (r ^ 2) with h | h
  · have h1 : 0 ≤ ∫ v in (1:ℝ)..r ^ 2, (Real.exp (-a * v) - Real.exp (-b * v)) / v :=
      integral_nonneg h fun v hv => (Ltr_integrand_bounds ha hab (by linarith [hv.1])).1
    have h2 : (∫ v in (1:ℝ)..r ^ 2, (Real.exp (-a * v) - Real.exp (-b * v)) / v) ≤
        ∫ v in (1:ℝ)..r ^ 2, 1 / v :=
      integral_mono_on h (hF _ _ one_pos hr2) (hG _ _ one_pos hr2)
        fun v hv => (Ltr_integrand_bounds ha hab (by linarith [hv.1])).2
    have hr1 : 0 ≤ Real.log r := Real.log_nonneg (by nlinarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hr1, hlog]
    linarith
  · rw [integral_symm (r ^ 2) 1]
    rw [integral_symm (r ^ 2) 1] at hlog
    have h1 : 0 ≤ ∫ v in r ^ 2..(1:ℝ), (Real.exp (-a * v) - Real.exp (-b * v)) / v :=
      integral_nonneg h fun v hv => (Ltr_integrand_bounds ha hab (by linarith [hv.1])).1
    have h2 : (∫ v in r ^ 2..(1:ℝ), (Real.exp (-a * v) - Real.exp (-b * v)) / v) ≤
        ∫ v in r ^ 2..(1:ℝ), 1 / v :=
      integral_mono_on h (hF _ _ hr2 one_pos) (hG _ _ hr2 one_pos)
        fun v hv => (Ltr_integrand_bounds ha hab (by linarith [hv.1])).2
    have hr1 : Real.log r ≤ 0 := Real.log_nonpos hr.le (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hr1, hlog]
    linarith

-- adapted from Li2Unified/Modular/Positive/Packed/P184.lean
lemma continuous_inv_max {a : ℝ} (ha : 0 < a) : Continuous fun s : ℝ => (max s a)⁻¹ :=
  (continuous_id.max continuous_const).inv₀ fun _s => (lt_max_of_lt_right ha).ne'

-- adapted from Li2Unified/Modular/Positive/Packed/P184.lean
lemma Ltr_eq_max {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    Ltr a b r = (1 / 2) * ∫ s in a..b, (Real.exp (-s) - Real.exp (-s * r ^ 2)) * (max s a)⁻¹ := by
  unfold Ltr
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  simp only [max_eq_left hs.1, div_eq_mul_inv]

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma continuous_Ltr {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Continuous fun r => Ltr a b r := by
  simp_rw [Ltr_eq_max hab]
  have hinv := continuous_inv_max ha
  refine continuous_const.mul (continuous_parametric_intervalIntegral_of_continuous'
    (f := fun r s => (Real.exp (-s) - Real.exp (-s * r ^ 2)) * (max s a)⁻¹) ?_ a b)
  have h1 : Continuous fun p : ℝ × ℝ => Real.exp (-p.2) - Real.exp (-p.2 * p.1 ^ 2) := by fun_prop
  exact h1.mul (hinv.comp continuous_snd)

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma log_sub_Ltr {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    Real.log r - Ltr a b r =
      (1 / 2) * ∫ v in (1 : ℝ)..r ^ 2, (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v := by
  rw [Ltr_eq_v ha hab hr, log_eq_half_integral hr, ← mul_sub, ← integral_sub
    (intervalIntegrable_of_pos continuous_const one_pos (by positivity))
    (intervalIntegrable_of_pos (by fun_prop) one_pos (by positivity))]
  congr 1
  apply integral_congr
  intro v _
  simp only
  ring

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma diff_integrand_bounds {a b m v : ℝ} (ha : 0 < a) (hab : a ≤ b) (hm : 0 < m) (hv : m ≤ v) :
    0 ≤ (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v ∧
      (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v ≤ a + Real.exp (-b * m) / m := by
  have hv0 : 0 < v := hm.trans_le hv
  have h1 : Real.exp (-a * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : 0 < Real.exp (-b * v) := Real.exp_pos _
  have h3 : 1 - a * v ≤ Real.exp (-a * v) := by
    have := Real.add_one_le_exp (-a * v); linarith
  have h4 : Real.exp (-b * v) ≤ Real.exp (-b * m) := Real.exp_le_exp.mpr (by nlinarith)
  constructor
  · apply div_nonneg _ hv0.le; linarith
  · rw [div_le_iff₀ hv0]
    have h5 : Real.exp (-b * m) / m * v ≥ Real.exp (-b * m) := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hm]
      exact mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    nlinarith

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
lemma abs_log_sub_Ltr_le {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    |Real.log r - Ltr a b r| ≤
      (1 / 2) * ((a + Real.exp (-b * min 1 (r ^ 2)) / min 1 (r ^ 2)) * |r ^ 2 - 1|) := by
  rw [log_sub_Ltr ha hab hr, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hm : 0 < min 1 (r ^ 2) := lt_min one_pos (by positivity)
  have := norm_integral_le_of_norm_le_const (a := 1) (b := r ^ 2)
    (C := a + Real.exp (-b * min 1 (r ^ 2)) / min 1 (r ^ 2))
    (f := fun v => (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v) (fun v hv => by
      have hv' : min 1 (r ^ 2) ≤ v := by
        rcases le_total 1 (r ^ 2) with h | h
        · rw [uIoc_of_le h] at hv; exact (min_le_left _ _).trans hv.1.le
        · rw [uIoc_of_ge h] at hv; exact (min_le_right _ _).trans hv.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (diff_integrand_bounds ha hab hm hv').1]
      exact (diff_integrand_bounds ha hab hm hv').2)
  rwa [Real.norm_eq_abs] at this

-- adapted from Li2Unified/Modular/Positive/Packed/P185.lean
/-- Convergence of the truncated kernel to the logarithm. -/
lemma tendsto_Ltr {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) r) atTop (𝓝 (Real.log r)) := by
  have hm : 0 < min 1 (r ^ 2) := lt_min one_pos (by positivity)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, ‖Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) r - Real.log r‖ ≤
      (1 / 2) * ((1 / ((n : ℝ) + 1) + Real.exp (-((n : ℝ) + 1) * min 1 (r ^ 2)) / min 1 (r ^ 2)) *
        |r ^ 2 - 1|) := by
    intro n
    rw [Real.norm_eq_abs, abs_sub_comm]
    refine abs_log_sub_Ltr_le (by positivity) ?_ hr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1) * min 1 (r ^ 2)) / min 1 (r ^ 2))
      atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * min 1 (r ^ 2)) atTop atTop := by
      apply Tendsto.atTop_mul_const hm
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have := (tendsto_exp_neg_atTop_nhds_zero.comp h3).div_const (min 1 (r ^ 2))
    rw [zero_div] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    ring_nf
  have := ((h1.add h2).mul_const |r ^ 2 - 1|).const_mul (1 / 2)
  simpa using! this

/-! ### Gaussians on `ℂ` (adapted from Li2Unified/Modular/Positive/Packed/P183–P184) -/

-- adapted from Li2Unified/Modular/Positive/Packed/P183.lean
lemma integral_gaussian_sub {b : ℝ} (c : ℝ) :
    ∫ x : ℝ, Real.exp (-b * (x - c) ^ 2) = Real.sqrt (π / b) := by
  rw [integral_sub_right_eq_self (fun x => Real.exp (-b * x ^ 2)) c]
  exact integral_gaussian b

-- adapted from Li2Unified/Modular/Positive/Packed/P183.lean
lemma integrable_gaussian_sub {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * (x - c) ^ 2)) := by
  have := (integrable_exp_neg_mul_sq hb).comp_sub_right c
  simpa using! this

-- adapted from Li2Unified/Modular/Positive/Packed/P183.lean
lemma gaussian_conv_one (s a b : ℝ) :
    ∫ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.sqrt (π / (4 * s)) * Real.exp (-s * (a - b) ^ 2) := by
  have : ∀ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.exp (-(4 * s) * (x - (a + b) / 2) ^ 2) * Real.exp (-s * (a - b) ^ 2) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [this]
  rw [MeasureTheory.integral_mul_const, integral_gaussian_sub]

-- adapted from Li2Unified/Modular/Positive/Packed/P183.lean
lemma normSq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

-- adapted from Li2Unified/Modular/Positive/Packed/P183.lean
/-- The completing-the-square identity on `ℂ`. -/
lemma gaussian_conv {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ∫ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      π / (4 * s) * Real.exp (-s * ‖z - w‖ ^ 2) := by
  have h := Complex.volume_preserving_equiv_real_prod
  have key : ∀ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      (Real.exp (-(2 * s) * (z.re - u.re) ^ 2) * Real.exp (-(2 * s) * (w.re - u.re) ^ 2)) *
      (Real.exp (-(2 * s) * (z.im - u.im) ^ 2) * Real.exp (-(2 * s) * (w.im - u.im) ^ 2)) := by
    intro u
    rw [normSq_eq, normSq_eq]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  simp_rw [key]
  have e := h.integral_comp' (fun p : ℝ × ℝ =>
      (Real.exp (-(2 * s) * (z.re - p.1) ^ 2) * Real.exp (-(2 * s) * (w.re - p.1) ^ 2)) *
      (Real.exp (-(2 * s) * (z.im - p.2) ^ 2) * Real.exp (-(2 * s) * (w.im - p.2) ^ 2)))
  simp only [Complex.measurableEquivRealProd_apply] at e
  rw [e, Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-(2 * s) * (z.re - x) ^ 2) *
      Real.exp (-(2 * s) * (w.re - x) ^ 2))
    (fun y : ℝ => Real.exp (-(2 * s) * (z.im - y) ^ 2) * Real.exp (-(2 * s) * (w.im - y) ^ 2)),
    gaussian_conv_one s _ _, gaussian_conv_one s _ _, normSq_eq]
  simp only [Complex.sub_re, Complex.sub_im]
  rw [mul_mul_mul_comm, ← Real.sqrt_mul (by positivity), ← Real.exp_add, ← sq,
    Real.sqrt_sq (by positivity)]
  congr 2
  ring

-- adapted from Li2Unified/Modular/Positive/Packed/P184.lean
lemma integrable_gaussC {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Integrable (fun u : ℂ => Real.exp (-c * ‖z - u‖ ^ 2)) := by
  have e : (fun u : ℂ => Real.exp (-c * ‖z - u‖ ^ 2)) =
      (fun p : ℝ × ℝ => Real.exp (-c * (p.1 - z.re) ^ 2) * Real.exp (-c * (p.2 - z.im) ^ 2)) ∘
        Complex.measurableEquivRealProd := by
    funext u
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, normSq_eq,
      Complex.sub_re, Complex.sub_im, ← Real.exp_add]
    congr 1; ring
  rw [e, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding, Measure.volume_eq_prod]
  exact (integrable_gaussian_sub hc z.re).mul_prod (integrable_gaussian_sub hc z.im)

/-! ### Gaussian positivity for finite measures (new) -/

section gauss
variable {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The Gaussian smoothing of a measure. -/
def gM (μ : Measure ℂ) (t : ℝ) (u : ℂ) : ℝ := ∫ z, Real.exp (-(2 * t) * ‖z - u‖ ^ 2) ∂μ

/-- The integrand of the Gaussian convolution. -/
def gF (t : ℝ) (q : (ℂ × ℂ) × ℂ) : ℝ :=
  Real.exp (-(2 * t) * ‖q.1.1 - q.2‖ ^ 2) * Real.exp (-(2 * t) * ‖q.1.2 - q.2‖ ^ 2)

theorem continuous_gF (t : ℝ) : Continuous (gF t) := by unfold gF; fun_prop

theorem integral_gF {t : ℝ} (ht : 0 < t) (p : ℂ × ℂ) :
    ∫ u, gF t (p, u) = π / (4 * t) * Real.exp (-t * ‖p.1 - p.2‖ ^ 2) :=
  gaussian_conv ht p.1 p.2

theorem integrable_gF_slice {t : ℝ} (ht : 0 < t) (p : ℂ × ℂ) :
    Integrable (fun u => gF t (p, u)) := by
  refine (integrable_gaussC (show 0 < 2 * t by positivity) p.2).mono'
    ((continuous_gF t).comp (Continuous.prodMk_right p)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [gF, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have h1 : Real.exp (-(2 * t) * ‖p.1 - u‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - u‖])
  have : 0 < Real.exp (-(2 * t) * ‖p.2 - u‖ ^ 2) := Real.exp_pos _
  nlinarith

theorem integrable_gF {t : ℝ} (ht : 0 < t) : Integrable (gF t) ((μ.prod ν).prod volume) := by
  rw [integrable_prod_iff (continuous_gF t).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun p => integrable_gF_slice ht p, ?_⟩
  have e : (fun p : ℂ × ℂ => ∫ u, ‖gF t (p, u)‖) =
      fun p => π / (4 * t) * Real.exp (-t * ‖p.1 - p.2‖ ^ 2) := by
    funext p
    rw [← integral_gF ht p]
    congr 1; funext u
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold gF; positivity)]
  rw [e]
  refine (integrable_const (π / (4 * t))).mono' (by fun_prop) (Filter.Eventually.of_forall fun p
    => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - p.2‖])
  have hc : 0 < π / (4 * t) := by positivity
  nlinarith

theorem gM_mul_eq {t : ℝ} (u : ℂ) :
    ∫ p, gF t (p, u) ∂(μ.prod ν) = gM μ t u * gM ν t u := by
  unfold gF gM
  exact integral_prod_mul (fun z => Real.exp (-(2 * t) * ‖z - u‖ ^ 2))
    (fun w => Real.exp (-(2 * t) * ‖w - u‖ ^ 2))

theorem integrable_gM_mul {t : ℝ} (ht : 0 < t) : Integrable (fun u => gM μ t u * gM ν t u) := by
  have := (integrable_gF (μ := μ) (ν := ν) ht).integral_prod_right
  exact this.congr (Filter.Eventually.of_forall fun u => gM_mul_eq u)

/-- `∫∫ e^{-t|z−w|²} dμ dν = (4t/π) ∫ g_μ g_ν`. -/
theorem gauss_pair_eq {t : ℝ} (ht : 0 < t) :
    ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂(μ.prod ν) = (4 * t / π) * ∫ u, gM μ t u * gM ν t u := by
  have hpi : 0 < π := Real.pi_pos
  have h1 : ∀ p : ℂ × ℂ, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) = (4 * t / π) * ∫ u, gF t (p, u) := by
    intro p; rw [integral_gF ht p]; field_simp
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have hsw := integral_integral_swap (μ := μ.prod ν) (ν := volume) (f := fun p u => gF t (p, u))
    (integrable_gF ht)
  rw [hsw]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => gM_mul_eq u)

/-- Gaussian positivity of a signed finite combination. -/
theorem gauss_energy_nonneg {ι : Type*} [Fintype ι] (m : ι → Measure ℂ) [∀ k, IsFiniteMeasure (m k)]
    (w : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑ k, ∑ l, w k * w l * ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂((m k).prod (m l)) := by
  have hpi : 0 < π := Real.pi_pos
  have hI : ∀ k l, Integrable (fun u => w k * gM (m k) t u * (w l * gM (m l) t u)) := by
    intro k l
    exact ((integrable_gM_mul (μ := m k) (ν := m l) ht).const_mul (w k * w l)).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have e : (∑ k, ∑ l, w k * w l * ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂((m k).prod (m l))) =
      (4 * t / π) * ∫ u, (∑ k, w k * gM (m k) t u) ^ 2 := by
    simp_rw [gauss_pair_eq ht, sq, Finset.sum_mul_sum]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hI k l)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun l _ => hI k l), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (fun u => w k * gM (m k) t u * (w l * gM (m l) t u)) =
        fun u => (w k * w l) * (gM (m k) t u * gM (m l) t u) := by funext u; ring
    rw [this, MeasureTheory.integral_const_mul]
    ring
  rw [e]
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

end gauss

/-! ### The truncated kernel against finite measures -/

section trunc
variable {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The integrand of `Ltr` as a function of `(p, s)`. -/
def ltrF (p : ℂ × ℂ) (s : ℝ) : ℝ := (Real.exp (-s) - Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) / s

theorem measurable_ltrF : Measurable (Function.uncurry ltrF) := by
  unfold ltrF; fun_prop

theorem integrable_ltrF {α β : ℝ} (hα : 0 < α) :
    Integrable (Function.uncurry ltrF) ((μ.prod ν).prod (volume.restrict (Ioc α β))) := by
  refine (integrable_const (2 / α)).mono' measurable_ltrF.aestronglyMeasurable ?_
  have hmem : ∀ᵐ q ∂((μ.prod ν).prod (volume.restrict (Ioc α β))), q.2 ∈ Ioc α β :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hmem] with q hq
  have hs : 0 < q.2 := hα.trans hq.1
  simp only [Function.uncurry, ltrF, Real.norm_eq_abs, abs_div, abs_of_pos hs]
  have h1 : |Real.exp (-q.2) - Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2)| ≤ 2 := by
    have e1 : Real.exp (-q.2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have e2 : Real.exp (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖q.1.1 - q.1.2‖])
    have := Real.exp_pos (-q.2)
    have := Real.exp_pos (-q.2 * ‖q.1.1 - q.1.2‖ ^ 2)
    rw [abs_le]; constructor <;> linarith
  rw [div_le_div_iff₀ hs hα]
  nlinarith [hq.1]

/-- `∫ Ltr(|z − w|) dμ dν = ½ ∫_α^β ∫ ltrF`. -/
theorem integral_Ltr_eq {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ p, Ltr α β ‖p.1 - p.2‖ ∂(μ.prod ν) =
      (1 / 2) * ∫ s in Ioc α β, ∫ p, ltrF p s ∂(μ.prod ν) := by
  have e : ∀ p : ℂ × ℂ, Ltr α β ‖p.1 - p.2‖ = (1 / 2) * ∫ s in Ioc α β, ltrF p s := by
    intro p; unfold Ltr ltrF; rw [intervalIntegral.integral_of_le hαβ]
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_integral_swap (integrable_ltrF hα)

theorem integral_ltrF {s : ℝ} (hs : 0 ≤ s) :
    ∫ p, ltrF p s ∂(μ.prod ν) =
      (Real.exp (-s) * (μ.real univ * ν.real univ) -
        ∫ p, Real.exp (-s * ‖p.1 - p.2‖ ^ 2) ∂(μ.prod ν)) / s := by
  unfold ltrF
  have hint : Integrable (fun p : ℂ × ℂ => Real.exp (-s * ‖p.1 - p.2‖ ^ 2)) (μ.prod ν) := by
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - p.2‖])
  rw [MeasureTheory.integral_div, integral_sub (integrable_const _) hint,
    MeasureTheory.integral_const,
    smul_eq_mul]
  congr 2
  rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
  simp only [Measure.real]
  ring

end trunc

/-- Zero-mass logarithmic energy inequality for a finite signed combination of finite measures
on `ℂ`. -/
theorem zero_mass_energy_nonpos {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ)
    [∀ k, IsFiniteMeasure (μ k)] (w : ι → ℝ)
    (hmass : ∑ k, w k * (μ k).real Set.univ = 0)
    (hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((μ k).prod (μ l)))
    (hdiag : ∀ k l, ∀ᵐ p ∂((μ k).prod (μ l)), p.1 ≠ p.2) :
    ∑ k, ∑ l, w k * w l * ∫ p, Real.log ‖p.1 - p.2‖ ∂((μ k).prod (μ l)) ≤ 0 := by
  have htrunc : ∀ n : ℕ, ∑ k, ∑ l, w k * w l *
      ∫ p, Ltr (1 / ((n:ℝ) + 1)) ((n:ℝ) + 1) ‖p.1 - p.2‖ ∂((μ k).prod (μ l)) ≤ 0 := by
    intro n
    have hα : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    have hαβ : 1 / ((n:ℝ) + 1) ≤ (n:ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    simp_rw [integral_Ltr_eq hα hαβ]
    set S := Ioc (1 / ((n:ℝ) + 1)) ((n:ℝ) + 1)
    have hΦ : ∀ k l, Integrable (fun x => ∫ p, ltrF p x ∂((μ k).prod (μ l))) (volume.restrict S) :=
      fun k l => (integrable_ltrF (μ := μ k) (ν := μ l) hα).integral_prod_right
    have hΦ' : ∀ k l, Integrable (fun x => w k * w l * ∫ p, ltrF p x ∂((μ k).prod (μ l)))
        (volume.restrict S) := fun k l => (hΦ k l).const_mul _
    have e : (∑ k, ∑ l, w k * w l * ((1 / 2) * ∫ x in S, ∫ p, ltrF p x ∂((μ k).prod (μ l)))) =
        (1 / 2) * ∫ x in S, ∑ k, ∑ l, w k * w l * ∫ p, ltrF p x ∂((μ k).prod (μ l)) := by
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hΦ' k l)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ (fun l _ => hΦ' k l), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [MeasureTheory.integral_const_mul]
      ring
    rw [e]
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply setIntegral_nonpos measurableSet_Ioc
    intro x hx
    have hx0 : 0 < x := hα.trans hx.1
    simp_rw [integral_ltrF hx0.le]
    have hQ := gauss_energy_nonneg μ w hx0
    have halg : (∑ k, ∑ l, w k * w l * ((Real.exp (-x) * ((μ k).real univ * (μ l).real univ) -
        ∫ p, Real.exp (-x * ‖p.1 - p.2‖ ^ 2) ∂((μ k).prod (μ l))) / x)) =
        (Real.exp (-x) * (∑ k, w k * (μ k).real univ) ^ 2 -
          ∑ k, ∑ l, w k * w l * ∫ p, Real.exp (-x * ‖p.1 - p.2‖ ^ 2) ∂((μ k).prod (μ l))) / x := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [halg, hmass]
    apply div_nonpos_of_nonpos_of_nonneg _ hx0.le
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub,
      Left.neg_nonpos_iff]
    exact hQ
  have hlim : Tendsto (fun n : ℕ => ∑ k, ∑ l, w k * w l *
      ∫ p, Ltr (1 / ((n:ℝ) + 1)) ((n:ℝ) + 1) ‖p.1 - p.2‖ ∂((μ k).prod (μ l))) atTop
      (𝓝 (∑ k, ∑ l, w k * w l * ∫ p, Real.log ‖p.1 - p.2‖ ∂((μ k).prod (μ l)))) := by
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
    refine Tendsto.const_mul _ ?_
    have hα : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => by positivity
    have hαβ : ∀ n : ℕ, 1 / ((n:ℝ) + 1) ≤ (n:ℝ) + 1 := fun n => by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    refine tendsto_integral_of_dominated_convergence (fun p => |Real.log ‖p.1 - p.2‖|)
      (fun n => ((continuous_Ltr (hα n) (hαβ n)).comp
        (continuous_fst.sub continuous_snd).norm).aestronglyMeasurable) (hint k l).abs ?_ ?_
    · intro n
      filter_upwards [hdiag k l] with p hp
      rw [Real.norm_eq_abs]
      exact abs_Ltr_le (hα n) (hαβ n) (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
    · filter_upwards [hdiag k l] with p hp
      exact tendsto_Ltr (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  exact le_of_tendsto' hlim htrunc

end
end Zeta32.Analytic.EnergyI

end

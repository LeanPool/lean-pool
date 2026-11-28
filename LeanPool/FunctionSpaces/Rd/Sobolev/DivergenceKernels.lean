/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.DilationFamilies
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Divergence kernels

Let `V` be a finite-dimensional real inner product space of dimension `n`, such as `ℝ^d`, with
Lebesgue measure and an orthonormal basis `(e_i)`, and let `m_c(x) = c^n m(c x)` be the
dilations (`Rd.dilate`).

* **Smoothness of parametric integrals**
  (`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff`): if `(x, t) ↦ F(x, t)` is
  smooth, so is `x ↦ ∫_a^b F(x, t) dt`, with the derivative under the integral sign for `C^1`
  integrands (`intervalIntegral.hasFDerivAt_integral_of_contDiff`). Mathlib has the derivative at
  one point and the continuity; smoothness follows by induction on the order.
* **The dilation identity** (`Rd.sum_fderiv_divergenceKernel`): for `m ∈ C^1`, Euler's identity
  `d/ds m_{e^s}(x) = n m_{e^s}(x) + D(m_{e^s})(x) x` (`Rd.hasDerivAt_dilate_exp`) and the
  fundamental theorem of calculus give, with the dilation average
  `A_m(x) = ∫_0^{log 2} m_{e^s}(x) ds = ∫_1^2 t⁻¹ m_t(x) dt` (`Rd.dilationAverage`,
  `Rd.dilationAverage_eq_integral_inv_mul`) and the
  divergence kernels `K_i(x) = ⟪e_i, x⟫ A_m(x)` (`Rd.divergenceKernel`),
  `m_2 - m = ∑_i ∂_{e_i} K_i`, since `∑_i ∂_{e_i} (⟪e_i, ·⟫ A)(x) = n A(x) + DA(x) x`
  (`Rd.sum_fderiv_inner_mul`); at every scale for the dilates
  (`Rd.sum_lineDerivOp_schwartzDilate_divergenceSchwartz`).
* **Support and mean**: `K_i(x) ≠ 0` only if `m(t x) ≠ 0` for some `t ∈ [1, 2]`
  (`Rd.divergenceKernel_eq_zero`), so the `K_i` of a smooth compactly supported `m` are Schwartz
  functions (`Rd.divergenceSchwartz`). A kernel that vanishes outside a closed set `S` with
  `c y ∈ S ⇒ y ∈ S` for `c ≥ 1` has its dyadic dilates supported in `S`
  (`Rd.tsupport_dilate_two_pow_subset`), and `∫ K_i = 0` if the first moments of `m` vanish
  (`Rd.integral_divergenceKernel`, with the first moments of dilates
  `Rd.integral_inner_mul_dilate`),
  as they do for the moment kernels of order two (`Rd.integral_inner_mul_momentKernel_two`).
* **Calderón–Zygmund families** (`Rd.isCZFamily_dilate_of_integral_eq_zero`): for a Schwartz
  function `G` with `∫ G = 0`, `|𝓕G(η)| ≤ C min(‖η‖, ‖η‖⁻¹)` (`Rd.enorm_fourier_le_mul_min`), so
  the dilates `G_{2^j}` have the Fourier overlap `4 C²` (`Rd.meanZeroOverlap`); in particular the
  dilated divergence kernels form Calderón–Zygmund families
  (`Rd.isCZFamily_divergenceSchwartz`).
* **The local means kernels as dilation differences** (`Rd.LocalMeansBump.kernel_succ_eq_dilate`):
  for a bump with moment kernel `m` of any order, `k_{j+1} = (m_2 - m)_{2^j}`, the identity that
  the divergence kernels of `m_2 - m` turn into derivatives.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real

/-! ### Smoothness of parametric integrals -/

section ParametricIntegral

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

namespace intervalIntegral

omit [FiniteDimensional ℝ H] in
/-- The partial derivative `(x, t) ↦ D_x F(x, t)` of a jointly `C^1` integrand is continuous. -/
private theorem continuous_fderiv_fst_of_contDiff {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : H → ℝ → E} (hF : ContDiff ℝ 1 (Function.uncurry F)) :
    Continuous fun q : H × ℝ => fderiv ℝ (fun x => F x q.2) q.1 := by
  have hpart : ContDiff ℝ 1 (Function.uncurry fun (q : H × ℝ) (x : H) => F x q.2) :=
    hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  exact (ContDiff.fderiv (n := 0) hpart contDiff_fst (by norm_num)).continuous

/-- **Differentiation under the integral sign** for a jointly `C^1` integrand: if
`(x, t) ↦ F x t` is `C^1` on `H × ℝ`, then `x ↦ ∫_a^b F x t dt` has the derivative
`∫_a^b D_x F x₀ t dt` at every `x₀`. The partial derivative is bounded on the compact set
`closedBall(x₀, 1) × [a, b]`, so Mathlib's
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`
applies. -/
theorem hasFDerivAt_integral_of_contDiff {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : H → ℝ → E} (hF : ContDiff ℝ 1 (Function.uncurry F)) (a b : ℝ)
    (x₀ : H) :
    HasFDerivAt (fun x => ∫ t in a..b, F x t) (∫ t in a..b, fderiv ℝ (fun x => F x t) x₀) x₀ := by
  have hcont := continuous_fderiv_fst_of_contDiff hF
  have hslice : ∀ t, ContDiff ℝ 1 fun x => F x t := fun t =>
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hK : IsCompact (closedBall x₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (bound := fun _ => C) (F' := fun x t => fderiv ℝ (fun x => F x t) x)
    (closedBall_mem_nhds x₀ one_pos) (Eventually.of_forall fun x =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
    (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun t ht x hx => hC (x, t) ⟨hx, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const (ae_of_all _ fun t _ x _ => ?_)
  exact ((hslice t).differentiable one_ne_zero x).hasFDerivAt

/-- **The derivative of a parametric integral, applied to a vector**: for a jointly `C^1`
integrand, `D(∫_a^b F(·, t) dt)(x) v = ∫_a^b D_x F(x, t) v dt`
(`intervalIntegral.hasFDerivAt_integral_of_contDiff` and Mathlib's
`ContinuousLinearMap.intervalIntegral_apply`). -/
theorem fderiv_integral_apply_of_contDiff {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : H → ℝ → E} (hF : ContDiff ℝ 1 (Function.uncurry F)) (a b : ℝ)
    (x v : H) :
    fderiv ℝ (fun x => ∫ t in a..b, F x t) x v = ∫ t in a..b, fderiv ℝ (fun x => F x t) x v := by
  rw [(hasFDerivAt_integral_of_contDiff hF a b x).fderiv,
    ContinuousLinearMap.intervalIntegral_apply (φ := fun t => fderiv ℝ (fun x => F x t) x)
      (((continuous_fderiv_fst_of_contDiff hF).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable a b)]

/-- Smoothness of parametric integrals with values in a space of the universe of `H` or above,
by induction on the order: the derivative of `x ↦ ∫_a^b F x t dt` is again a parametric integral
of a smooth integrand (`intervalIntegral.hasFDerivAt_integral_of_contDiff`). -/
theorem contDiff_parametric_intervalIntegral_of_contDiff_aux {E : Type max u v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) {F : H → ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ n fun x => ∫ t in a..b, F x t := by
  induction n generalizing E with
  | zero =>
    exact contDiff_zero.2 (continuous_parametric_intervalIntegral_of_continuous' hF.continuous a b)
  | succ n ih =>
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun x => ∫ t in a..b, fderiv ℝ (fun x => F x t) x,
      ?_, fun x => hasFDerivAt_integral_of_contDiff (hF.of_le (by simp)) a b x⟩
    have hpart : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry fun (q : H × ℝ) (x : H) => F x q.2) :=
      hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
    exact ih (F := fun x t => fderiv ℝ (fun x => F x t) x)
      (hpart.fderiv contDiff_fst (by simp))

/-- **Smoothness of parametric integrals**: if `(x, t) ↦ F x t` is smooth on `H × ℝ`, `H` finite
dimensional, then `x ↦ ∫_a^b F x t dt` is smooth. Mathlib has the derivative under the integral
sign (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`) and the continuity
(`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`); the induction on the
order runs in one universe
(`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff_aux`), reached through
`ULift`. -/
theorem contDiff_parametric_intervalIntegral_of_contDiff {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : H → ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => ∫ t in a..b, F x t := by
  let e : ULift.{u} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry fun x t => e.symm (F x t)) :=
    e.symm.contDiff.comp hF
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => ∫ t in a..b, e.symm (F x t) :=
    contDiff_infty.2 fun n => contDiff_parametric_intervalIntegral_of_contDiff_aux.{u, w} n hF' a b
  have heq : (fun x => ∫ t in a..b, F x t) = fun x => e (∫ t in a..b, e.symm (F x t)) := by
    funext x
    calc ∫ t in a..b, F x t = ∫ t in a..b, e (e.symm (F x t)) := by simp
      _ = e (∫ t in a..b, e.symm (F x t)) := by
          simp only [intervalIntegral, e.integral_comp_comm, map_sub]
  rw [heq]
  exact e.contDiff.comp h

end intervalIntegral

end ParametricIntegral

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Exponential dilations -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The dilations `m_{e^s}(x) = e^{sn} m(e^s x)` depend smoothly on `(x, s)` if `m` is smooth. -/
theorem contDiff_dilate_exp {m : V → ℂ} {n : WithTop ℕ∞} (hm : ContDiff ℝ n m) :
    ContDiff ℝ n (Function.uncurry fun (x : V) (s : ℝ) => dilate (Real.exp s) m x) := by
  have he : ContDiff ℝ n fun p : V × ℝ => Real.exp p.2 := Real.contDiff_exp.comp contDiff_snd
  exact (Complex.ofRealCLM.contDiff.comp (he.pow _)).mul (hm.comp (he.smul contDiff_fst))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The dilations `m_{e^s}(x)` depend continuously on `(x, s)` if `m` is continuous. -/
theorem continuous_dilate_exp {m : V → ℂ} (hm : Continuous m) :
    Continuous (Function.uncurry fun (x : V) (s : ℝ) => dilate (Real.exp s) m x) :=
  (contDiff_dilate_exp (n := 0) (contDiff_zero.2 hm)).continuous

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The derivative of a dilate: `D(m_c)(x) v = c^n Dm(c x)(c v)`. -/
theorem fderiv_dilate_apply {m : V → ℂ} (hm : Differentiable ℝ m) (c : ℝ) (x v : V) :
    fderiv ℝ (dilate c m) x v = (((c ^ finrank ℝ V : ℝ)) : ℂ) * fderiv ℝ m (c • x) (c • v) := by
  have h : HasFDerivAt (dilate c m) ((((c ^ finrank ℝ V : ℝ)) : ℂ) •
      (fderiv ℝ m (c • x)).comp (c • ContinuousLinearMap.id ℝ V)) x :=
    ((hm (c • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)).const_mul _
  rw [h.fderiv]
  simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The dilates of a differentiable function are differentiable. -/
theorem differentiableAt_dilate {G : V → ℂ} (hG : Differentiable ℝ G) (c : ℝ) (x : V) :
    DifferentiableAt ℝ (dilate c G) x :=
  (differentiableAt_const _).mul ((hG _).comp x (differentiableAt_id.const_smul c))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Euler's identity for dilations**: `d/ds m_{e^s}(x) = n m_{e^s}(x) + D(m_{e^s})(x) x`, the
derivative of the dilation parameter is the radial derivative. -/
theorem hasDerivAt_dilate_exp {m : V → ℂ} (hm : Differentiable ℝ m) (x : V) (s : ℝ) :
    HasDerivAt (fun s => dilate (Real.exp s) m x)
      ((finrank ℝ V : ℂ) * dilate (Real.exp s) m x +
        fderiv ℝ (dilate (Real.exp s) m) x x) s := by
  set n := finrank ℝ V
  have h1 : HasDerivAt (fun s => ((Real.exp (n * s) : ℝ) : ℂ)) ((Real.exp (n * s) * n : ℝ) : ℂ) s :=
    (((hasDerivAt_id s).const_mul (n : ℝ)).exp.congr_deriv (by simp)).ofReal_comp
  have h2 : HasDerivAt (fun s => m (Real.exp s • x)) (fderiv ℝ m (Real.exp s • x)
      (Real.exp s • x)) s :=
    (hm _).hasFDerivAt.comp_hasDerivAt s ((Real.hasDerivAt_exp s).smul_const x)
  have hd : (fun s => dilate (Real.exp s) m x) =
      fun s => ((Real.exp (n * s) : ℝ) : ℂ) * m (Real.exp s • x) := by
    funext s
    rw [dilate, Real.exp_nat_mul]
  rw [hd]
  convert h1.mul h2 using 1
  rw [fderiv_dilate_apply hm, dilate, ← Real.exp_nat_mul]
  push_cast
  ring

/-! ### The dilation average and the divergence kernels -/

/-- The **dilation average** `A_m(x) = ∫_0^{log 2} m_{e^s}(x) ds`, which is
`∫_1^2 t⁻¹ m_t(x) dt` after the substitution `t = e^s`. -/
noncomputable def dilationAverage (m : V → ℂ) (x : V) : ℂ :=
  ∫ s in (0 : ℝ)..Real.log 2, dilate (Real.exp s) m x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The dilation average after the substitution `t = e^s`**: for continuous `m`,
`A_m(x) = ∫_1^2 t⁻¹ m_t(x) dt` (Mathlib's `intervalIntegral.integral_deriv_smul_comp'`). -/
theorem dilationAverage_eq_integral_inv_mul {m : V → ℂ} (hm : Continuous m) (x : V) :
    dilationAverage m x = ∫ t in (1 : ℝ)..2, ((t⁻¹ : ℝ) : ℂ) * dilate t m x := by
  have hcont : Continuous fun t : ℝ => dilate t m x :=
    (Complex.continuous_ofReal.comp (continuous_pow _)).mul
      (hm.comp (continuous_id.smul continuous_const))
  have hg : ContinuousOn (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) * dilate t m x)
      (Real.exp '' uIcc 0 (Real.log 2)) := by
    refine (Complex.continuous_ofReal.comp_continuousOn (continuousOn_inv₀.mono ?_)).mul
      hcont.continuousOn
    rintro _ ⟨s, -, rfl⟩
    exact (Real.exp_pos s).ne'
  have h := intervalIntegral.integral_deriv_smul_comp' (fun s _ => Real.hasDerivAt_exp s)
    Real.continuous_exp.continuousOn hg
  rw [Real.exp_zero, Real.exp_log two_pos] at h
  rw [dilationAverage, ← h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [Function.comp_apply, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (Real.exp_pos s).ne', Complex.ofReal_one, one_mul]

/-- The **divergence kernel** `K_w(x) = ⟪w, x⟫ A_m(x)` in the direction `w`. For an orthonormal
basis `(b_i)`, `∑_i ∂_{b_i} K_{b_i} = m_2 - m` (`Rd.sum_fderiv_divergenceKernel`). -/
noncomputable def divergenceKernel (m : V → ℂ) (w : V) (x : V) : ℂ :=
  (inner ℝ w x : ℂ) * dilationAverage m x

omit [MeasurableSpace V] [BorelSpace V] in
/-- The dilation average of a smooth function is smooth
(`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff`). -/
theorem contDiff_dilationAverage {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilationAverage m) :=
  intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff (contDiff_dilate_exp hm) _ _

omit [MeasurableSpace V] [BorelSpace V] in
/-- The divergence kernels of a smooth function are smooth. -/
theorem contDiff_divergenceKernel {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    (w : V) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (divergenceKernel m w) :=
  (Complex.ofRealCLM.contDiff.comp (innerSL ℝ w).contDiff).mul (contDiff_dilationAverage hm)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The dilation average vanishes at `x` if `m(t x) = 0` for every `t ∈ [1, 2]`. -/
theorem dilationAverage_eq_zero {m : V → ℂ} {x : V}
    (hx : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → m (t • x) = 0) : dilationAverage m x = 0 := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => ?_).trans
    intervalIntegral.integral_zero
  rw [uIcc_of_le hlog] at hs
  have h1 : 1 ≤ Real.exp s := Real.one_le_exp hs.1
  have h2 : Real.exp s ≤ 2 := by
    calc Real.exp s ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hs.2
      _ = 2 := Real.exp_log two_pos
  simp [dilate, hx _ h1 h2]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The divergence kernels vanish at `x` if `m(t x) = 0` for every `t ∈ [1, 2]`. -/
theorem divergenceKernel_eq_zero {m : V → ℂ} (w : V) {x : V}
    (hx : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → m (t • x) = 0) : divergenceKernel m w x = 0 := by
  rw [divergenceKernel, dilationAverage_eq_zero hx, mul_zero]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The divergence kernels vanish outside the ball of radius `R` if `m` does. -/
theorem divergenceKernel_eq_zero_of_lt {m : V → ℂ} {R : ℝ} (hR : ∀ z, R < ‖z‖ → m z = 0)
    (w : V) {x : V} (hx : R < ‖x‖) : divergenceKernel m w x = 0 :=
  divergenceKernel_eq_zero w fun t ht _ => hR _ (by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
    nlinarith [norm_nonneg x])

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The divergence kernels have compact support if `m` vanishes outside a ball. -/
theorem hasCompactSupport_divergenceKernel [ProperSpace V] {m : V → ℂ} {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → m z = 0) (w : V) : HasCompactSupport (divergenceKernel m w) :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx =>
    divergenceKernel_eq_zero_of_lt hR w (by simpa [mem_closedBall, dist_zero_right] using hx)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Supports of dyadic dilates**: if `K` vanishes outside a closed set `S` with
`c y ∈ S ⇒ y ∈ S` for `c ≥ 1`, then every dilate `K_{2^j}` is supported in `S`. -/
theorem tsupport_dilate_two_pow_subset [NormedSpace ℝ V] {K : V → ℂ} {S : Set V}
    (hS : IsClosed S) (hK : ∀ y, K y ≠ 0 → y ∈ S)
    (hscale : ∀ c : ℝ, 1 ≤ c → ∀ y, c • y ∈ S → y ∈ S) (j : ℕ) :
    tsupport (dilate (2 ^ j) K) ⊆ S :=
  closure_minimal (fun y hy => hscale (2 ^ j) (one_le_pow₀ one_le_two) y
    (hK _ fun h => hy (by simp [dilate, h]))) hS

omit [MeasurableSpace V] [BorelSpace V] in
/-- The dilation average of a `C^1` function is differentiable
(`intervalIntegral.hasFDerivAt_integral_of_contDiff`). -/
theorem differentiable_dilationAverage {m : V → ℂ} (hm : ContDiff ℝ 1 m) :
    Differentiable ℝ (dilationAverage m) := fun x =>
  (intervalIntegral.hasFDerivAt_integral_of_contDiff (contDiff_dilate_exp hm) _ _
    x).differentiableAt

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivative of the dilation average of a `C^1` function:
`D A_m(x) v = ∫_0^{log 2} D(m_{e^s})(x) v ds`
(`intervalIntegral.fderiv_integral_apply_of_contDiff`). -/
theorem fderiv_dilationAverage_apply {m : V → ℂ} (hm : ContDiff ℝ 1 m) (x v : V) :
    fderiv ℝ (dilationAverage m) x v =
      ∫ s in (0 : ℝ)..Real.log 2, fderiv ℝ (dilate (Real.exp s) m) x v :=
  intervalIntegral.fderiv_integral_apply_of_contDiff (contDiff_dilate_exp hm) _ _ x v

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The radial derivative `s ↦ D(m_{e^s})(x) x` of the dilates of a `C^1` function is
continuous in `s`. -/
theorem continuous_fderiv_dilate_exp_apply {m : V → ℂ} (hm : ContDiff ℝ 1 m) (x : V) :
    Continuous fun s => fderiv ℝ (dilate (Real.exp s) m) x x := by
  have hd : Differentiable ℝ m := hm.differentiable one_ne_zero
  simp_rw [fderiv_dilate_apply hd]
  have hg : Continuous fun s : ℝ => Real.exp s • x := Real.continuous_exp.smul continuous_const
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.pow _)).mul
    (((hm.continuous_fderiv one_ne_zero).comp hg).clm_apply hg)

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The dilation identity**: `m_2(x) - m(x) = n A_m(x) + D A_m(x) x`, by the fundamental theorem
of calculus for `s ↦ m_{e^s}(x)` on `[0, log 2]` and Euler's identity
(`Rd.hasDerivAt_dilate_exp`). -/
theorem dilate_two_sub_eq {m : V → ℂ} (hm : ContDiff ℝ 1 m) (x : V) :
    dilate 2 m x - m x = (finrank ℝ V : ℂ) * dilationAverage m x +
      fderiv ℝ (dilationAverage m) x x := by
  have hd : Differentiable ℝ m := hm.differentiable one_ne_zero
  have hc1 : Continuous fun s => dilate (Real.exp s) m x :=
    (contDiff_dilate_exp hm).continuous.comp (continuous_const.prodMk continuous_id)
  have hc2 := continuous_fderiv_dilate_exp_apply hm x
  have hcf : Continuous fun s => (finrank ℝ V : ℂ) * dilate (Real.exp s) m x +
      fderiv ℝ (dilate (Real.exp s) m) x x := (continuous_const.mul hc1).add hc2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_dilate_exp hd x s) (hcf.intervalIntegrable 0 (Real.log 2))
  rw [intervalIntegral.integral_add (f := fun s => (finrank ℝ V : ℂ) * dilate (Real.exp s) m x)
    (g := fun s => fderiv ℝ (dilate (Real.exp s) m) x x)
    ((continuous_const.mul hc1).intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, Real.exp_log two_pos,
    Real.exp_zero] at hftc
  rw [dilationAverage, fderiv_dilationAverage_apply hm, hftc]
  simp [dilate]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The divergence of `x A(x)`**: for an orthonormal basis `(b_i)` of `V` and `A`
differentiable at `x`, `∑_i ∂_{b_i} (⟪b_i, ·⟫ A)(x) = n A(x) + DA(x) x`, since
`∑_i ⟪b_i, x⟫ b_i = x` (Mathlib's `OrthonormalBasis.sum_repr'`). -/
theorem sum_fderiv_inner_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) {A : V → ℂ}
    {x : V} (hA : DifferentiableAt ℝ A x) :
    ∑ i, fderiv ℝ (fun y => (inner ℝ (b i) y : ℂ) * A y) x (b i) =
      (finrank ℝ V : ℂ) * A x + fderiv ℝ A x x := by
  have hK : ∀ w v : V, fderiv ℝ (fun y => (inner ℝ w y : ℂ) * A y) x v =
      (inner ℝ w v : ℂ) * A x + (inner ℝ w x : ℂ) * fderiv ℝ A x v := fun w v => by
    have h := ((Complex.ofRealCLM.comp (innerSL ℝ w)).hasFDerivAt (x := x)).mul hA.hasFDerivAt
    rw [show (fun y => (inner ℝ w y : ℂ) * A y) = ⇑(Complex.ofRealCLM.comp (innerSL ℝ w)) * A from
      funext fun y => by simp, h.fderiv]
    simp [add_comm, mul_comm]
  have hb : ∀ i, inner ℝ (b i) (b i) = (1 : ℝ) := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
  have hsum : fderiv ℝ A x x = ∑ i, (inner ℝ (b i) x : ℂ) * fderiv ℝ A x (b i) := by
    rw [← congrArg (fun v => fderiv ℝ A x v) (b.sum_repr' x)]
    simp [map_sum, Complex.real_smul]
  simp_rw [hK, hb, Complex.ofReal_one, one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hsum,
    ← Module.finrank_eq_card_basis b.toBasis, nsmul_eq_mul]

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The divergence identity**: for an orthonormal basis `(b_i)` of `V` and `m ∈ C^1`,
`∑_i ∂_{b_i} K_{b_i}(x) = m_2(x) - m(x)` with the divergence kernels
`K_{b_i}(x) = ⟪b_i, x⟫ A_m(x)`: the left side is `n A_m(x) + D A_m(x) x`
(`Rd.sum_fderiv_inner_mul`), and `Rd.dilate_two_sub_eq`. -/
theorem sum_fderiv_divergenceKernel {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {m : V → ℂ} (hm : ContDiff ℝ 1 m) (x : V) :
    ∑ i, fderiv ℝ (divergenceKernel m (b i)) x (b i) = dilate 2 m x - m x :=
  (sum_fderiv_inner_mul b (differentiable_dilationAverage hm x)).trans (dilate_two_sub_eq hm x).symm

/-- The integrand `(x, s) ↦ ⟪w, x⟫ m_{e^s}(x)` of the dilation average is integrable on
`V × (0, c]` if `m` is continuous and vanishes outside a ball: it is continuous and vanishes
outside the compact set `closedBall(0, R) × [0, c]`. -/
theorem integrable_inner_mul_dilate_exp {m : V → ℂ} (hm : Continuous m) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → m z = 0) (w : V) (c : ℝ) :
    Integrable (Function.uncurry fun (x : V) (s : ℝ) => (inner ℝ w x : ℂ) * dilate (Real.exp s) m x)
      ((volume : Measure V).prod (volume.restrict (Ioc 0 c))) := by
  have hcont : Continuous (Function.uncurry fun (x : V) (s : ℝ) =>
      (inner ℝ w x : ℂ) * dilate (Real.exp s) m x) :=
    (Complex.continuous_ofReal.comp (continuous_const.inner continuous_fst)).mul
      (continuous_dilate_exp hm)
  have hμ : (volume : Measure V).prod (volume.restrict (Ioc 0 c)) =
      ((volume : Measure V).prod volume).restrict (univ ×ˢ Ioc 0 c) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hμ]
  refine IntegrableOn.mono_set ?_ (prod_mono subset_rfl Ioc_subset_Icc_self)
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := closedBall 0 R ×ˢ Icc 0 c)
    (hcont.continuousOn.integrableOn_compact ((isCompact_closedBall 0 R).prod isCompact_Icc))
    (MeasurableSet.univ.prod measurableSet_Icc) ?_
  rintro ⟨x, s⟩ ⟨⟨-, hs⟩, hns⟩
  have hx : R < ‖x‖ := by
    by_contra h
    exact hns ⟨by simpa [mem_closedBall, dist_zero_right] using h, hs⟩
  have h1 : R < ‖Real.exp s • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos s).le]
    nlinarith [Real.one_le_exp hs.1, norm_nonneg x]
  simp [dilate, hR _ h1]

/-- **The divergence kernels have mean zero** if the first moments of `m` vanish:
`∫ K_w = ∫_0^{log 2} ∫ ⟪w, x⟫ m_{e^s}(x) dx ds = ∫_0^{log 2} e^{-s} ∫ ⟪w, x⟫ m(x) dx ds = 0`
(Fubini, Mathlib's `integral_integral_swap`, and `Rd.integral_inner_mul_dilate`). -/
theorem integral_divergenceKernel {m : V → ℂ} (hm : Continuous m) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → m z = 0) (w : V) (h1 : ∫ x, (inner ℝ w x : ℂ) * m x = 0) :
    ∫ x, divergenceKernel m w x = 0 := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have h : ∀ x, divergenceKernel m w x =
      ∫ s in Ioc 0 (Real.log 2), (inner ℝ w x : ℂ) * dilate (Real.exp s) m x := fun x => by
    rw [divergenceKernel, dilationAverage, intervalIntegral.integral_of_le hlog,
      integral_const_mul]
  simp_rw [h]
  rw [integral_integral_swap (integrable_inner_mul_dilate_exp hm hR w _)]
  refine integral_eq_zero_of_ae (ae_of_all _ fun s => ?_)
  change (∫ x, (inner ℝ w x : ℂ) * dilate (Real.exp s) m x) = 0
  rw [integral_inner_mul_dilate m w (Real.exp_pos s), h1, mul_zero]

/-! ### The divergence kernels as Schwartz functions -/

/-- The divergence kernel `K_w` of a smooth `m` that vanishes outside a ball, as a Schwartz
function (it is smooth with compact support). -/
noncomputable def divergenceSchwartz {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    {R : ℝ} (hR : ∀ z, R < ‖z‖ → m z = 0) (w : V) : 𝓢(V, ℂ) :=
  (hasCompactSupport_divergenceKernel hR w).toSchwartzMap (contDiff_divergenceKernel hm w)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The values of the Schwartz divergence kernel are those of `Rd.divergenceKernel`. -/
theorem coe_divergenceSchwartz {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    {R : ℝ} (hR : ∀ z, R < ‖z‖ → m z = 0) (w : V) :
    (divergenceSchwartz hm hR w : V → ℂ) = divergenceKernel m w :=
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The divergence identity for Schwartz kernels**: `∑_i ∂_{b_i} K_{b_i} = m_2 - m` pointwise
(`Rd.sum_fderiv_divergenceKernel`). -/
theorem sum_lineDerivOp_divergenceSchwartz {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → m z = 0) (x : V) :
    ∑ i, (∂_{b i} (divergenceSchwartz hm hR (b i)) : 𝓢(V, ℂ)) x = dilate 2 m x - m x := by
  simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, coe_divergenceSchwartz]
  exact sum_fderiv_divergenceKernel b (hm.of_le (by simp)) x

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The divergence identity at every scale**: for `c ≠ 0`,
`∑_i ∂_{b_i} (K_{b_i})_c = c (m_2 - m)_c`, by the chain rule for dilations
(`Rd.lineDerivOp_schwartzDilate`). -/
theorem sum_lineDerivOp_schwartzDilate_divergenceSchwartz {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    {R : ℝ} (hR : ∀ z, R < ‖z‖ → m z = 0) {c : ℝ} (hc : c ≠ 0) (x : V) :
    ∑ i, (∂_{b i} (schwartzDilate c hc (divergenceSchwartz hm hR (b i))) : 𝓢(V, ℂ)) x =
      (c : ℂ) * dilate c (fun y => dilate 2 m y - m y) x := by
  simp_rw [lineDerivOp_schwartzDilate, smul_apply, coe_schwartzDilate, smul_eq_mul,
    ← Finset.mul_sum]
  congr 1
  simp only [dilate, ← Finset.mul_sum]
  congr 1
  exact sum_lineDerivOp_divergenceSchwartz b hm hR (c • x)

/-! ### Fourier transforms of mean-zero kernels -/

/-- **Fourier transforms of mean-zero kernels vanish at `0` to first order**: for a Schwartz
function `G` with `∫ G = 0`, `|𝓕G(ξ)| ≤ 2π ‖ξ‖ ∫ ‖x‖ |G(x)| dx`, since
`𝓕G(ξ) = ∫ (e^(-2πi⟪x, ξ⟫) - 1) G(x) dx` and the character is `2π`-Lipschitz
(`Rd.norm_fourierChar_sub_le`). -/
theorem norm_fourier_le_of_integral_eq_zero (G : 𝓢(V, ℂ)) (h0 : ∫ x, G x = 0) (ξ : V) :
    ‖𝓕 (G : V → ℂ) ξ‖ ≤ 2 * π * ‖ξ‖ * ∫ x, ‖x‖ * ‖G x‖ := by
  have hi : Integrable fun x => 𝐞 (-inner ℝ x ξ) • G x := by
    simpa using (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (show Continuous fun p : V × V => (innerₗ V) p.1 p.2 from continuous_inner)
      (μ := volume) ξ).2 G.integrable
  have h : 𝓕 (G : V → ℂ) ξ = ∫ x, (𝐞 (-inner ℝ x ξ) • G x - G x) := by
    rw [integral_sub hi G.integrable, h0, sub_zero, Real.fourier_eq]
  have hb : Integrable fun x => 2 * π * ‖ξ‖ * (‖x‖ * ‖G x‖) := by
    simpa using (G.integrable_pow_mul volume 1).const_mul (2 * π * ‖ξ‖)
  rw [h, ← integral_const_mul]
  refine norm_integral_le_of_norm_le hb (ae_of_all _ fun x => ?_)
  have h1 : 𝐞 (-inner ℝ x ξ) • G x - G x = ((𝐞 (-inner ℝ x ξ) : ℂ) - 𝐞 0) * G x := by
    rw [AddChar.map_zero_eq_one, Circle.smul_def, Circle.coe_one, sub_mul, one_mul, smul_eq_mul]
  rw [h1, norm_mul]
  calc ‖(𝐞 (-inner ℝ x ξ) : ℂ) - 𝐞 0‖ * ‖G x‖ ≤ 2 * π * |-inner ℝ x ξ - 0| * ‖G x‖ := by
        gcongr
        exact norm_fourierChar_sub_le _ _
    _ ≤ 2 * π * (‖x‖ * ‖ξ‖) * ‖G x‖ := by
        gcongr
        rw [sub_zero, abs_neg]
        exact abs_real_inner_le_norm x ξ
    _ = 2 * π * ‖ξ‖ * (‖x‖ * ‖G x‖) := by ring

/-- **Fourier transforms of Schwartz functions decay like `1/‖ξ‖`**:
`2π ‖ξ‖ |𝓕G(ξ)| ≤ C_G` with the gradient mass `C_G = Rd.gradMassConst G`, since
`𝓕(∂_ξ G)(ξ) = 2πi ‖ξ‖² 𝓕G(ξ)` (Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`) and
`∫ |∂_ξ G| ≤ ‖ξ‖ C_G` (`Rd.lintegral_enorm_lineDerivOp_le`). -/
theorem ofReal_mul_enorm_mul_enorm_fourier_le (G : 𝓢(V, ℂ)) (ξ : V) :
    ENNReal.ofReal (2 * π) * ‖ξ‖ₑ * ‖𝓕 (G : V → ℂ) ξ‖ₑ ≤ gradMassConst G := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have hF : 𝓕 ((∂_{ξ} G : 𝓢(V, ℂ)) : V → ℂ) ξ =
      (2 * π * Complex.I * (inner ℝ ξ ξ : ℂ)) * 𝓕 (G : V → ℂ) ξ := by
    have ht : (fun x : V => inner ℝ x ξ).HasTemperateGrowth := by fun_prop
    rw [← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, SchwartzMap.fourier_coe]
    simp [mul_assoc]
  have hnorm : ‖𝓕 ((∂_{ξ} G : 𝓢(V, ℂ)) : V → ℂ) ξ‖ₑ =
      ‖ξ‖ₑ * (ENNReal.ofReal (2 * π) * ‖ξ‖ₑ * ‖𝓕 (G : V → ℂ) ξ‖ₑ) := by
    rw [hF, eNorm_mul, real_inner_self_eq_norm_sq]
    have h2 : ‖2 * π * Complex.I * ((‖ξ‖ ^ 2 : ℝ) : ℂ)‖ₑ =
        ENNReal.ofReal (2 * π) * ‖ξ‖ₑ ^ 2 := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [h2]
    ring
  have hle : ‖𝓕 ((∂_{ξ} G : 𝓢(V, ℂ)) : V → ℂ) ξ‖ₑ ≤ ‖ξ‖ₑ * gradMassConst G :=
    (enorm_fourier_le_lintegral _ ξ).trans (lintegral_enorm_lineDerivOp_le ξ G)
  rw [hnorm] at hle
  exact (ENNReal.mul_le_mul_iff_right (eNorm_ne_zero.2 hξ) eNorm_ne_top).1 hle

/-- The constant `4 (2π ∫ ‖x‖ |G(x)| dx + C_G / (2π))²` of the Fourier overlap of the dilates of a
mean-zero Schwartz function `G`, with the gradient mass `C_G = Rd.gradMassConst G`. -/
noncomputable def meanZeroOverlap (G : 𝓢(V, ℂ)) : ℝ≥0∞ :=
  4 * (ENNReal.ofReal (2 * π * ∫ x, ‖x‖ * ‖G x‖) +
    gradMassConst G * (ENNReal.ofReal (2 * π))⁻¹) ^ 2

/-- The overlap constant of a mean-zero Schwartz function is finite. -/
theorem meanZeroOverlap_ne_top (G : 𝓢(V, ℂ)) : meanZeroOverlap G ≠ ∞ :=
  ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (gradMassConst_ne_top G)
      (ENNReal.inv_ne_top.2 (by simp [Real.pi_pos]))⟩))

/-- **The two Fourier bounds of a mean-zero kernel together**:
`|𝓕G(η)| ≤ C min(‖η‖, ‖η‖⁻¹)` with `C = 2π ∫ ‖x‖ |G(x)| dx + C_G / (2π)`
(`Rd.norm_fourier_le_of_integral_eq_zero`, `Rd.ofReal_mul_enorm_mul_enorm_fourier_le`). -/
theorem enorm_fourier_le_mul_min (G : 𝓢(V, ℂ)) (h0 : ∫ x, G x = 0) (η : V) :
    ‖𝓕 (G : V → ℂ) η‖ₑ ≤ (ENNReal.ofReal (2 * π * ∫ x, ‖x‖ * ‖G x‖) +
      gradMassConst G * (ENNReal.ofReal (2 * π))⁻¹) * min ‖η‖ₑ ‖η‖ₑ⁻¹ := by
  set A := ENNReal.ofReal (2 * π * ∫ x, ‖x‖ * ‖G x‖)
  set B := gradMassConst G * (ENNReal.ofReal (2 * π))⁻¹
  have hA : ‖𝓕 (G : V → ℂ) η‖ₑ ≤ (A + B) * ‖η‖ₑ := by
    refine le_trans ?_ (mul_le_mul_left (le_self_add : A ≤ A + B) _)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((norm_fourier_le_of_integral_eq_zero G h0 η).trans_eq ?_)
    ring
  rcases eq_or_ne η 0 with rfl | hη
  · rw [eNorm_zero, mul_zero] at hA
    exact hA.trans zero_le
  have hc0 : ENNReal.ofReal (2 * π) * ‖η‖ₑ ≠ 0 :=
    mul_ne_zero (by simp [Real.pi_pos]) (eNorm_ne_zero.2 hη)
  have hct : ENNReal.ofReal (2 * π) * ‖η‖ₑ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top eNorm_ne_top
  have hB : ‖𝓕 (G : V → ℂ) η‖ₑ ≤ (A + B) * ‖η‖ₑ⁻¹ :=
    calc ‖𝓕 (G : V → ℂ) η‖ₑ
        = (ENNReal.ofReal (2 * π) * ‖η‖ₑ)⁻¹ *
          (ENNReal.ofReal (2 * π) * ‖η‖ₑ * ‖𝓕 (G : V → ℂ) η‖ₑ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
      _ ≤ (ENNReal.ofReal (2 * π) * ‖η‖ₑ)⁻¹ * gradMassConst G := by
          gcongr
          exact ofReal_mul_enorm_mul_enorm_fourier_le G η
      _ = B * ‖η‖ₑ⁻¹ := by
          rw [ENNReal.mul_inv (Or.inr eNorm_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
          ring
      _ ≤ (A + B) * ‖η‖ₑ⁻¹ := by gcongr; exact le_add_self
  rw [mul_min]
  exact le_min hA hB

/-- **The Fourier overlap of the dilates of a mean-zero kernel**: for a Schwartz function `G`
with `∫ G = 0` and every `ξ`, `∑_j |𝓕(G_{2^j})(ξ)|² ≤ 4 C²` (`Rd.meanZeroOverlap G`), since
`𝓕(G_{2^j})(ξ) = 𝓕G(2^(-j) ξ)` and `∑_j min(2^(-j) ‖ξ‖, 2^j ‖ξ‖⁻¹) ≤ 4`
(`ENNReal.tsum_min_two_pow_le`). -/
theorem tsum_enorm_fourier_dilate_sq_le (G : 𝓢(V, ℂ)) (h0 : ∫ x, G x = 0) (ξ : V) :
    ∑' j : ℕ, ‖𝓕 (dilate (2 ^ j) (G : V → ℂ)) ξ‖ₑ ^ 2 ≤ meanZeroOverlap G := by
  set C := ENNReal.ofReal (2 * π * ∫ x, ‖x‖ * ‖G x‖) +
    gradMassConst G * (ENNReal.ofReal (2 * π))⁻¹
  have hdil : ∀ j : ℕ, 𝓕 (dilate (2 ^ j) (G : V → ℂ)) ξ = 𝓕 (G : V → ℂ) (((2 : ℝ) ^ j)⁻¹ • ξ) :=
    fun j => fourier_dilate _ (by positivity) ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h : ∀ j : ℕ, ‖𝓕 (dilate (2 ^ j) (G : V → ℂ)) 0‖ₑ ^ 2 = 0 := fun j => by
      have h1 := enorm_fourier_le_mul_min G h0 0
      rw [eNorm_zero, min_eq_left zero_le, mul_zero, nonpos_iff_eq_zero] at h1
      rw [hdil, smul_zero, h1, zero_pow two_ne_zero]
    simp [h]
  set a := ‖ξ‖ₑ⁻¹
  have hn : ∀ j : ℕ, ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ₑ = (2 ^ j * a)⁻¹ := fun j => by
    rw [eNorm_smul, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), inv_inv]
    congr 1
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity), ENNReal.ofReal_inv_of_pos
      (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  have hterm : ∀ j : ℕ, ‖𝓕 (dilate (2 ^ j) (G : V → ℂ)) ξ‖ₑ ^ 2 ≤
      C ^ 2 * min (2 ^ j * a) (2 ^ j * a)⁻¹ := fun j => by
    rw [hdil]
    calc ‖𝓕 (G : V → ℂ) (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2
        ≤ (C * min (2 ^ j * a)⁻¹ (2 ^ j * a)⁻¹⁻¹) ^ 2 := by
          gcongr
          rw [← hn]
          exact enorm_fourier_le_mul_min G h0 _
      _ = C ^ 2 * min (2 ^ j * a)⁻¹ (2 ^ j * a)⁻¹⁻¹ ^ 2 := by ring
      _ ≤ C ^ 2 * min (2 ^ j * a)⁻¹ (2 ^ j * a)⁻¹⁻¹ := by
          gcongr
          exact ENNReal.min_inv_sq_le _
      _ = C ^ 2 * min (2 ^ j * a) (2 ^ j * a)⁻¹ := by rw [inv_inv, min_comm]
  calc ∑' j : ℕ, ‖𝓕 (dilate (2 ^ j) (G : V → ℂ)) ξ‖ₑ ^ 2
      ≤ ∑' j : ℕ, C ^ 2 * min (2 ^ j * a) (2 ^ j * a)⁻¹ := tsum_le_tsum hterm
    _ = C ^ 2 * ∑' j : ℕ, min (2 ^ j * a) (2 ^ j * a)⁻¹ := ENNReal.tsum_mul_left
    _ ≤ C ^ 2 * 4 := by gcongr; exact ENNReal.tsum_min_two_pow_le a
    _ = meanZeroOverlap G := by rw [meanZeroOverlap]; ring

/-- **Dilates of a mean-zero Schwartz function form a Calderón–Zygmund family**: for
`G ∈ 𝓢(V, ℂ)` with `∫ G = 0`, the kernels `G_{2^j}` have the Fourier overlap
`Rd.meanZeroOverlap G` and the Hörmander constant `4 H_G` (`Rd.IsCZFamily.of_dilation` with the
constant family `Rd.IsUniformSchwartz.const`). -/
theorem isCZFamily_dilate_of_integral_eq_zero (G : 𝓢(V, ℂ)) (h0 : ∫ x, G x = 0) :
    IsCZFamily (fun j => dilate (2 ^ j) (G : V → ℂ)) (meanZeroOverlap G)
      (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l G) :=
  IsCZFamily.of_dilation (G := fun _ => G) (IsUniformSchwartz.const G)
    (tsum_enorm_fourier_dilate_sq_le G h0)

/-- **The divergence kernels form Calderón–Zygmund families**: if `m` is smooth, vanishes outside
a ball and has vanishing first moment in the direction `w`, the dilates `(K_w)_{2^j}` of the
divergence kernel form a Calderón–Zygmund family (`Rd.integral_divergenceKernel`,
`Rd.isCZFamily_dilate_of_integral_eq_zero`). -/
theorem isCZFamily_divergenceSchwartz {m : V → ℂ} (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    {R : ℝ} (hR : ∀ z, R < ‖z‖ → m z = 0) {w : V} (h1 : ∫ x, (inner ℝ w x : ℂ) * m x = 0) :
    IsCZFamily (fun j => dilate (2 ^ j) (divergenceSchwartz hm hR w : V → ℂ))
      (meanZeroOverlap (divergenceSchwartz hm hR w))
      (4 * familyHormanderConst V fun k l =>
        SchwartzMap.seminorm ℝ k l (divergenceSchwartz hm hR w)) :=
  isCZFamily_dilate_of_integral_eq_zero _ (integral_divergenceKernel hm.continuous hR w h1)

/-! ### The local means kernels as dilation differences -/

/-- **The local means kernels at dyadic scales**: for a bump with moment kernel `m` of order `L`,
`k_{j+1} = (m_2 - m)_{2^j}`, since `k_{j+1} = m_{2^(j+1)} - m_{2^j}` and
`(m_2)_{2^j} = m_{2^(j+1)}` (`Rd.dilate_sub`, `Rd.dilate_dilate`). -/
theorem LocalMeansBump.kernel_succ_eq_dilate (b : LocalMeansBump V) (L j : ℕ) :
    b.kernel L (j + 1) =
      dilate (2 ^ j) (fun y => dilate 2 (momentKernel b.toFun L) y - momentKernel b.toFun L y) := by
  rw [show (fun y => dilate 2 (momentKernel b.toFun L) y - momentKernel b.toFun L y) =
    dilate 2 (momentKernel b.toFun L) - momentKernel b.toFun L from rfl, dilate_sub,
    dilate_dilate, ← pow_succ]
  rfl

end Rd

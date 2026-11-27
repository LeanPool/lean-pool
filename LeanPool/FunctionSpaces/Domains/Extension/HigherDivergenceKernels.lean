/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.DivergenceKernels
public import LeanPool.FunctionSpaces.Domains.Lipschitz.LipschitzGraph

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Higher divergence kernels

Let `V` be a finite-dimensional real inner product space of dimension `n` with Lebesgue measure,
the orthonormal basis `(e_i)` of `Rd.gridBasis` and the dilations `G_c(x) = c^n G(c x)`
(`Rd.dilate`). A word `i = (i_0, …, i_{m-1})` stands for the derivative
`∂^{e_i} = ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}}` and the monomial `x^i = ∏_l ⟪e_{i_l}, x⟫`.

* **Weighted dilation averages** (`Rd.weightedDilation`): `A_w G(x) = ∫_a^b w(s) G_{e^s}(x) ds`.
  They are smooth for smooth `w` and `G` (`Rd.contDiff_weightedDilation`), vanish outside the ball
  of radius `R e^{-a}` if `G` vanishes outside the ball of radius `R`, satisfy
  `∫ A_w G = (∫_a^b w) ∫ G` (`Rd.integral_weightedDilation`), and are supported in `-K` if `G` is
  (`Rd.LipschitzGraph.coneSupported_weightedDilation`).
* **One step** (`Rd.weightedDilation_eq_sum_fderiv`): if `∫_a^b w = 0`, then
  `A_w G = ∑_i ∂_{e_i} A_W(⟪e_i, ·⟫ G)` with the anti-weight `W(s) = -e^{-s} ∫_a^s w`
  (`Rd.antiWeight`), by Euler's identity `d/ds G_{e^s} = div(x G_{e^s})` and integration by parts
  in `s`. The anti-weight shifts the moments:
  `∫_a^b W(s) e^{-rs} ds = -(r + 1)⁻¹ ∫_a^b w(s) e^{-(r+1)s} ds`
  (`Rd.integral_antiWeight_mul_exp`).
* **Iteration** (`Rd.weightedDilation_eq_sum_iteratedLineDeriv`): if the moments
  `∫_a^b w(s) e^{-rs} ds` vanish for `r < m`, then `A_w G = ∑_i ∂^{e_i} K_i` over the words of
  length `m`, with the higher divergence kernels `K_i = A_{w_m}(x^i G)` (`Rd.higherDivKernel`,
  `Rd.higherDivSchwartz`) and the iterated anti-weights `w_m` (`Rd.iterWeight`). The `K_i` have
  mean zero if also the moment of order `m` vanishes (`Rd.integral_higherDivKernel_eq_zero`).
* **The smoothed bump** (`Rd.LocalMeansBump.dilationSmoothed`): for a bump `b`,
  `b' = ∫_0^{log 2} ρ(s) b_{e^s} ds` with a smooth weight `ρ` (`Rd.dilationWeight`) is a bump of the
  same radius. Its moment kernel of order `L` is `A_u b` with the smooth weight
  `u(s) = ∑_{l<L} a_l ρ(s + log(l + 1))` (`Rd.momentWeight`,
  `Rd.LocalMeansBump.momentKernel_dilationSmoothed`), and its local means kernels are
  `k_{j+1} = (A_v b)_{2^j}` with `v(s) = u(s - log 2) - u(s)` (`Rd.kernelWeight`,
  `Rd.LocalMeansBump.kernel_succ_dilationSmoothed`). The moments of `v` of the orders `r < L`
  vanish (`Rd.integral_kernelWeight_mul_exp`), since `∑_{l<L} a_l (l + 1)^r = 0` for
  `1 ≤ r < L` (`Rd.sum_jacksonCoeff_mul_pow`).
* **The bump statement**: for `m ≤ L`, `k_{j+1} = 2^{-jm} ∑_i ∂^{e_i} (K_i)_{2^j}` with the higher
  divergence kernels of the bump (`Rd.LocalMeansBump.higherKernel`,
  `Rd.LocalMeansBump.kernel_succ_eq_sum_higherKernel`). For `m < L` their dyadic dilates form
  Calderón–Zygmund families (`Rd.LocalMeansBump.isCZFamily_higherKernel`); they have compact
  support (`Rd.LocalMeansBump.hasCompactSupport_higherKernel`), for `L ≥ 1` in `closedBall(0, L
  R)`, and
  in the reflected closed cone for bumps supported in `-K`
  (`Rd.LipschitzGraph.tsupport_dilate_higherKernel_subset`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal SchwartzMap LineDeriv Real

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Weighted dilation averages -/

/-- The **weighted dilation average** `∫_a^b w(s) G_{e^s}(x) ds` of `G` with the weight `w`, an
average of the dilates `G_t`, `e^a ≤ t ≤ e^b`; for `w = 1` on `[0, log 2]` this is the dilation
average `Rd.dilationAverage`. -/
noncomputable def weightedDilation (a b : ℝ) (w : ℝ → ℂ) (G : V → ℂ) (x : V) : ℂ :=
  ∫ s in a..b, w s * dilate (Real.exp s) G x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The integrand `(x, s) ↦ w(s) G_{e^s}(x)` of a weighted dilation average is as smooth as `w`
and `G` (`Rd.contDiff_dilate_exp`). -/
theorem contDiff_weight_mul_dilate_exp {w : ℝ → ℂ} {G : V → ℂ} {n : WithTop ℕ∞}
    (hw : ContDiff ℝ n w) (hG : ContDiff ℝ n G) :
    ContDiff ℝ n (Function.uncurry fun (x : V) (s : ℝ) => w s * dilate (Real.exp s) G x) :=
  (hw.comp contDiff_snd).mul (contDiff_dilate_exp hG)

omit [MeasurableSpace V] [BorelSpace V] in
/-- Weighted dilation averages of smooth functions with smooth weights are smooth
(`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff`). -/
theorem contDiff_weightedDilation (a b : ℝ) {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weightedDilation a b w G) :=
  intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff
    (contDiff_weight_mul_dilate_exp hw hG) a b

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A weighted dilation average vanishes at `x` if `G(e^s x) = 0` for every `s` between `a` and
`b`. -/
theorem weightedDilation_eq_zero (a b : ℝ) (w : ℝ → ℂ) {G : V → ℂ} {x : V}
    (hx : ∀ s ∈ uIcc a b, G (Real.exp s • x) = 0) : weightedDilation a b w G x = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => ?_).trans
    intervalIntegral.integral_zero
  simp [dilate, hx s hs]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If `R e^{-a} < ‖x‖` and `a ≤ s`, then `R < ‖e^s x‖`. -/
theorem lt_norm_exp_smul {R a s : ℝ} {x : V} (has : a ≤ s) (hx : R * Real.exp (-a) < ‖x‖) :
    R < ‖Real.exp s • x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos s).le]
  have h1 : R < ‖x‖ * Real.exp a := by
    rw [← div_lt_iff₀ (Real.exp_pos a), div_eq_mul_inv, ← Real.exp_neg]
    exact hx
  have h2 : Real.exp a ≤ Real.exp s := Real.exp_le_exp.2 has
  nlinarith [norm_nonneg x]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A weighted dilation average over `[a, b]` of a function that vanishes outside the ball of
radius `R` vanishes outside the ball of radius `R e^{-a}`. -/
theorem weightedDilation_eq_zero_of_lt {a b : ℝ} (hab : a ≤ b) (w : ℝ → ℂ) {G : V → ℂ} {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → G z = 0) {x : V} (hx : R * Real.exp (-a) < ‖x‖) :
    weightedDilation a b w G x = 0 :=
  weightedDilation_eq_zero a b w fun s hs => hR _ (lt_norm_exp_smul
    (by rw [uIcc_of_le hab] at hs; exact hs.1) hx)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A weighted dilation average of a function that vanishes outside a ball has compact
support. -/
theorem hasCompactSupport_weightedDilation [ProperSpace V] {a b : ℝ} (hab : a ≤ b) (w : ℝ → ℂ)
    {G : V → ℂ} {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) :
    HasCompactSupport (weightedDilation a b w G) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (R * Real.exp (-a))) fun x hx =>
    weightedDilation_eq_zero_of_lt hab w hR (by simpa [mem_closedBall, dist_zero_right] using hx)

/-- The integrand `(x, s) ↦ w(s) G_{e^s}(x)` is integrable on `V × (a, b]` if `w` and `G` are
continuous and `G` vanishes outside a ball: it is continuous and vanishes outside the compact set
`closedBall(0, R e^{-a}) × [a, b]`. -/
theorem integrable_weight_mul_dilate_exp {a b : ℝ} {w : ℝ → ℂ} (hw : Continuous w) {G : V → ℂ}
    (hG : Continuous G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) :
    Integrable (Function.uncurry fun (x : V) (s : ℝ) => w s * dilate (Real.exp s) G x)
      ((volume : Measure V).prod (volume.restrict (Ioc a b))) := by
  have hcont : Continuous (Function.uncurry fun (x : V) (s : ℝ) =>
      w s * dilate (Real.exp s) G x) := (hw.comp continuous_snd).mul (continuous_dilate_exp hG)
  have hμ : (volume : Measure V).prod (volume.restrict (Ioc a b)) =
      ((volume : Measure V).prod volume).restrict (univ ×ˢ Ioc a b) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hμ]
  refine IntegrableOn.mono_set ?_ (prod_mono subset_rfl Ioc_subset_Icc_self)
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := closedBall 0 (R * Real.exp (-a)) ×ˢ Icc a b)
    (hcont.continuousOn.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc))
    (MeasurableSet.univ.prod measurableSet_Icc) ?_
  rintro ⟨x, s⟩ ⟨⟨-, hs⟩, hns⟩
  have hx : R * Real.exp (-a) < ‖x‖ := by
    by_contra h
    exact hns ⟨by simpa [mem_closedBall, dist_zero_right] using h, hs⟩
  simp [dilate, hR _ (lt_norm_exp_smul hs.1 hx)]

/-- **The integral of a weighted dilation average**: `∫ A = (∫_a^b w) ∫ G` for `a ≤ b`, continuous
`w` and continuous `G` vanishing outside a ball, by Fubini (Mathlib's `integral_integral_swap`)
and `∫ G_t = ∫ G` (`Rd.integral_dilate`). -/
theorem integral_weightedDilation {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ} (hw : Continuous w)
    {G : V → ℂ} (hG : Continuous G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) :
    ∫ x, weightedDilation a b w G x = (∫ s in a..b, w s) * ∫ x, G x := by
  have h : ∀ x, weightedDilation a b w G x =
      ∫ s in Ioc a b, w s * dilate (Real.exp s) G x := fun x => by
    rw [weightedDilation, intervalIntegral.integral_of_le hab]
  simp_rw [h]
  rw [integral_integral_swap (integrable_weight_mul_dilate_exp hw hG hR),
    intervalIntegral.integral_of_le hab, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  change (∫ x, w s * dilate (Real.exp s) G x) = w s * ∫ x, G x
  rw [integral_const_mul, integral_dilate G (Real.exp_pos s)]

/-! ### One step: a weighted dilation average as a divergence -/

/-- The **primitive** `s ↦ ∫_a^s w` of a smooth function is smooth: its derivative is `w`
(Mathlib's `Continuous.integral_hasStrictDerivAt` and `contDiff_infty_iff_deriv`). -/
theorem contDiff_primitive {w : ℝ → ℂ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (a : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s => ∫ σ in a..s, w σ := by
  have hd : ∀ s, HasDerivAt (fun s => ∫ σ in a..s, w σ) (w s) s := fun s =>
    (hw.continuous.integral_hasStrictDerivAt a s).hasDerivAt
  refine contDiff_infty_iff_deriv.2 ⟨fun s => (hd s).differentiableAt, ?_⟩
  rw [show deriv (fun s => ∫ σ in a..s, w σ) = w from funext fun s => (hd s).deriv]
  exact hw

/-- The **anti-weight** `W(s) = -e^{-s} ∫_a^s w` of a weight `w`: if `∫_a^b w = 0`, the weighted
dilation average with the weight `w` is the divergence of those with the weight `W`
(`Rd.weightedDilation_eq_sum_fderiv`). -/
noncomputable def antiWeight (a : ℝ) (w : ℝ → ℂ) (s : ℝ) : ℂ :=
  -((Real.exp (-s) : ℝ) : ℂ) * ∫ σ in a..s, w σ

/-- The anti-weight of a smooth weight is smooth. -/
theorem contDiff_antiWeight (a : ℝ) {w : ℝ → ℂ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (antiWeight a w) :=
  ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)).neg).mul
    (contDiff_primitive hw a)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The anti-weight carries a coordinate factor**: with `W = Rd.antiWeight a w`,
`∫_a^b W(s) (⟪e, ·⟫ G)_{e^s}(x) ds = ⟪e, x⟫ ∫_a^b (-∫_a^s w) G_{e^s}(x) ds`, since
`(⟪e, ·⟫ G)_c(x) = c ⟪e, x⟫ G_c(x)` (`Rd.inner_mul_dilate_eq`). -/
theorem weightedDilation_antiWeight_inner_mul (a b : ℝ) (w : ℝ → ℂ) (G : V → ℂ) (e x : V) :
    weightedDilation a b (antiWeight a w) (fun y => (inner ℝ e y : ℂ) * G y) x =
      (inner ℝ e x : ℂ) * weightedDilation a b (fun s => -∫ σ in a..s, w σ) G x := by
  rw [weightedDilation, weightedDilation, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hc : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have h1 : ((Real.exp (-s) : ℝ) : ℂ) * ((Real.exp s : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have h2 : dilate (Real.exp s) (fun y => (inner ℝ e y : ℂ) * G y) x =
      ((Real.exp s : ℝ) : ℂ) * ((inner ℝ e x : ℂ) * dilate (Real.exp s) G x) := by
    rw [inner_mul_dilate_eq G e hc x, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc,
      Complex.ofReal_one, one_mul]
  simp only [antiWeight]
  rw [h2]
  linear_combination (-(∫ σ in a..s, w σ) * (inner ℝ e x : ℂ) * dilate (Real.exp s) G x) * h1

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Differentiation under the integral sign** for weighted dilation averages: for a `C^1` weight
`w` and `G ∈ C^1`, `DA(x) v = ∫_a^b w(s) D(G_{e^s})(x) v ds`
(`intervalIntegral.fderiv_integral_apply_of_contDiff`). -/
theorem fderiv_weightedDilation_apply (a b : ℝ) {w : ℝ → ℂ} (hw : ContDiff ℝ 1 w) {G : V → ℂ}
    (hG : ContDiff ℝ 1 G) (x v : V) :
    fderiv ℝ (weightedDilation a b w G) x v =
      ∫ s in a..b, w s * fderiv ℝ (dilate (Real.exp s) G) x v := by
  change fderiv ℝ (fun x => ∫ s in a..b, w s * dilate (Real.exp s) G x) x v = _
  rw [intervalIntegral.fderiv_integral_apply_of_contDiff (contDiff_weight_mul_dilate_exp hw hG)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [fderiv_const_mul (differentiableAt_dilate (hG.differentiable one_ne_zero) _ x)]
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Integration by parts along the dilations**: for smooth `w` with `∫_a^b w = 0` and smooth `G`,
the weighted dilation average `A` with the weight `-∫_a^s w` satisfies
`n A(x) + DA(x) x = ∫_a^b w(s) G_{e^s}(x) ds`. The left side is
`-∫_a^b (∫_a^s w) d/ds G_{e^s}(x) ds` by Euler's identity (`Rd.hasDerivAt_dilate_exp`), and
integration by parts (Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul`) has no boundary
terms. -/
theorem finrank_mul_add_fderiv_weightedDilation_primitive {a b : ℝ} {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (hw0 : ∫ s in a..b, w s = 0) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (x : V) :
    (finrank ℝ V : ℂ) * weightedDilation a b (fun s => -∫ σ in a..s, w σ) G x +
        fderiv ℝ (weightedDilation a b (fun s => -∫ σ in a..s, w σ) G) x x =
      weightedDilation a b w G x := by
  have hW : ∀ s, HasDerivAt (fun s => ∫ σ in a..s, w σ) (w s) s := fun s =>
    (hw.continuous.integral_hasStrictDerivAt a s).hasDerivAt
  have hWc : Continuous fun s => ∫ σ in a..s, w σ := (contDiff_primitive hw a).continuous
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
  have hD : ∀ s, HasDerivAt (fun s => dilate (Real.exp s) G x)
      ((finrank ℝ V : ℂ) * dilate (Real.exp s) G x + fderiv ℝ (dilate (Real.exp s) G) x x) s :=
    fun s => hasDerivAt_dilate_exp (hG1.differentiable one_ne_zero) x s
  have hDc : Continuous fun s => dilate (Real.exp s) G x :=
    (continuous_dilate_exp hG.continuous).comp (continuous_const.prodMk continuous_id)
  have hFc := continuous_fderiv_dilate_exp_apply hG1 x
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun s _ => hD s)
    (fun s _ => hW s) (((continuous_const.mul hDc).add hFc).intervalIntegrable a b)
    (hw.continuous.intervalIntegrable a b)
  rw [intervalIntegral.integral_same, hw0, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  have h1 : Continuous fun s =>
      (finrank ℝ V : ℂ) * (-(∫ σ in a..s, w σ) * dilate (Real.exp s) G x) :=
    continuous_const.mul (hWc.neg.mul hDc)
  have h2 : Continuous fun s => -(∫ σ in a..s, w σ) * fderiv ℝ (dilate (Real.exp s) G) x x :=
    hWc.neg.mul hFc
  rw [fderiv_weightedDilation_apply a b ((contDiff_primitive hw a).neg.of_le
    (by exact_mod_cast le_top)) hG1, weightedDilation, weightedDilation,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (h1.intervalIntegrable a b) (h2.intervalIntegrable a b)]
  calc ∫ s in a..b, ((finrank ℝ V : ℂ) * (-(∫ σ in a..s, w σ) * dilate (Real.exp s) G x) +
        -(∫ σ in a..s, w σ) * fderiv ℝ (dilate (Real.exp s) G) x x)
      = ∫ s in a..b, -(((finrank ℝ V : ℂ) * dilate (Real.exp s) G x +
          fderiv ℝ (dilate (Real.exp s) G) x x) * ∫ σ in a..s, w σ) :=
        intervalIntegral.integral_congr fun s _ => by ring
    _ = ∫ s in a..b, dilate (Real.exp s) G x * w s := by rw [intervalIntegral.integral_neg, hibp]
    _ = ∫ s in a..b, w s * dilate (Real.exp s) G x :=
        intervalIntegral.integral_congr fun s _ => mul_comm _ _

omit [MeasurableSpace V] [BorelSpace V] in
/-- **A weighted dilation average as a divergence**: for smooth `w` with `∫_a^b w = 0` and smooth
`G`, `A_w G = ∑_i ∂_{e_i} A_W(⟪e_i, ·⟫ G)` with the anti-weight `W = Rd.antiWeight a w`. The terms
are `⟪e_i, x⟫` times the average with the weight `-∫_a^s w`
(`Rd.weightedDilation_antiWeight_inner_mul`), whose divergence is computed by
`Rd.sum_fderiv_inner_mul` and `Rd.finrank_mul_add_fderiv_weightedDilation_primitive`. -/
theorem weightedDilation_eq_sum_fderiv {a b : ℝ} {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (hw0 : ∫ s in a..b, w s = 0) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (x : V) :
    weightedDilation a b w G x = ∑ i, fderiv ℝ (weightedDilation a b (antiWeight a w)
      (fun y => (inner ℝ (gridBasis V i) y : ℂ) * G y)) x (gridBasis V i) := by
  have h : ∀ i, weightedDilation a b (antiWeight a w)
      (fun y => (inner ℝ (gridBasis V i) y : ℂ) * G y) = fun y =>
        (inner ℝ (gridBasis V i) y : ℂ) * weightedDilation a b (fun s => -∫ σ in a..s, w σ) G y :=
    fun i => funext fun y => weightedDilation_antiWeight_inner_mul a b w G _ y
  simp_rw [h]
  rw [sum_fderiv_inner_mul (gridBasis V) ((contDiff_weightedDilation a b
    (contDiff_primitive hw a).neg hG).differentiable (by simp) x),
    finrank_mul_add_fderiv_weightedDilation_primitive hw hw0 hG x]

/-- The anti-weight of a continuous weight is continuous: the primitive `s ↦ ∫_a^s w` is
continuous (Mathlib's `intervalIntegral.continuous_primitive`). -/
theorem continuous_antiWeight (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w) :
    Continuous (antiWeight a w) :=
  ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).neg).mul
    (intervalIntegral.continuous_primitive (fun _ _ => hw.intervalIntegrable _ _) a)

/-- The exponential `s ↦ -(c⁻¹ e^{-cs})` has the derivative `e^{-cs}` for `c ≠ 0`. -/
theorem hasDerivAt_neg_inv_mul_exp {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => -(c⁻¹ * Real.exp (-(c * s)))) (Real.exp (-(c * s))) s := by
  have h := ((((hasDerivAt_id' s).const_mul c).neg).exp.const_mul c⁻¹).neg
  convert h using 1
  simp only [Pi.neg_apply]
  field_simp

/-- **The moments of the anti-weight**: for continuous `w` with `∫_a^b w = 0` and `r ∈ ℕ`,
`∫_a^b W(s) e^{-rs} ds = -(r + 1)⁻¹ ∫_a^b w(s) e^{-(r+1)s} ds` with `W = Rd.antiWeight a w`, by
integration by parts against `-(r + 1)⁻¹ e^{-(r+1)s}` (Mathlib's
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`). -/
theorem integral_antiWeight_mul_exp {a b : ℝ} {w : ℝ → ℂ} (hw : Continuous w)
    (hw0 : ∫ s in a..b, w s = 0) (r : ℕ) :
    ∫ s in a..b, antiWeight a w s * ((Real.exp (-(r * s)) : ℝ) : ℂ) =
      -((r : ℂ) + 1)⁻¹ * ∫ s in a..b, w s * ((Real.exp (-((r + 1 : ℕ) * s)) : ℝ) : ℂ) := by
  have hc : ((r : ℝ) + 1) ≠ 0 := by positivity
  have hW : ∀ s, HasDerivAt (fun s => ∫ σ in a..s, w σ) (w s) s := fun s =>
    (hw.integral_hasStrictDerivAt a s).hasDerivAt
  have hE : Continuous fun s => ((Real.exp (-(((r : ℝ) + 1) * s)) : ℝ) : ℂ) := by fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun s _ => hW s)
    (fun s _ => (hasDerivAt_neg_inv_mul_exp hc s).ofReal_comp)
    (hw.intervalIntegrable a b) (hE.intervalIntegrable a b)
  rw [intervalIntegral.integral_same, hw0, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  calc ∫ s in a..b, antiWeight a w s * ((Real.exp (-(r * s)) : ℝ) : ℂ)
      = -∫ s in a..b, (∫ σ in a..s, w σ) * ((Real.exp (-(((r : ℝ) + 1) * s)) : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun s _ => ?_
        have he : Real.exp (-s) * Real.exp (-(r * s)) = Real.exp (-(((r : ℝ) + 1) * s)) := by
          rw [← Real.exp_add]
          ring_nf
        simp only [antiWeight]
        rw [← he, Complex.ofReal_mul]
        ring
    _ = -((r : ℂ) + 1)⁻¹ * ∫ s in a..b, w s * ((Real.exp (-((r + 1 : ℕ) * s)) : ℝ) : ℂ) := by
        rw [hibp, neg_neg, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_neg, Complex.ofReal_mul,
          Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
        ring

/-! ### Iterated anti-weights and the higher divergence kernels -/

/-- The **iterated anti-weights** `w_0 = w`, `w_{k+1} = Rd.antiWeight a w_k`. -/
noncomputable def iterWeight (a : ℝ) (w : ℝ → ℂ) (k : ℕ) : ℝ → ℂ := (antiWeight a)^[k] w

/-- `w_{k+1}` of `w` is `w_k` of the anti-weight of `w`. -/
theorem iterWeight_succ (a : ℝ) (w : ℝ → ℂ) (k : ℕ) :
    iterWeight a w (k + 1) = iterWeight a (antiWeight a w) k :=
  Function.iterate_succ_apply _ _ _

/-- The iterated anti-weights of a smooth weight are smooth. -/
theorem contDiff_iterWeight (a : ℝ) {w : ℝ → ℂ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iterWeight a w k) := by
  induction k generalizing w with
  | zero => exact hw
  | succ k ih => rw [iterWeight_succ]; exact ih (contDiff_antiWeight a hw)

/-- The zeroth moment of a weight is its integral. -/
theorem integral_mul_exp_zero (a b : ℝ) (w : ℝ → ℂ) :
    ∫ s in a..b, w s * ((Real.exp (-(((0 : ℕ) : ℝ) * s)) : ℝ) : ℂ) = ∫ s in a..b, w s := by
  simp

/-- **Moments of the iterated anti-weights**: if the moments `∫_a^b w(s) e^{-r's} ds` of a
continuous `w` vanish for `r' ≤ r + k`, then `∫_a^b w_k(s) e^{-rs} ds = 0`, by induction on `k`
with `Rd.integral_antiWeight_mul_exp`. -/
theorem integral_iterWeight_mul_exp_eq_zero {a b : ℝ} {w : ℝ → ℂ} (hw : Continuous w) {k r : ℕ}
    (hmom : ∀ r' ≤ r + k, ∫ s in a..b, w s * ((Real.exp (-(r' * s)) : ℝ) : ℂ) = 0) :
    ∫ s in a..b, iterWeight a w k s * ((Real.exp (-(r * s)) : ℝ) : ℂ) = 0 := by
  induction k generalizing w with
  | zero => exact hmom r (by omega)
  | succ k ih =>
    rw [iterWeight_succ]
    have hw0 : ∫ s in a..b, w s = 0 := by
      rw [← integral_mul_exp_zero]
      exact hmom 0 (by omega)
    refine ih (continuous_antiWeight a hw) fun r' hr' => ?_
    rw [integral_antiWeight_mul_exp hw hw0, hmom (r' + 1) (by omega), mul_zero]

/-- The iterated anti-weights of a continuous weight are continuous. -/
theorem continuous_iterWeight (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w) (k : ℕ) :
    Continuous (iterWeight a w k) := by
  induction k generalizing w with
  | zero => exact hw
  | succ k ih => rw [iterWeight_succ]; exact ih (continuous_antiWeight a hw)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The products `∏_l ⟪e_{i_l}, x⟫ G(x)` of a smooth `G` with the coordinates along a word `i` are
smooth. -/
theorem contDiff_prod_inner_mul {G : V → ℂ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun y => (∏ l, (inner ℝ (gridBasis V (i l)) y : ℂ)) * G y :=
  (contDiff_prod (t := Finset.univ) (f := fun l y => (inner ℝ (gridBasis V (i l)) y : ℂ))
    fun l _ => Complex.ofRealCLM.contDiff.comp (innerSL ℝ (gridBasis V (i l))).contDiff).mul hG

omit [MeasurableSpace V] [BorelSpace V] in
/-- The products `⟪e_j, x⟫ G(x)` of a smooth `G` with a coordinate are smooth. -/
theorem contDiff_inner_mul {G : V → ℂ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (j : Fin (finrank ℝ V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => (inner ℝ (gridBasis V j) y : ℂ) * G y :=
  (Complex.ofRealCLM.contDiff.comp (innerSL ℝ (gridBasis V j)).contDiff).mul hG

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Products `c(x) G(x)` vanish where `G` vanishes. -/
theorem mul_eq_zero_of_lt_norm {G : V → ℂ} {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) (c : V → ℂ) :
    ∀ z, R < ‖z‖ → c z * G z = 0 := fun z hz => by rw [hR z hz, mul_zero]

/-- The **higher divergence kernel** of the word `i = (i_0, …, i_{m-1})`: the weighted dilation
average `∫_a^b w_m(s) (x^i G)_{e^s} ds` of `x^i G(x) = ∏_l ⟪e_{i_l}, x⟫ G(x)` with the iterated
anti-weight `w_m = Rd.iterWeight a w m`. If the moments of `w` of the orders `0, …, m - 1` vanish,
`A_w G = ∑_i ∂^{e_i}` of these kernels (`Rd.weightedDilation_eq_sum_iteratedLineDeriv`). -/
noncomputable def higherDivKernel (a b : ℝ) (w : ℝ → ℂ) (G : V → ℂ) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) : V → ℂ :=
  weightedDilation a b (iterWeight a w m)
    (fun y => (∏ l, (inner ℝ (gridBasis V (i l)) y : ℂ)) * G y)

/-- The higher divergence kernel of smooth `w` and of a smooth `G` that vanishes outside a ball, as
a Schwartz function (it is smooth with compact support). -/
noncomputable def higherDivSchwartz {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) : 𝓢(V, ℂ) :=
  (hasCompactSupport_weightedDilation hab (iterWeight a w m)
    (mul_eq_zero_of_lt_norm hR fun y => ∏ l, (inner ℝ (gridBasis V (i l)) y : ℂ))).toSchwartzMap
    (contDiff_weightedDilation a b (contDiff_iterWeight a hw m) (contDiff_prod_inner_mul hG i))

omit [MeasurableSpace V] [BorelSpace V] in
/-- The values of `Rd.higherDivSchwartz` are those of `Rd.higherDivKernel`. -/
theorem higherDivSchwartz_apply {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) (x : V) :
    higherDivSchwartz hab hw hG hR i x = higherDivKernel a b w G i x :=
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Words of the anti-weight**: the kernel of the word `i` for the anti-weight of `w` and
`⟪e_j, ·⟫ G` is the kernel of the word `(j, i)` for `w` and `G`. -/
theorem higherDivSchwartz_antiWeight {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) {m : ℕ}
    (j : Fin (finrank ℝ V)) (i : Fin m → Fin (finrank ℝ V)) :
    higherDivSchwartz hab (contDiff_antiWeight a hw) (contDiff_inner_mul hG j)
        (mul_eq_zero_of_lt_norm hR fun y => (inner ℝ (gridBasis V j) y : ℂ)) i =
      higherDivSchwartz hab hw hG hR (Fin.cons j i : Fin (m + 1) → Fin (finrank ℝ V)) := by
  ext x
  rw [higherDivSchwartz_apply, higherDivSchwartz_apply, higherDivKernel, higherDivKernel,
    iterWeight_succ]
  congr 1
  funext y
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

omit [MeasurableSpace V] [BorelSpace V] in
/-- **A weighted dilation average as a sum of derivatives of order `m`**: if `w` is smooth with
vanishing moments `∫_a^b w(s) e^{-rs} ds = 0` for `r < m` and `G` is smooth and vanishes outside a
ball, then `A_w G = ∑_i ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} K_i` over the words `i` of length `m`, with
the higher divergence kernels `K_i` (`Rd.higherDivSchwartz`). By induction on `m`: one step is
`Rd.weightedDilation_eq_sum_fderiv`, and the anti-weight keeps the vanishing moments
(`Rd.integral_antiWeight_mul_exp`). -/
theorem weightedDilation_eq_sum_iteratedLineDeriv {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {G : V → ℂ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) {m : ℕ}
    (hmom : ∀ r < m, ∫ s in a..b, w s * ((Real.exp (-(r * s)) : ℝ) : ℂ) = 0) (x : V) :
    weightedDilation a b w G x = ∑ i : Fin m → Fin (finrank ℝ V),
      (∂^{fun l => gridBasis V (i l)} (higherDivSchwartz hab hw hG hR i) : 𝓢(V, ℂ)) x := by
  induction m generalizing w G x with
  | zero =>
    simp [higherDivSchwartz_apply, higherDivKernel, iterWeight]
  | succ m ih =>
    have hw0 : ∫ s in a..b, w s = 0 := by
      rw [← integral_mul_exp_zero]
      exact hmom 0 (by omega)
    have hmom' : ∀ r < m, ∫ s in a..b, antiWeight a w s * ((Real.exp (-(r * s)) : ℝ) : ℂ) = 0 :=
      fun r hr => by
        rw [integral_antiWeight_mul_exp hw.continuous hw0, hmom (r + 1) (by omega), mul_zero]
    have hS : ∀ j, weightedDilation a b (antiWeight a w)
        (fun y => (inner ℝ (gridBasis V j) y : ℂ) * G y) =
          ⇑(∑ i : Fin m → Fin (finrank ℝ V), ∂^{fun l => gridBasis V (i l)}
            (higherDivSchwartz hab hw hG hR (Fin.cons j i : Fin (m + 1) → Fin (finrank ℝ V)))) :=
      fun j => funext fun y => by
        rw [ih (contDiff_antiWeight a hw) (contDiff_inner_mul hG j)
          (mul_eq_zero_of_lt_norm hR fun y => (inner ℝ (gridBasis V j) y : ℂ)) hmom' y, sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [higherDivSchwartz_antiWeight]
    rw [weightedDilation_eq_sum_fderiv hw hw0 hG x]
    simp_rw [hS]
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin (finrank ℝ V)) _ _ fun _ => rfl,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv, LineDeriv.lineDerivOp_sum, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    rfl

/-- **The higher divergence kernels have mean zero**: if the moments `∫_a^b w(s) e^{-rs} ds` of a
continuous `w` vanish for `r ≤ m`, then `∫ K_i = (∫_a^b w_m) ∫ x^i G = 0` for every word `i` of
length `m` (`Rd.integral_weightedDilation`, `Rd.integral_iterWeight_mul_exp_eq_zero`). -/
theorem integral_higherDivKernel_eq_zero {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ} (hw : Continuous w)
    {G : V → ℂ} (hG : Continuous G) {R : ℝ} (hR : ∀ z, R < ‖z‖ → G z = 0) {m : ℕ}
    (hmom : ∀ r ≤ m, ∫ s in a..b, w s * ((Real.exp (-(r * s)) : ℝ) : ℂ) = 0)
    (i : Fin m → Fin (finrank ℝ V)) : ∫ x, higherDivKernel a b w G i x = 0 := by
  have hc : Continuous fun y => (∏ l, (inner ℝ (gridBasis V (i l)) y : ℂ)) * G y :=
    (continuous_finsetProd _ fun l _ =>
      Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)).mul hG
  rw [higherDivKernel, integral_weightedDilation hab (continuous_iterWeight a hw m) hc
    (mul_eq_zero_of_lt_norm hR _), ← integral_mul_exp_zero,
    integral_iterWeight_mul_exp_eq_zero (r := 0) hw fun r' hr' => hmom r' (by omega), zero_mul]

/-! ### Supports in a cone -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Products `c(x) G(x)` of a kernel supported in `-K` are supported in `-K`. -/
theorem ConeSupported.mul_left {G : V → ℂ} (hG : Ω.ConeSupported G) (c : V → ℂ) :
    Ω.ConeSupported fun y => c y * G y := fun y hy => hG y (right_ne_zero_of_mul hy)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Weighted dilation averages of cone kernels are cone kernels**: if `G` is supported in `-K`,
so is every weighted dilation average of `G`, since `A_w G(y) ≠ 0` needs `G(e^s y) ≠ 0` for some
`s`, and `-e^s y ∈ K` gives `-y ∈ K` (`Rd.LipschitzGraph.smul_mem_cone`). -/
theorem coneSupported_weightedDilation {G : V → ℂ} (hG : Ω.ConeSupported G) (a b : ℝ)
    (w : ℝ → ℂ) : Ω.ConeSupported (weightedDilation a b w G) := fun y hy => by
  by_contra hny
  refine hy (weightedDilation_eq_zero a b w fun s _ => ?_)
  by_contra hne
  have h := Ω.smul_mem_cone (inv_pos.2 (Real.exp_pos s)) (hG _ hne)
  rw [smul_neg, inv_smul_smul₀ (Real.exp_pos s).ne'] at h
  exact hny h

omit [MeasurableSpace V] [BorelSpace V] in
/-- The higher divergence kernels of a kernel supported in `-K` are supported in `-K`. -/
theorem coneSupported_higherDivKernel {G : V → ℂ} (hG : Ω.ConeSupported G) (a b : ℝ)
    (w : ℝ → ℂ) {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) :
    Ω.ConeSupported (higherDivKernel a b w G i) :=
  Ω.coneSupported_weightedDilation (ConeSupported.mul_left Ω hG _) a b _

end LipschitzGraph

/-! ### Changes of the interval, linearity and dilation -/

/-- **Interval integrals only see the support**: if `f` vanishes outside `(a, b] ⊆ (a', b']`, then
`∫_a^b f = ∫_{a'}^{b'} f`, both being `∫ f` (Mathlib's
`intervalIntegral.integral_eq_integral_of_support_subset`). -/
theorem intervalIntegral_eq_of_support_subset {f : ℝ → ℂ} {a b a' b' : ℝ}
    (h : Function.support f ⊆ Ioc a b) (h' : Ioc a b ⊆ Ioc a' b') :
    ∫ s in a..b, f s = ∫ s in a'..b', f s :=
  (intervalIntegral.integral_eq_integral_of_support_subset h).trans
    (intervalIntegral.integral_eq_integral_of_support_subset (h.trans h')).symm

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A weighted dilation average does not change if the interval grows beyond the support of the
weight (`Rd.intervalIntegral_eq_of_support_subset`). -/
theorem weightedDilation_eq_of_support {a b a' b' : ℝ} {w : ℝ → ℂ}
    (h : ∀ s, w s ≠ 0 → s ∈ Ioc a b) (h' : Ioc a b ⊆ Ioc a' b') (G : V → ℂ) (x : V) :
    weightedDilation a b w G x = weightedDilation a' b' w G x :=
  intervalIntegral_eq_of_support_subset (fun s hs => h s (left_ne_zero_of_mul hs)) h'

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Weighted dilation averages are linear in the weight**:
`A_{∑_l c_l w_l} G = ∑_l c_l A_{w_l} G` for continuous `w_l` and `G`. -/
theorem weightedDilation_sum {ι : Type*} (t : Finset ι) (c : ι → ℂ) {w : ι → ℝ → ℂ}
    (hw : ∀ l ∈ t, Continuous (w l)) {G : V → ℂ} (hG : Continuous G) (a b : ℝ) (x : V) :
    weightedDilation a b (fun s => ∑ l ∈ t, c l * w l s) G x =
      ∑ l ∈ t, c l * weightedDilation a b (w l) G x := by
  have hD : Continuous fun s => dilate (Real.exp s) G x :=
    (continuous_dilate_exp hG).comp (continuous_const.prodMk continuous_id)
  simp only [weightedDilation]
  calc ∫ s in a..b, (∑ l ∈ t, c l * w l s) * dilate (Real.exp s) G x
      = ∫ s in a..b, ∑ l ∈ t, c l * (w l s * dilate (Real.exp s) G x) :=
        intervalIntegral.integral_congr fun s _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
    _ = ∑ l ∈ t, ∫ s in a..b, c l * (w l s * dilate (Real.exp s) G x) :=
        intervalIntegral.integral_finsetSum fun l hl =>
          (continuous_const.mul ((hw l hl).mul hD)).intervalIntegrable a b
    _ = _ := Finset.sum_congr rfl fun l _ => intervalIntegral.integral_const_mul _ _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Weighted dilation averages of differences of continuous weights: `A_{w - v} G = A_w G - A_v G`
for continuous `G`. -/
theorem weightedDilation_sub {w v : ℝ → ℂ} (hw : Continuous w) (hv : Continuous v) {G : V → ℂ}
    (hG : Continuous G) (a b : ℝ) (x : V) :
    weightedDilation a b (fun s => w s - v s) G x =
      weightedDilation a b w G x - weightedDilation a b v G x := by
  have hD : Continuous fun s => dilate (Real.exp s) G x :=
    (continuous_dilate_exp hG).comp (continuous_const.prodMk continuous_id)
  simp only [weightedDilation, sub_mul]
  exact intervalIntegral.integral_sub ((hw.mul hD).intervalIntegrable a b)
    ((hv.mul hD).intervalIntegrable a b)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Dilating a weighted dilation average shifts the weight**:
`(A_w G)_{e^{-t}} = ∫_{a-t}^{b-t} w(s + t) G_{e^s} ds`, since
`(G_{e^s})_{e^{-t}} = G_{e^{s-t}}` (`Rd.dilate_dilate`) and the substitution `s ↦ s + t` (Mathlib's
`intervalIntegral.integral_comp_add_right`). -/
theorem dilate_exp_neg_weightedDilation (a b t : ℝ) (w : ℝ → ℂ) (G : V → ℂ) (x : V) :
    dilate (Real.exp (-t)) (weightedDilation a b w G) x =
      weightedDilation (a - t) (b - t) (fun s => w (s + t)) G x := by
  have h := intervalIntegral.integral_comp_add_right
    (fun s => w s * dilate (Real.exp (s - t)) G x) t (a := a - t) (b := b - t)
  simp only [add_sub_cancel_right, sub_add_cancel] at h
  change ((Real.exp (-t) ^ finrank ℝ V : ℝ) : ℂ) *
      (∫ s in a..b, w s * dilate (Real.exp s) G (Real.exp (-t) • x)) =
    ∫ s in (a - t)..(b - t), w (s + t) * dilate (Real.exp s) G x
  rw [h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hd : dilate (Real.exp (s - t)) G x =
      ((Real.exp (-t) ^ finrank ℝ V : ℝ) : ℂ) * dilate (Real.exp s) G (Real.exp (-t) • x) := by
    rw [sub_eq_neg_add, Real.exp_add, ← dilate_dilate]
    rfl
  rw [hd]
  ring

/-! ### The smoothing weight and the smoothed bump -/

/-- The smooth bump on `ℝ` centred at `log 2 / 2` with inner radius `log 2 / 4` and outer radius
`log 2 / 2`, supported in `[0, log 2]`. -/
noncomputable def logBumpBase : ContDiffBump (Real.log 2 / 2) :=
  ⟨Real.log 2 / 4, Real.log 2 / 2, div_pos (Real.log_pos one_lt_two) four_pos,
    by linarith [Real.log_pos one_lt_two]⟩

/-- The **smoothing weight** `ρ`: a smooth function with `∫ ρ = 1` that vanishes outside
`(0, log 2)` (the normalised bump `logBumpBase`). -/
noncomputable def dilationWeight (s : ℝ) : ℂ := ((logBumpBase.normed volume s : ℝ) : ℂ)

/-- The smoothing weight is smooth. -/
theorem contDiff_dilationWeight : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dilationWeight :=
  Complex.ofRealCLM.contDiff.comp (logBumpBase.contDiff_normed (n := ⊤))

/-- The smoothing weight vanishes outside `(0, log 2)` (Mathlib's
`ContDiffBump.support_normed_eq`). -/
theorem mem_Ioo_of_dilationWeight_ne_zero {s : ℝ} (h : dilationWeight s ≠ 0) :
    s ∈ Ioo 0 (Real.log 2) := by
  have hs : s ∈ Function.support (logBumpBase.normed volume) := fun h0 =>
    h (by simp [dilationWeight, h0])
  rw [logBumpBase.support_normed_eq, Real.ball_eq_Ioo] at hs
  change s ∈ Ioo (Real.log 2 / 2 - Real.log 2 / 2) (Real.log 2 / 2 + Real.log 2 / 2) at hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The smoothing weight has integral `1` over `[0, log 2]` (Mathlib's
`ContDiffBump.integral_normed`). -/
theorem integral_dilationWeight : ∫ s in (0 : ℝ)..Real.log 2, dilationWeight s = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset fun s hs =>
    Ioo_subset_Ioc_self (mem_Ioo_of_dilationWeight_ne_zero hs)]
  simp only [dilationWeight]
  rw [integral_complex_ofReal, logBumpBase.integral_normed, Complex.ofReal_one]

/-- The **smoothed bump** `∫_0^{log 2} ρ(s) b_{e^s} ds` of a bump `b` of radius `R`: a bump of the
same radius, an average of the dilates `b_t`, `1 ≤ t ≤ 2`. Its moment kernels are weighted dilation
averages of `b` with smooth weights (`Rd.LocalMeansBump.momentKernel_dilationSmoothed`). -/
noncomputable def LocalMeansBump.dilationSmoothed (b : LocalMeansBump V) : LocalMeansBump V where
  toFun := weightedDilation 0 (Real.log 2) dilationWeight b.toFun
  radius := b.radius
  radius_nonneg := b.radius_nonneg
  contDiff := contDiff_weightedDilation _ _ contDiff_dilationWeight b.contDiff
  eq_zero z hz := weightedDilation_eq_zero_of_lt (Real.log_nonneg one_le_two) _ b.eq_zero
    (by rwa [neg_zero, Real.exp_zero, mul_one])
  integral_eq_one := by
    rw [integral_weightedDilation (Real.log_nonneg one_le_two)
      contDiff_dilationWeight.continuous b.contDiff.continuous
      b.eq_zero, integral_dilationWeight, b.integral_eq_one, one_mul]

/-- The smoothed bump has the radius of the bump. -/
theorem LocalMeansBump.dilationSmoothed_radius (b : LocalMeansBump V) :
    b.dilationSmoothed.radius = b.radius :=
  rfl

/-- The smoothed bump of a bump supported in `-K` is supported in `-K`
(`Rd.LipschitzGraph.coneSupported_weightedDilation`). -/
theorem LipschitzGraph.coneSupported_dilationSmoothed (Ω : LipschitzGraph V)
    {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) :
    Ω.ConeSupported b.dilationSmoothed.toFun :=
  Ω.coneSupported_weightedDilation hb _ _ _

/-! ### The moment weights -/

/-- The **moment weight** `u(s) = ∑_{l<L} a_l ρ(s + log(l + 1))` with the coefficients
`a_l = Rd.jacksonCoeff L l`: the moment kernel of order `L` of the smoothed bump is the weighted
dilation average of `b` with the weight `u` (`Rd.LocalMeansBump.momentKernel_dilationSmoothed`). -/
noncomputable def momentWeight (L : ℕ) (s : ℝ) : ℂ :=
  ∑ l ∈ Finset.range L, jacksonCoeff L l * dilationWeight (s + Real.log ((l : ℝ) + 1))

/-- The **kernel weight** `u(s - log 2) - u(s)`: the local means kernels of order `L` of the
smoothed bump are dilates of the weighted dilation average of `b` with this weight
(`Rd.LocalMeansBump.kernel_succ_dilationSmoothed`). -/
noncomputable def kernelWeight (L : ℕ) (s : ℝ) : ℂ :=
  momentWeight L (s - Real.log 2) - momentWeight L s

/-- The moment weights are smooth. -/
theorem contDiff_momentWeight (L : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (momentWeight L) :=
  ContDiff.sum fun _ _ => contDiff_const.mul (contDiff_dilationWeight.comp
    (contDiff_id.add contDiff_const))

/-- The kernel weights are smooth. -/
theorem contDiff_kernelWeight (L : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kernelWeight L) :=
  ((contDiff_momentWeight L).comp (contDiff_id.sub contDiff_const)).sub (contDiff_momentWeight L)

/-- `0 ≤ log(l + 1) ≤ log L` for `l < L`. -/
theorem log_succ_mem_Icc {L l : ℕ} (hl : l < L) :
    Real.log ((l : ℝ) + 1) ∈ Icc 0 (Real.log L) := by
  have h1 : (1 : ℝ) ≤ (l : ℝ) + 1 := by linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have h2 : (l : ℝ) + 1 ≤ L := by exact_mod_cast hl
  exact ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) h2⟩

/-- The shifted smoothing weights `ρ(s + log(l + 1))`, `l < L`, vanish outside
`(-log L, log 2]`. -/
theorem mem_Ioc_of_dilationWeight_add_ne_zero {L l : ℕ} (hl : l < L) {s : ℝ}
    (h : dilationWeight (s + Real.log ((l : ℝ) + 1)) ≠ 0) : s ∈ Ioc (-Real.log L) (Real.log 2) := by
  obtain ⟨h1, h2⟩ := mem_Ioo_of_dilationWeight_ne_zero h
  obtain ⟨h3, h4⟩ := log_succ_mem_Icc hl
  exact ⟨by linarith, by linarith⟩

/-- The moment weight vanishes outside `(-log L, log 2]`. -/
theorem mem_Ioc_of_momentWeight_ne_zero {L : ℕ} {s : ℝ} (h : momentWeight L s ≠ 0) :
    s ∈ Ioc (-Real.log L) (Real.log 2) := by
  obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact mem_Ioc_of_dilationWeight_add_ne_zero (Finset.mem_range.1 hl) (right_ne_zero_of_mul hne)

/-- The kernel weight vanishes outside `(-log L, 2 log 2]`. -/
theorem mem_Ioc_of_kernelWeight_ne_zero {L : ℕ} {s : ℝ} (h : kernelWeight L s ≠ 0) :
    s ∈ Ioc (-Real.log L) (2 * Real.log 2) := by
  have hlog := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  by_cases h1 : momentWeight L (s - Real.log 2) = 0
  · have h2 : momentWeight L s ≠ 0 := fun h2 => h (by rw [kernelWeight, h1, h2, sub_zero])
    obtain ⟨h3, h4⟩ := mem_Ioc_of_momentWeight_ne_zero h2
    exact ⟨h3, by linarith⟩
  · obtain ⟨h3, h4⟩ := mem_Ioc_of_momentWeight_ne_zero h1
    have h5 : 0 ≤ Real.log L := Real.log_natCast_nonneg L
    exact ⟨by linarith, by linarith⟩

/-- The interval `(-log L, 2 log 2]` of the kernel weights is not reversed. -/
theorem neg_log_le_two_mul_log_two (L : ℕ) : -Real.log L ≤ 2 * Real.log 2 := by
  have h1 := Real.log_natCast_nonneg L
  have h2 := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  linarith

/-- **The moment kernels of the smoothed bump**: `m = ∑_{l<L} a_l (b')_{1/(l+1)}` of the smoothed
bump `b'` is the weighted dilation average `∫_{-log L}^{log 2} u(s) b_{e^s} ds` with the moment
weight `u` (`Rd.dilate_exp_neg_weightedDilation` with `1/(l+1) = e^{-log(l+1)}`). -/
theorem LocalMeansBump.momentKernel_dilationSmoothed (b : LocalMeansBump V) (L : ℕ) :
    momentKernel b.dilationSmoothed.toFun L =
      weightedDilation (-Real.log L) (Real.log 2) (momentWeight L) b.toFun := by
  funext x
  have hterm : ∀ l ∈ Finset.range L, dilate (1 / ((l : ℝ) + 1)) b.dilationSmoothed.toFun x =
      weightedDilation (-Real.log L) (Real.log 2)
        (fun s => dilationWeight (s + Real.log ((l : ℝ) + 1))) b.toFun x := fun l hl => by
    have hc : (1 : ℝ) / ((l : ℝ) + 1) = Real.exp (-Real.log ((l : ℝ) + 1)) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
    obtain ⟨h3, h4⟩ := log_succ_mem_Icc (Finset.mem_range.1 hl)
    rw [hc]
    refine (dilate_exp_neg_weightedDilation 0 (Real.log 2) _ dilationWeight b.toFun x).trans
      (weightedDilation_eq_of_support (fun s hs => ?_)
        (Ioc_subset_Ioc (by linarith) (by linarith)) _ x)
    obtain ⟨h1, h2⟩ := mem_Ioo_of_dilationWeight_ne_zero hs
    exact ⟨by linarith, by linarith⟩
  rw [momentKernel, Finset.sum_congr rfl fun l hl => by rw [hterm l hl]]
  exact (weightedDilation_sum _ _ (fun l _ => contDiff_dilationWeight.continuous.comp
    (continuous_id.add continuous_const)) b.contDiff.continuous _ _ x).symm

/-- **The local means kernels of the smoothed bump**: `k_{j+1} = (m_2 - m)_{2^j}` with
`m_2 - m = ∫_{-log L}^{2 log 2} (u(s - log 2) - u(s)) b_{e^s} ds`, the weighted dilation average
with the kernel weight (`Rd.LocalMeansBump.kernel_succ_eq_dilate`,
`Rd.LocalMeansBump.momentKernel_dilationSmoothed`, `Rd.dilate_exp_neg_weightedDilation`). -/
theorem LocalMeansBump.kernel_succ_dilationSmoothed (b : LocalMeansBump V) (L j : ℕ) :
    b.dilationSmoothed.kernel L (j + 1) = dilate (2 ^ j)
      (weightedDilation (-Real.log L) (2 * Real.log 2) (kernelWeight L) b.toFun) := by
  rw [b.dilationSmoothed.kernel_succ_eq_dilate L j]
  congr 1
  funext y
  have hlog := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  have hL := Real.log_natCast_nonneg L
  have hcont := (contDiff_momentWeight L).continuous
  have h2 : dilate 2 (weightedDilation (-Real.log L) (Real.log 2) (momentWeight L) b.toFun) y =
      dilate (Real.exp (-(-Real.log 2)))
        (weightedDilation (-Real.log L) (Real.log 2) (momentWeight L) b.toFun) y := by
    rw [neg_neg, Real.exp_log two_pos]
  rw [b.momentKernel_dilationSmoothed, h2, dilate_exp_neg_weightedDilation,
    weightedDilation_eq_of_support (a' := -Real.log L) (b' := 2 * Real.log 2) (fun s hs => ?_)
      (Ioc_subset_Ioc (by linarith) (by linarith)),
    weightedDilation_eq_of_support (a' := -Real.log L) (b' := 2 * Real.log 2)
      (fun s hs => mem_Ioc_of_momentWeight_ne_zero hs) (Ioc_subset_Ioc le_rfl (by linarith)),
    ← weightedDilation_sub (w := fun s => momentWeight L (s + -Real.log 2))
      (hcont.comp (continuous_id.add continuous_const)) hcont b.contDiff.continuous]
  · congr 1
  · obtain ⟨h3, h4⟩ := mem_Ioc_of_momentWeight_ne_zero hs
    exact ⟨by linarith, by linarith⟩

/-! ### Vanishing moments of the kernel weights -/

/-- **Moments of the shifted smoothing weight**: for `l < L` and `r ∈ ℕ`,
`∫_{-log L}^{log 2} ρ(s + log(l + 1)) e^{-rs} ds = (l + 1)^r ∫_0^{log 2} ρ(s) e^{-rs} ds`, by the
substitution `s ↦ s + log(l + 1)` (Mathlib's `intervalIntegral.integral_comp_add_right`). -/
theorem integral_dilationWeight_add_mul_exp {L l : ℕ} (hl : l < L) (r : ℕ) :
    ∫ s in (-Real.log L)..(Real.log 2),
        dilationWeight (s + Real.log ((l : ℝ) + 1)) * ((Real.exp (-(r * s)) : ℝ) : ℂ) =
      ((l : ℂ) + 1) ^ r *
        ∫ s in (0 : ℝ)..Real.log 2, dilationWeight s * ((Real.exp (-(r * s)) : ℝ) : ℂ) := by
  obtain ⟨h3, h4⟩ := log_succ_mem_Icc hl
  have hlog := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  have h := intervalIntegral.integral_comp_add_right (fun s => dilationWeight s *
    ((Real.exp (-(r * (s - Real.log ((l : ℝ) + 1)))) : ℝ) : ℂ)) (Real.log ((l : ℝ) + 1))
    (a := -Real.log L) (b := Real.log 2)
  simp only [add_sub_cancel_right] at h
  rw [h, ← intervalIntegral_eq_of_support_subset (a := 0) (b := Real.log 2)
    (fun s hs => Ioo_subset_Ioc_self (mem_Ioo_of_dilationWeight_ne_zero (left_ne_zero_of_mul hs)))
    (Ioc_subset_Ioc (by linarith) (by linarith)), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have he : Real.exp (-(r * (s - Real.log ((l : ℝ) + 1)))) =
      ((l : ℝ) + 1) ^ r * Real.exp (-(r * s)) := by
    rw [show -(r * (s - Real.log ((l : ℝ) + 1))) = r * Real.log ((l : ℝ) + 1) + -(r * s) by ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [he]
  push_cast
  ring

/-- **Moments of the moment weight**: `∫_{-log L}^{log 2} u(s) e^{-rs} ds` is
`∑_{l<L} a_l (l + 1)^r` times the moment `∫_0^{log 2} ρ(s) e^{-rs} ds` of the smoothing weight
(`Rd.integral_dilationWeight_add_mul_exp`). -/
theorem integral_momentWeight_mul_exp (L r : ℕ) :
    ∫ s in (-Real.log L)..(Real.log 2), momentWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) =
      (∑ l ∈ Finset.range L, jacksonCoeff L l * ((l : ℂ) + 1) ^ r) *
        ∫ s in (0 : ℝ)..Real.log 2, dilationWeight s * ((Real.exp (-(r * s)) : ℝ) : ℂ) := by
  have hE : Continuous fun s : ℝ => ((Real.exp (-(r * s)) : ℝ) : ℂ) := by fun_prop
  have hcont : ∀ l : ℕ, Continuous fun s => jacksonCoeff L l *
      (dilationWeight (s + Real.log ((l : ℝ) + 1)) * ((Real.exp (-(r * s)) : ℝ) : ℂ)) := fun l =>
    continuous_const.mul ((contDiff_dilationWeight.continuous.comp
      (continuous_id.add continuous_const)).mul hE)
  simp only [momentWeight, Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum fun l _ => (hcont l).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [intervalIntegral.integral_const_mul,
    integral_dilationWeight_add_mul_exp (Finset.mem_range.1 hl)]

/-- **The kernel weights have vanishing moments**: `∫_{-log L}^{2 log 2} (u(s - log 2) - u(s))
e^{-rs} ds = 0` for `r < L`. The integral is `(2^{-r} - 1)` times the moment of the moment weight
`u` (substitution `s ↦ s - log 2`); the factor vanishes for `r = 0`, the moment for
`1 ≤ r < L` (`Rd.integral_momentWeight_mul_exp`, `Rd.sum_jacksonCoeff_mul_pow`). -/
theorem integral_kernelWeight_mul_exp {L r : ℕ} (hr : r < L) :
    ∫ s in (-Real.log L)..(2 * Real.log 2),
      kernelWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) = 0 := by
  have hlog := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  have hc := (contDiff_momentWeight L).continuous
  have hE : Continuous fun s : ℝ => ((Real.exp (-(r * s)) : ℝ) : ℂ) := by fun_prop
  have hsupp : ∀ (f : ℝ → ℂ), Function.support (fun s => momentWeight L s * f s) ⊆
      Ioc (-Real.log L) (Real.log 2) := fun f s hs =>
    mem_Ioc_of_momentWeight_ne_zero (left_ne_zero_of_mul hs)
  have h1 : ∫ s in (-Real.log L)..(2 * Real.log 2),
      momentWeight L (s - Real.log 2) * ((Real.exp (-(r * s)) : ℝ) : ℂ) =
        ((Real.exp (-(r * Real.log 2)) : ℝ) : ℂ) * ∫ s in (-Real.log L)..(Real.log 2),
          momentWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) := by
    have h := intervalIntegral.integral_comp_sub_right (fun s => momentWeight L s *
      ((Real.exp (-(r * (s + Real.log 2))) : ℝ) : ℂ)) (Real.log 2) (a := -Real.log L)
      (b := 2 * Real.log 2)
    simp only [sub_add_cancel] at h
    rw [h, ← intervalIntegral_eq_of_support_subset (hsupp _)
      (Ioc_subset_Ioc (by linarith) (by linarith)), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show -(r * (s + Real.log 2)) = -(r * Real.log 2) + -(r * s) by ring, Real.exp_add]
    push_cast
    ring
  have h2 : ∫ s in (-Real.log L)..(2 * Real.log 2),
      momentWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) = ∫ s in (-Real.log L)..(Real.log 2),
        momentWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) :=
    (intervalIntegral_eq_of_support_subset (hsupp _) (Ioc_subset_Ioc le_rfl (by linarith))).symm
  have hsplit : ∫ s in (-Real.log L)..(2 * Real.log 2),
      kernelWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) =
        (∫ s in (-Real.log L)..(2 * Real.log 2),
          momentWeight L (s - Real.log 2) * ((Real.exp (-(r * s)) : ℝ) : ℂ)) -
        ∫ s in (-Real.log L)..(2 * Real.log 2),
          momentWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) := by
    have hc1 : Continuous fun s =>
        momentWeight L (s - Real.log 2) * ((Real.exp (-(r * s)) : ℝ) : ℂ) :=
      (hc.comp (continuous_id.sub continuous_const)).mul hE
    have hc2 : Continuous fun s => momentWeight L s * ((Real.exp (-(r * s)) : ℝ) : ℂ) := hc.mul hE
    rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun s _ => by simp only [kernelWeight]; ring
  rw [hsplit, h1, h2, integral_momentWeight_mul_exp]
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · simp
  · rw [sum_jacksonCoeff_mul_pow hr1 hr]
    simp

/-! ### The higher divergence kernels of a bump -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The **higher divergence kernels** of a bump `b` for the word `i` of length `m` and the order
`L`: the higher divergence kernels (`Rd.higherDivSchwartz`) of `b` with the kernel weight
`u(s - log 2) - u(s)` on `[-log L, 2 log 2]`. The local means kernels of order `L` of the smoothed
bump are sums of their derivatives of order `m ≤ L`
(`Rd.LocalMeansBump.kernel_succ_eq_sum_higherKernel`). -/
noncomputable def higherKernel (L m : ℕ) (i : Fin m → Fin (finrank ℝ V)) : 𝓢(V, ℂ) :=
  higherDivSchwartz (neg_log_le_two_mul_log_two L) (contDiff_kernelWeight L) b.contDiff b.eq_zero i

/-- The values of the higher divergence kernels of a bump. -/
theorem higherKernel_apply (L m : ℕ) (i : Fin m → Fin (finrank ℝ V)) (x : V) :
    b.higherKernel L m i x =
      higherDivKernel (-Real.log L) (2 * Real.log 2) (kernelWeight L) b.toFun i x :=
  rfl

/-- **The local means kernels of the smoothed bump at dyadic scales as derivatives of order `m`**:
for `m ≤ L`,
`k_{j+1} = 2^{-jm} ∑_i ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} (K_i)_{2^j}` with the higher divergence kernels
`K_i` (`Rd.LocalMeansBump.kernel_succ_dilationSmoothed`,
`Rd.weightedDilation_eq_sum_iteratedLineDeriv` with the moments
`Rd.integral_kernelWeight_mul_exp`, and the chain rule for dilations
`Rd.iteratedLineDerivOp_schwartzDilate`). -/
theorem kernel_succ_eq_sum_higherKernel {L m : ℕ} (hmL : m ≤ L) (j : ℕ) (y : V) :
    b.dilationSmoothed.kernel L (j + 1) y = ((2 : ℂ) ^ (j * m))⁻¹ *
      ∑ i, (∂^{fun l => gridBasis V (i l)}
        (schwartzDilate (2 ^ j) (by positivity) (b.higherKernel L m i)) : 𝓢(V, ℂ)) y := by
  rw [b.kernel_succ_dilationSmoothed, dilate,
    weightedDilation_eq_sum_iteratedLineDeriv (neg_log_le_two_mul_log_two L)
      (contDiff_kernelWeight L) b.contDiff b.eq_zero (m := m)
      (fun r hr => integral_kernelWeight_mul_exp (by omega))]
  simp_rw [iteratedLineDerivOp_schwartzDilate, smul_apply, coe_schwartzDilate, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dilate]
  have h2 : ((2 : ℂ) ^ (j * m)) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_mul]
  push_cast
  field_simp
  rfl

/-- **The higher divergence kernels have mean zero** for `m < L`
(`Rd.integral_higherDivKernel_eq_zero`, `Rd.integral_kernelWeight_mul_exp`). -/
theorem integral_higherKernel {L m : ℕ} (hmL : m < L) (i : Fin m → Fin (finrank ℝ V)) :
    ∫ x, b.higherKernel L m i x = 0 :=
  integral_higherDivKernel_eq_zero (neg_log_le_two_mul_log_two L)
    (contDiff_kernelWeight L).continuous b.contDiff.continuous b.eq_zero
    (fun r hr => integral_kernelWeight_mul_exp (by omega)) i

/-- **The higher divergence kernels form Calderón–Zygmund families**: for `m < L`, the dilates
`(K_i)_{2^j}` have the Fourier overlap `Rd.meanZeroOverlap (K_i)` and the Hörmander constant
`4 H_{K_i}` (`Rd.isCZFamily_dilate_of_integral_eq_zero`). -/
theorem isCZFamily_higherKernel {L m : ℕ} (hmL : m < L) (i : Fin m → Fin (finrank ℝ V)) :
    IsCZFamily (fun j => dilate (2 ^ j) (b.higherKernel L m i : V → ℂ))
      (meanZeroOverlap (b.higherKernel L m i))
      (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.higherKernel L m i)) :=
  isCZFamily_dilate_of_integral_eq_zero _ (b.integral_higherKernel hmL i)

/-- The higher divergence kernels of a bump of radius `R` vanish outside the ball of radius
`L R` for `L ≥ 1` (`Rd.weightedDilation_eq_zero_of_lt` with `R e^{log L} = L R`). -/
theorem higherKernel_eq_zero_of_lt {L m : ℕ} (hL : 1 ≤ L) (i : Fin m → Fin (finrank ℝ V))
    {y : V} (hy : L * b.radius < ‖y‖) : b.higherKernel L m i y = 0 :=
  weightedDilation_eq_zero_of_lt (neg_log_le_two_mul_log_two L) _
    (mul_eq_zero_of_lt_norm b.eq_zero _)
    (by rwa [neg_neg, Real.exp_log (by exact_mod_cast hL), mul_comm])

/-- The higher divergence kernels of a bump have compact support
(`Rd.hasCompactSupport_weightedDilation`). -/
theorem hasCompactSupport_higherKernel (L m : ℕ) (i : Fin m → Fin (finrank ℝ V)) :
    HasCompactSupport (b.higherKernel L m i : V → ℂ) :=
  hasCompactSupport_weightedDilation (neg_log_le_two_mul_log_two L) _
    (mul_eq_zero_of_lt_norm b.eq_zero _)

/-- The higher divergence kernels of a bump of radius `R` and their dilates `(K_i)_{2^j}` are
supported in the closed ball of radius `L R`, for `L ≥ 1`. -/
theorem tsupport_dilate_higherKernel_subset_closedBall {L m : ℕ} (hL : 1 ≤ L)
    (i : Fin m → Fin (finrank ℝ V)) (j : ℕ) :
    tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)) ⊆ closedBall 0 (L * b.radius) := by
  refine tsupport_dilate_two_pow_subset isClosed_closedBall (fun y hy => ?_)
    (fun c hc y hy => ?_) j
  · rw [mem_closedBall, dist_zero_right]
    exact not_lt.1 fun h => hy (b.higherKernel_eq_zero_of_lt hL i h)
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (zero_le_one.trans hc)]
      at hy
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg y]

end LocalMeansBump

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- **The higher divergence kernels of a cone-supported bump lie in the reflected closed cone**:
for a bump of radius `R` supported in `-K` and `L ≥ 1`, every dilate `(K_i)_{2^j}` of its higher
divergence kernels is supported in `{y : -y ∈ KBar, ‖y‖ ≤ L R}`
(`Rd.LipschitzGraph.coneSupported_higherDivKernel`). -/
theorem tsupport_dilate_higherKernel_subset {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    {L m : ℕ} (hL : 1 ≤ L) (i : Fin m → Fin (finrank ℝ V)) (j : ℕ) :
    tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)) ⊆
      {y | -y ∈ Ω.closedCone} ∩ closedBall 0 (L * b.radius) := by
  refine subset_inter (tsupport_dilate_two_pow_subset
    (Ω.isClosed_closedCone.preimage continuous_neg) (fun y hy => ?_) (fun c hc y hy => ?_) j)
    (b.tsupport_dilate_higherKernel_subset_closedBall hL i j)
  · exact Ω.cone_subset_closedCone (Ω.coneSupported_higherDivKernel hb _ _ _ i y hy)
  · have h := Ω.smul_mem_closedCone (inv_nonneg.2 (zero_le_one.trans hc)) hy
    rwa [smul_neg, inv_smul_smul₀ (zero_lt_one.trans_le hc).ne'] at h

end LipschitzGraph

end Rd

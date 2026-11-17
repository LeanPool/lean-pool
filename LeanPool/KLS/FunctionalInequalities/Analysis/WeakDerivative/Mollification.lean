/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Mollification and weak derivatives from difference bounds
-/

@[expose] public section

section
open MeasureTheory
open scoped ContDiff

section WeakDerivativeMollification

open MeasureTheory Set Filter
open scoped Topology Convolution

/-! Mollification commutes with weak directional derivatives. -/

namespace FunctionalInequalities.Analysis

/-- **Mollification commutes with weak derivatives**: if `g` is the weak derivative
of `f` along `v`, then `φ.normed ⋆ f` is smooth with `∂ᵥ(φ.normed ⋆ f) = φ.normed ⋆ g`. -/
theorem fderiv_convolution_eq_of_hasWeakDerivAlong {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  let ρ : E → ℝ := φ.normed volume
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hρ : ContDiff ℝ 1 ρ := φ.contDiff_normed (n := 1)
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  let ψ : E → ℝ := fun y => ρ (x - y)
  have hψ : ContDiff ℝ 1 ψ :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψd (y : E) :
      fderiv ℝ ψ y v = -(fderiv ℝ ρ (x - y) v) := by
    have hd := ((hρ.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    have he := congrArg (fun A : E →L[ℝ] ℝ => A v) hd.fderiv
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.map_neg] using he
  have hw := h.2.2 ψ hψ hψc
  simp_rw [hψd, mul_neg] at hw
  rw [integral_neg] at hw
  have hi :
      (∫ y, f y * fderiv ℝ ρ (x - y) v ∂(volume : Measure E)) =
        ∫ y, g y * ρ (x - y) ∂(volume : Measure E) :=
    neg_injective hw
  have hint :
      Integrable
        (fun y => (ContinuousLinearMap.precompL E L)
          (fderiv ℝ ρ (x - y)) (f y))
        (volume : Measure E) :=
    ((hρc.fderiv ℝ).convolutionExists_left
      (ContinuousLinearMap.precompL E L)
      (hρ.continuous_fderiv one_ne_zero) h.1 x).integrable_swap
  have hconv :
      fderiv ℝ (convolution ρ f L volume) x v =
        ∫ y, fderiv ℝ ρ (x - y) v * f y ∂(volume : Measure E) := by
    rw [(hρc.hasFDerivAt_convolution_left L hρ h.1 x).fderiv]
    rw [convolution_eq_swap (ContinuousLinearMap.precompL E L)]
    rw [ContinuousLinearMap.integral_apply hint]
    rfl
  change fderiv ℝ (convolution ρ f L volume) x v =
    convolution ρ g L volume x
  calc
    fderiv ℝ (convolution ρ f L volume) x v =
        ∫ y, fderiv ℝ ρ (x - y) v * f y ∂(volume : Measure E) := hconv
    _ = ∫ y, f y * fderiv ℝ ρ (x - y) v ∂(volume : Measure E) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => mul_comm _ _
    _ = ∫ y, g y * ρ (x - y) ∂(volume : Measure E) := hi
    _ = convolution ρ g L volume x := by
      rw [convolution_eq_swap L]
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      change g y * ρ (x - y) = ρ (x - y) * g y
      exact mul_comm _ _

end FunctionalInequalities.Analysis

end WeakDerivativeMollification

section WeakDerivativeOfDifferenceBound

open MeasureTheory Set Filter
open scoped Topology

/-! Uniform `L²` bounds on difference quotients give a weak derivative in `L²`. -/

namespace FunctionalInequalities.Analysis

section MeasurableSpace

variable {X : Type*}
  [MeasurableSpace X]

private lemma l2_pairing_toLp
    {μ : Measure X} (A : Lp ℝ 2 μ) {b : X → ℝ} (hb : MemLp b 2 μ) :
    inner ℝ A (hb.toLp b) = ∫ x, A x * b x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx]
  exact mul_comm _ _

private lemma l2_toLp_norm_sq
    {μ : Measure X} {a : X → ℝ} (ha : MemLp a 2 μ) :
    ‖ha.toLp a‖ ^ 2 = ∫ x, a x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, l2_pairing_toLp]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp] with x hx
  rw [hx, pow_two]

end MeasurableSpace

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]

private lemma translated_memLp {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (w : E) :
    MemLp (fun x => f (x - w)) 2 (volume : Measure E) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hf.comp_measurePreserving (measurePreserving_add_right volume (-w))

private lemma quotient_pairing_tendsto {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (v : E)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Tendsto
      (fun t : ℝ => ∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x)
      (𝓝[≠] 0) (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
  let F : ℝ → ℝ := fun t =>
    convolution (fun y => f (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)
  have hi : LocallyIntegrable (fun y => f (-y)) (volume : Measure E) :=
    (hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).locallyIntegrable
      (by norm_num)
  have hF (t : ℝ) : F t = ∫ x, f (x - t • v) * ψ x := by
    have h := integral_sub_left_eq_self
      (fun y => f (-y) * ψ (t • v - y)) (volume : Measure E) (t • v)
    simpa only [F, convolution_def, ContinuousLinearMap.mul_apply',
      neg_sub, sub_sub_cancel] using h.symm
  have hd : HasDerivAt F (∫ x, f x * fderiv ℝ ψ x v) 0 := by
    have h :=
      (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        hi hψ (0 • v)).comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simp only [one_smul, zero_smul] at h
    apply h.congr_deriv
    calc
      _ = convolution (fun y => f (-y)) (fun x => fderiv ℝ ψ x v)
          (ContinuousLinearMap.mul ℝ ℝ) volume 0 :=
        convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hi
          (hψc.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) 0 v
      _ = ∫ x, f x * fderiv ℝ ψ x v := by
        simpa only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub] using
          integral_neg_eq_self (fun x => f x * fderiv ℝ ψ x v) volume
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have heq (t : ℝ) :
      (∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x) =
        t⁻¹ * (F t - F 0) := by
    have i₁ : Integrable (fun x => f (x - t • v) * ψ x)
        (volume : Measure E) :=
      (translated_memLp hf (t • v)).integrable_mul hp
    have i₀ : Integrable (fun x => f x * ψ x) (volume : Measure E) :=
      hf.integrable_mul hp
    rw [hF t, hF 0]
    simp only [zero_smul, sub_zero]
    calc
      _ = ∫ x, t⁻¹ * (f (x - t • v) * ψ x - f x * ψ x) := by
        apply integral_congr_ae
        exact .of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_const_mul, integral_sub i₁ i₀]
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at ht
  exact ht.congr' (.of_forall fun t => (heq t).symm)

/-- **Difference-quotient criterion for a weak derivative in `L²`** (Nirenberg; Evans PDE §5.8.2 Thm
3(ii)): if `f ∈ L²` and `∫ (f(x + t v) − f(x))² ≤ C t²` for all small `t ≠ 0`, then `f` has a weak
derivative along `v` that lies in `L²`. -/
theorem exists_hasWeakDerivAlong_of_sq_difference_le
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (v : E) {C : ℝ}
    (hdiff : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ∫ x, (f (x + t • v) - f x) ^ 2 ∂(volume : Measure E) ≤ C * t ^ 2) :
    ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧ MemLp g 2 (volume : Measure E) := by
  have hC : 0 ≤ C := by
    have h := hdiff 1 one_ne_zero (by norm_num)
    have hn : 0 ≤ ∫ x, (f (x + (1 : ℝ) • v) - f x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    norm_num only [one_pow, mul_one] at h
    exact hn.trans h
  let Q : ℝ → E → ℝ := fun t x => t⁻¹ * (f (x - t • v) - f x)
  have hQ (t : ℝ) : MemLp (Q t) 2 (volume : Measure E) :=
    ((translated_memLp hf (t • v)).sub hf).const_mul t⁻¹
  let A : ℝ → Lp ℝ 2 (volume : Measure E) := fun t => (hQ t).toLp (Q t)
  have hbound (t : ℝ) (ht : t ≠ 0) (ht1 : |t| ≤ 1) :
      ‖A t‖ ≤ Real.sqrt C := by
    apply (Real.le_sqrt (norm_nonneg _) hC).2
    have hdiff' :
        (∫ x, (f (x - t • v) - f x) ^ 2) ≤ C * t ^ 2 := by
      simpa only [neg_smul, sub_eq_add_neg, neg_sq] using
        hdiff (-t) (neg_ne_zero.mpr ht) (by simpa only [abs_neg] using ht1)
    calc
      ‖A t‖ ^ 2 = ∫ x, (Q t x) ^ 2 := l2_toLp_norm_sq (hQ t)
      _ = t⁻¹ ^ 2 * ∫ x, (f (x - t • v) - f x) ^ 2 := by
        simp only [Q, mul_pow, integral_const_mul]
      _ ≤ t⁻¹ ^ 2 * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff' (sq_nonneg _)
      _ = C := by field_simp
  let W : ℝ → WeakDual ℝ (Lp ℝ 2 (volume : Measure E)) := fun t =>
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (A t)).toWeakDual
  have hevent :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        W t ∈ WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E)))
            (Real.sqrt C) := by
    filter_upwards [eventually_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)]
      with t ht ht1
    have ht0 : t ≠ 0 := ht
    have ht2 : |t| ≤ 1 := by
      exact (show |t| < 1 from by
        simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht1).le
    change dist (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (A t)) 0
      ≤ Real.sqrt C
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hbound t ht0 ht2
  obtain ⟨L, _, hL⟩ :=
    (WeakDual.isCompact_closedBall
      (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E))) (Real.sqrt C)).exists_mapClusterPt
      (u := W) (f := 𝓝[≠] (0 : ℝ)) (le_principal_iff.mpr hevent)
  let G : Lp ℝ 2 (volume : Measure E) :=
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E))).symm L.toStrongDual
  have hg : MemLp (fun x => -(G x)) 2 (volume : Measure E) := (Lp.memLp G).neg
  refine ⟨fun x => -(G x), ⟨hf.locallyIntegrable (by norm_num),
    hg.locallyIntegrable (by norm_num), ?_⟩, hg⟩
  intro ψ hψ hψc
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  let P : Lp ℝ 2 (volume : Measure E) := hp.toLp ψ
  have heq (t : ℝ) : W t P = ∫ x, Q t x * ψ x := by
    change inner ℝ (A t) P = _
    rw [l2_pairing_toLp]
    apply integral_congr_ae
    filter_upwards [(hQ t).coeFn_toLp] with x hx
    rw [hx]
  have ht : Tendsto (fun t => W t P) (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
    exact (quotient_pairing_tendsto hf v hψ hψc).congr'
      (.of_forall fun t => (heq t).symm)
  have hc : MapClusterPt (L P) (𝓝[≠] (0 : ℝ)) (fun t => W t P) :=
    MapClusterPt.continuousAt_comp (WeakDual.eval_continuous P).continuousAt hL
  have hvalue : L P = ∫ x, f x * fderiv ℝ ψ x v :=
    eq_of_nhds_neBot (hc.clusterPt.mono ht).neBot
  have hrepr : (∫ x, G x * ψ x) = L P := by
    rw [← l2_pairing_toLp G hp]
    exact InnerProductSpace.toDual_symm_apply
  calc
    (∫ x, f x * fderiv ℝ ψ x v) = ∫ x, G x * ψ x :=
      hvalue.symm.trans hrepr.symm
    _ = -(∫ x, (-(G x)) * ψ x) := by
      simp only [neg_mul, integral_neg, neg_neg]

end FiniteDimensional

end FunctionalInequalities.Analysis

end WeakDerivativeOfDifferenceBound

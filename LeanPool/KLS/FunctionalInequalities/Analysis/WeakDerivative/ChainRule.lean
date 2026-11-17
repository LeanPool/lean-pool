/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Approximation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Profile

/-! # Weak chain rules for bounded compositions and Lipschitz exponents

Weak chain rules for scalar functions with coordinate weak derivatives.

* `hasWeakDerivAlong_exp_neg_of_lipschitz`: `e^{-F}` for globally Lipschitz `F` on a
  finite-dimensional inner product space, with chain density in `L²` on compact sets.
* `hasWeakDerivAlong_comp_of_compact_bounded`: `Φ ∘ η` for `C¹` Lipschitz `Φ` with `Φ 0 = 0` and
  bounded compactly supported `η` with compactly supported, globally `L²` weak derivatives; the
  shifted logarithm `log (δ + η) - log δ` and shifted real powers `(δ + η)^q - δ^q` of such data.
* `hasWeakDerivAlong_comp_of_bounded`: `Φ ∘ η` for bounded `η` with `L²_loc` weak derivatives
  (no compact support, no `Φ 0 = 0`); the shifted logarithm `log (δ + max w 0)` for `w ≥ 0` a.e.,
  and a bounded weak extension of it agreeing a.e. on every set where `w ≥ 0`
  (`exists_bounded_weak_log_extension`).

Supporting weak calculus for Letwin arXiv:2607.24164v1 and the
local elliptic estimates of Gilbarg--Trudinger (2001). Each declaration
retains its own support, integrability and dimensional hypotheses.
-/

@[expose] public section

section
open MeasureTheory
open scoped ContDiff

section WeakNegativeExponential
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

section StructuredSpace

variable {E : Type*}
  [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

end NormedSpace

end StructuredSpace

universe u

/-- A globally Lipschitz exponent has a local weak negative exponential
with its explicit chain density in L2 on compact sets. No bound on the
exponent or its exponential, and no C1 regularity of F, is assumed. -/
theorem hasWeakDerivAlong_exp_neg_of_lipschitz {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F) (v : E) :
    HasWeakDerivAlong (fun x => Real.exp (-F x))
      (fun x => -Real.exp (-F x) * fderiv ℝ F x v) v ∧
    ∀ S : Set E, IsCompact S →
      MemLp (fun x => -Real.exp (-F x) * fderiv ℝ F x v) 2
        ((volume : Measure E).restrict S) := by
  have hexp : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.continuous.neg
  have hweakF := hasWeakDerivAlong_of_lipschitz hF v
  have hchain :
      ∀ᵐ x : E ∂(volume : Measure E),
        fderiv ℝ (fun y => Real.exp (-F y)) x v =
          -Real.exp (-F x) * fderiv ℝ F x v := by
    filter_upwards [hF.ae_differentiableAt] with x hx
    have hd :
        fderiv ℝ (fun y => Real.exp (-F y)) x =
          Real.exp (-F x) • (-fderiv ℝ F x) :=
      hx.hasFDerivAt.neg.exp.fderiv
    rw [hd]
    change Real.exp (-F x) * (-(fderiv ℝ F x v)) =
      -Real.exp (-F x) * fderiv ℝ F x v
    ring
  constructor
  · refine ⟨hexp.locallyIntegrable,
      LocallyIntegrable.continuous_mul hexp.neg hweakF.2.1, ?_⟩
    intro ψ hψ hψc
    obtain ⟨χ, hχ, hχc, hχone⟩ :=
      exists_compact_contDiff_eq_one_near (hψc.isCompact.image hF.continuous)
    let q : ℝ → ℝ := fun t => χ t * Real.exp (-t)
    have hq : ContDiff ℝ 1 q :=
      hχ.mul (contDiff_id.neg.exp)
    have hqc : HasCompactSupport q := hχc.mul_right
    obtain ⟨C, hqLip⟩ :=
      ContDiff.lipschitzWith_of_hasCompactSupport hqc hq (by simp)
    have hweakq :
        HasWeakDerivAlong (fun x => q (F x))
          (fun x => fderiv ℝ (fun y => q (F y)) x v) v :=
      hasWeakDerivAlong_of_lipschitz (hqLip.comp hF) v
    have heq : ∀ x ∈ tsupport ψ,
        (fun y => q (F y)) =ᶠ[𝓝 x] (fun y => Real.exp (-F y)) := by
      intro x hx
      have hone :=
        (hχone (F x) ⟨x, hx, rfl⟩).comp_tendsto hF.continuous.continuousAt
      filter_upwards [hone] with y hy
      change χ (F y) = 1 at hy
      change χ (F y) * Real.exp (-F y) = Real.exp (-F y)
      rw [hy, one_mul]
    have hleft :
        (∫ x, Real.exp (-F x) * fderiv ℝ ψ x v ∂(volume : Measure E)) =
          ∫ x, q (F x) * fderiv ℝ ψ x v ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).eq_of_nhds]
      · rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply, mul_zero, mul_zero]
    have hright :
        (∫ x, fderiv ℝ (fun y => q (F y)) x v * ψ x ∂(volume : Measure E)) =
          ∫ x, (-Real.exp (-F x) * fderiv ℝ F x v) * ψ x
            ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [hchain] with x hxchain
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).fderiv_eq, hxchain]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    calc
      (∫ x, Real.exp (-F x) * fderiv ℝ ψ x v ∂(volume : Measure E)) =
          ∫ x, q (F x) * fderiv ℝ ψ x v ∂(volume : Measure E) := hleft
      _ = -(∫ x, fderiv ℝ (fun y => q (F y)) x v * ψ x
          ∂(volume : Measure E)) := hweakq.2.2 ψ hψ hψc
      _ = -(∫ x, (-Real.exp (-F x) * fderiv ℝ F x v) * ψ x
          ∂(volume : Measure E)) := congrArg Neg.neg hright
  · intro S hS
    let : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hexp.continuousOn
    apply MemLp.of_bound
      (hexp.neg.measurable.mul (measurable_fderiv_apply_const ℝ F v)).aestronglyMeasurable
      (C * ((L : ℝ) * ‖v‖))
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    calc
      ‖-Real.exp (-F x) * fderiv ℝ F x v‖ =
          ‖Real.exp (-F x)‖ * ‖fderiv ℝ F x v‖ := by
        rw [norm_mul, norm_neg]
      _ ≤ ‖Real.exp (-F x)‖ * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_fderiv_apply_le_of_lipschitz hF v x) (norm_nonneg _)
      _ ≤ C * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_right (hC x hx)
          (mul_nonneg L.coe_nonneg (norm_nonneg v))


end FunctionalInequalities.Analysis
end WeakNegativeExponential

section CompactBoundedWeakChain

open MeasureTheory Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/--
A uniformly bounded, a.e. convergent multiplier sequence supported in a finite-measure set, paired
with an `L²`-convergent
sequence, has convergent integrals. -/
private theorem tendsto_integral_bounded_mul_of_l2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} (hSm : MeasurableSet S) (hSμ : μ S ≠ ⊤) {g : ℕ → X → ℝ}
    {g₀ v₀ : X → ℝ} {w : ℕ → X → ℝ} {M : ℝ} (hg : ∀ m, AEStronglyMeasurable (g m) μ)
    (hgb : ∀ m x, ‖g m x‖ ≤ M) (hgS : ∀ m, Function.support (g m) ⊆ S)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun m => g m x) Filter.atTop (nhds (g₀ x)))
    (hv₀ : MemLp v₀ 2 μ) (hw : ∀ m, MemLp (w m) 2 μ)
    (hconv : Filter.Tendsto (fun m => eLpNorm (w m - v₀) 2 μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => ∫ x, g m x * w m x ∂μ) Filter.atTop (nhds (∫ x, g₀ x * v₀ x ∂μ)) := by
  classical
  have : IsFiniteMeasure (μ.restrict S) :=
    isFiniteMeasure_restrict.mpr
      hSμ
  -- multipliers are L² with a uniform norm bound
  have hmem (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (hfb : ∀ x, ‖f x‖ ≤ M)
    (hfS : Function.support f ⊆ S) :
    MemLp f 2 μ ∧
      (eLpNorm f 2 μ).toReal ≤
        ((μ.restrict S) Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal M).toReal := by
    have hind : S.indicator f = f := Set.indicator_eq_self.mpr hfS
    have hr : MemLp f 2 (μ.restrict S) := MemLp.of_bound hf.restrict M (ae_of_all _ hfb)
    have hm : MemLp f 2 μ := by
      rw [← hind]; exact (memLp_indicator_iff_restrict hSm.nullMeasurableSet).2 hr
    refine ⟨hm, ?_⟩
    have he : eLpNorm f 2 μ = eLpNorm f 2 (μ.restrict S) := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hSm.nullMeasurableSet, hind]
    rw [he]
    refine ENNReal.toReal_mono ?_ (eLpNorm_le_of_ae_bound hf.restrict (ae_of_all _ hfb))
    refine
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
        ENNReal.ofReal_ne_top
    exact (measure_lt_top _ _).ne
  set B := ((μ.restrict S) Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal M).toReal
  have hpair {f z : X → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ) :
    inner ℝ (hf.toLp f) (hz.toLp z) = ∫ x, f x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hz.coeFn_toLp] with x hx hz'
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, hz']
    exact
      mul_comm _
        _
  -- the L² error term tends to zero
  have herr : Filter.Tendsto (fun m => ∫ x, g m x * (w m - v₀) x ∂μ) Filter.atTop (nhds 0) := by
    have hbound (m : ℕ) :
      ‖∫ x, g m x * (w m - v₀) x ∂μ‖ ≤ B * (eLpNorm (w m - v₀) 2 μ).toReal := by
      obtain ⟨hgm, hgB⟩ := hmem (g m) (hg m) (hgb m) (hgS m)
      have hd : MemLp (w m - v₀) 2 μ := (hw m).sub hv₀
      rw [← hpair hgm hd, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [Lp.norm_toLp, Lp.norm_toLp]
      exact mul_le_mul_of_nonneg_right hgB ENNReal.toReal_nonneg
    have ht :
      Filter.Tendsto (fun m => B * (eLpNorm (w m - v₀) 2 μ).toReal) Filter.atTop (nhds 0) := by
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
      simpa using h0.const_mul B
    exact
      squeeze_zero_norm hbound
        ht
  -- the fixed L² factor passes by dominated convergence
  have hv₀S : IntegrableOn v₀ S μ := (hv₀.restrict S).integrable one_le_two
  have hdom : Integrable (S.indicator fun x => M * ‖v₀ x‖) μ :=
    (integrable_indicator_iff hSm).2 (hv₀S.norm.const_mul M)
  have hle (f : X → ℝ) (hfb : ∀ x, ‖f x‖ ≤ M) (hfS : Function.support f ⊆ S) (x : X) :
    ‖f x * v₀ x‖ ≤ (S.indicator fun y => M * ‖v₀ y‖) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (hfb x) (norm_nonneg _)
    · have hz : f x = 0 := by
        by_contra hne
        exact hx (hfS hne)
      rw [Set.indicator_of_notMem hx, hz, zero_mul, norm_zero]
  have hmain :
    Filter.Tendsto (fun m => ∫ x, g m x * v₀ x ∂μ) Filter.atTop (nhds (∫ x, g₀ x * v₀ x ∂μ)) := by
    refine
      tendsto_integral_of_dominated_convergence (S.indicator fun x => M * ‖v₀ x‖)
        (fun m => (hg m).mul hv₀.aestronglyMeasurable) hdom
        (fun m => ae_of_all _ (hle (g m) (hgb m) (hgS m))) ?_
    filter_upwards [hlim] with x hx
    exact hx.mul tendsto_const_nhds
  have hsplit (m : ℕ) :
    ∫ x, g m x * w m x ∂μ = ∫ x, g m x * (w m - v₀) x ∂μ + ∫ x, g m x * v₀ x ∂μ := by
    obtain ⟨hgm, -⟩ := hmem (g m) (hg m) (hgb m) (hgS m)
    have h1 : Integrable (fun x => g m x * (w m - v₀) x) μ :=
      hgm.integrable_mul ((hw m).sub hv₀)
    have h2 : Integrable (fun x => g m x * v₀ x) μ := hgm.integrable_mul hv₀
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.sub_apply]
    ring
  simp_rw [hsplit]
  simpa using herr.add hmain

/--
**Weak chain rule for bounded compactly supported weak data**: if `η` is bounded, compactly
supported and locally
integrable with coordinate weak derivatives `aᵢ` that are compactly supported and globally L², and
`Φ` is C1, Lipschitz with
`Φ 0 = 0`, then `Φ ∘ η` is compactly supported with weak derivatives `Φ'(η) aᵢ`, compactly supported
and globally L².
Every finite dimension. -/
theorem hasWeakDerivAlong_comp_of_compact_bounded {n : ℕ} {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) {Φ : ℝ → ℝ}
    {D : NNReal} (hΦ : ContDiff ℝ 1 Φ) (hΦLip : LipschitzWith D Φ) (hΦzero : Φ 0 = 0) :
    HasCompactSupport (fun x => Φ (η x)) ∧
      ∀ i : Fin n,
        HasWeakDerivAlong (fun x => Φ (η x)) (fun x => deriv Φ (η x) * a i x)
            (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
          HasCompactSupport (fun x => deriv Φ (η x) * a i x) ∧
            MemLp (fun x => deriv Φ (η x) * a i x) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hηm : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hη.aestronglyMeasurable
  have hΦc : Continuous Φ := hΦ.continuous
  have hdΦc : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
  have hdΦb (y : ℝ) : ‖deriv Φ y‖ ≤ D := norm_deriv_le_of_lipschitz hΦLip
  have hΦb (y : ℝ) : ‖Φ y‖ ≤ D * ‖y‖ := by
    have h := hΦLip.dist_le_mul y 0
    simpa only [hΦzero, dist_zero_right, Real.dist_eq, sub_zero] using h
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have hΦη_supp : Function.support (fun x => Φ (η x)) ⊆ Function.support η := by
    intro x hx
    by_contra h
    exact hx (by simp only [Function.notMem_support.mp h, hΦzero])
  have hcomp_c : HasCompactSupport (fun x => Φ (η x)) := hηc.comp_left hΦzero
  have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1
      (hη.integrableOn_isCompact hηc.isCompact)
  have hΦηm :
    AEStronglyMeasurable (fun x => Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hΦc.comp_aestronglyMeasurable hηm
  have hΦηint : Integrable (fun x => Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hηint.norm.const_mul D).mono' hΦηm (ae_of_all _ fun x => hΦb (η x))
  have hdΦηm :
    AEStronglyMeasurable (fun x => deriv Φ (η x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hdΦc.comp_aestronglyMeasurable hηm
  have hdmem (i : Fin n) :
    MemLp (fun x => deriv Φ (η x) * a i x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (ha2 i).of_le_mul (hdΦηm.mul (ha2 i).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul];
        exact mul_le_mul_of_nonneg_right (hdΦb _) (norm_nonneg _))
  obtain ⟨S, hS, hηS, haS, θ, hθ, hconv, hAE⟩ :=
    exists_contDiff_compact_bounded_all_weak_deriv_approximation hη hbound hηc hweak hac ha2
  refine
    ⟨hcomp_c, fun i =>
      ⟨⟨hΦηint.locallyIntegrable, (hdmem i).locallyIntegrable one_le_two, ?_⟩, (hac i).mul_left,
        hdmem i⟩⟩
  intro ψ hψ hψc
  beta_reduce
  set e := EuclideanSpace.basisFun (Fin n) ℝ i
  have hθ1 (m : ℕ) : ContDiff ℝ 1 (θ m) :=
    (hθ m).1.of_le
      (WithTop.coe_le_coe.mpr le_top)
  -- classical chain rule identity for each smooth approximant
  have hderiv (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => Φ (θ m y)) x e = deriv Φ (θ m x) * fderiv ℝ (θ m) x e := by
    have h :=
      ((hΦ.differentiable one_ne_zero (θ m x)).hasDerivAt.comp_hasFDerivAt x
        ((hθ1 m).differentiable one_ne_zero x).hasFDerivAt)
    rw [show (fun y => Φ (θ m y)) = Φ ∘ θ m from rfl, h.fderiv]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hid (m : ℕ) :
    (∫ x, Φ (θ m x) * fderiv ℝ ψ x e) = -∫ x, (deriv Φ (θ m x) * fderiv ℝ (θ m) x e) * ψ x := by
    have h := (hasWeakDerivAlong_of_contDiff (hΦ.comp (hθ1 m)) e).2.2 ψ hψ hψc
    simpa only [Function.comp_def, hderiv] using h
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hdψc : Continuous (fun x => fderiv ℝ ψ x e) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψmem :
    MemLp (fun x => fderiv ℝ ψ x e) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hdψc.memLp_of_hasCompactSupport (hψc.fderiv_apply ℝ e)
  have hSm := hS.measurableSet
  have hSμ : (volume : Measure (EuclideanSpace ℝ (Fin n))) S ≠ ⊤ :=
    hS.measure_lt_top.ne
  -- left side
  have hleft :
    Filter.Tendsto (fun m => ∫ x, Φ (θ m x) * fderiv ℝ ψ x e) Filter.atTop
      (nhds (∫ x, Φ (η x) * fderiv ℝ ψ x e)) := by
    refine
      tendsto_integral_bounded_mul_of_l2 hSm hSμ (M := D * (3 * C))
        (fun m => (hΦc.comp (hθ m).1.continuous).aestronglyMeasurable)
        (fun m x => (hΦb _).trans (mul_le_mul_of_nonneg_left ((hθ m).2.2.2.1 x) D.2))
        (fun m => fun x hx => (hθ m).2.2.1 (fun h => hx (by simp only [h, hΦzero]))) ?_ hdψmem
        (fun _ => hdψmem) (by simp)
    filter_upwards [hAE] with x hx
    exact
      (hΦc.tendsto _).comp
        hx
  -- right side, with the multiplier cut off to `S`
  have hright :
    Filter.Tendsto (fun m => ∫ x, (deriv Φ (θ m x) * fderiv ℝ (θ m) x e) * ψ x) Filter.atTop
      (nhds (∫ x, (deriv Φ (η x) * a i x) * ψ x)) := by
    have hcut (m : ℕ) :
      (fun x => (deriv Φ (θ m x) * fderiv ℝ (θ m) x e) * ψ x) = fun x =>
        S.indicator (fun y => deriv Φ (θ m y) * ψ y) x * fderiv ℝ (θ m) x e := by
      funext x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; ring
      · have hz : fderiv ℝ (θ m) x e = 0 := by
          by_contra hne
          exact hx (((hθ m).2.2.2.2 i).1 hne)
        rw [hz]; simp
    have hcut₀ :
      (fun x => (deriv Φ (η x) * a i x) * ψ x) = fun x =>
        S.indicator (fun y => deriv Φ (η y) * ψ y) x * a i x := by
      funext x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; ring
      · have hz : a i x = 0 := by
          by_contra hne
          exact hx (haS i hne)
        rw [hz]; simp
    simp_rw [hcut, hcut₀]
    have hMb (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      ‖S.indicator (fun y => deriv Φ (f y) * ψ y) x‖ ≤ D * Cψ := by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, norm_mul]
        exact mul_le_mul (hdΦb _) (hCψ x) (norm_nonneg _) D.2
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact mul_nonneg D.2 ((norm_nonneg _).trans (hCψ x))
    refine
      tendsto_integral_bounded_mul_of_l2 hSm hSμ (M := D * Cψ)
        (fun m =>
          (((hdΦc.comp (hθ m).1.continuous).mul hψ.continuous).aestronglyMeasurable).indicator
            hSm)
        (fun m x => hMb (θ m) x) (fun m => Set.support_indicator_subset) ?_ (ha2 i)
        (fun m => ((hθ m).2.2.2.2 i).2) (hconv i)
    filter_upwards [hAE] with x hx
    by_cases hxS : x ∈ S
    · simp only [Set.indicator_of_mem hxS]
      exact ((hdΦc.tendsto _).comp hx).mul tendsto_const_nhds
    · simp only [Set.indicator_of_notMem hxS]
      exact tendsto_const_nhds
  have hlim := hright.neg
  simp_rw [← hid] at hlim
  exact tendsto_nhds_unique hleft hlim

/--
**Weak shifted logarithm** of a bounded compactly supported weak test `η ≥ 0` a.e. (`δ > 0`):
`log(δ + η) - log δ` is compactly supported with weak derivatives `(δ + η)⁻¹ aᵢ`, compactly
supported and globally L². -/
theorem hasWeakDerivAlong_log_shift_of_ae_nonneg_compact_bounded {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ η x) (hδ : 0 < δ) :
    HasCompactSupport (fun x => Real.log (δ + η x) - Real.log δ) ∧
      ∀ i : Fin n,
        HasWeakDerivAlong (fun x => Real.log (δ + η x) - Real.log δ)
            (fun x => (δ + η x)⁻¹ * a i x) (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
          HasCompactSupport (fun x => (δ + η x)⁻¹ * a i x) ∧
            MemLp (fun x => (δ + η x)⁻¹ * a i x) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨Φ, D, hΦ, -, hLip, hzero, he⟩ :=
    exists_smooth_compact_log_shift_extension hδ (le_max_right C 0)
  have hchain :=
    hasWeakDerivAlong_comp_of_compact_bounded (Φ := Φ) (D := D) hη hbound hηc hweak hac ha2
      (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip hzero
  have hrange :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), η x ∈ Icc (0 : ℝ) (max C 0) := by
    filter_upwards [hnonneg] with x hx
    refine ⟨hx, ?_⟩
    exact
      (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hbound x)).trans
        (le_max_left C 0)
  have hval :
    (fun x => Φ (η x)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.log (δ + η x) - Real.log δ) := by
    filter_upwards [hrange] with x hx
    exact (he (η x) hx).1
  refine ⟨hηc.comp_left (g := fun t : ℝ => Real.log (δ + t) - Real.log δ) (by simp), ?_⟩
  intro i
  have hd :
    (fun x => deriv Φ (η x) * a i x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (δ + η x)⁻¹ * a i x) := by
    filter_upwards [hrange] with x hx
    rw [(he (η x) hx).2]
  exact ⟨(hchain.2 i).1.congr_ae hval hd, (hac i).mul_left, MemLp.ae_eq hd ((hchain.2 i).2.2)⟩

/--
**Weak shifted real power** of a bounded compactly supported weak test `η ≥ 0` a.e. (`δ > 0`, every
real `q`):
`(δ + η)^q - δ^q` is compactly supported with weak derivatives `q (δ + η)^(q - 1) aᵢ`, compactly
supported and
globally L². -/
theorem hasWeakDerivAlong_rpow_shift_of_ae_nonneg_compact_bounded {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ η x) (hδ : 0 < δ)
    (q : ℝ) :
    HasCompactSupport (fun x => (δ + η x) ^ q - δ ^ q) ∧
      ∀ i : Fin n,
        HasWeakDerivAlong (fun x => (δ + η x) ^ q - δ ^ q)
            (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
          HasCompactSupport (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) ∧
            MemLp (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨Φ, D, hΦ, -, hLip, hzero, he⟩ :=
    exists_smooth_compact_rpow_shift_extension hδ (le_max_right C 0) q
  have hchain :=
    hasWeakDerivAlong_comp_of_compact_bounded (Φ := Φ) (D := D) hη hbound hηc hweak hac ha2
      (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip hzero
  have hrange :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), η x ∈ Icc (0 : ℝ) (max C 0) := by
    filter_upwards [hnonneg] with x hx
    refine ⟨hx, ?_⟩
    exact
      (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hbound x)).trans
        (le_max_left C 0)
  have hval :
    (fun x => Φ (η x)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (δ + η x) ^ q - δ ^ q) := by
    filter_upwards [hrange] with x hx
    exact (he (η x) hx).1
  refine ⟨hηc.comp_left (g := fun t : ℝ => (δ + t) ^ q - δ ^ q) (by simp), ?_⟩
  intro i
  have hd :
    (fun x => deriv Φ (η x) * a i x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) := by
    filter_upwards [hrange] with x hx
    rw [(he (η x) hx).2]
  exact ⟨(hchain.2 i).1.congr_ae hval hd, (hac i).mul_left, MemLp.ae_eq hd ((hchain.2 i).2.2)⟩

end FunctionalInequalities.Analysis

end CompactBoundedWeakChain

section BoundedNoncompactWeakChain

open MeasureTheory Set Filter
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-! Bounded weak `H¹_loc` data WITHOUT compact support: the chain rule for globally Lipschitz `C¹`
profiles and the actual
shifted logarithm `log (δ + max w 0)`, the inputs of the logarithmic energy in Gilbarg–Trudinger
(2001) (8.48)–(8.49). -/

/--
**Bounded noncompact weak chain rule.** For bounded `η` with coordinate weak derivatives `a i` in
`L²_loc` (no compact
support, no global `L²`) and `Φ` of class `C¹` and `D`-Lipschitz (no `Φ 0 = 0`), `Φ ∘ η` is locally
integrable, bounded by
`D C + |Φ 0|`, with exact weak derivatives `Φ′(η) a i` in `L²_loc`. Every dimension, zero included.
Each test is handled by
an outer bump equal to one near its support, the compact chain rule for `Φ − Φ 0`, and the affine
rule. -/
theorem hasWeakDerivAlong_comp_of_bounded {n : ℕ} {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {Φ : ℝ → ℝ} {D : NNReal} (hΦ : ContDiff ℝ 1 Φ) (hLip : LipschitzWith D Φ) :
    LocallyIntegrable (fun x => Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖Φ (η x)‖ ≤ B) ∧
        ∀ i : Fin n,
          HasWeakDerivAlong (fun x => Φ (η x)) (fun x => deriv Φ (η x) * a i x)
              (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => deriv Φ (η x) * a i x) 2
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  have hfm : AEStronglyMeasurable (fun x => Φ (η x)) volume :=
    hΦ.continuous.comp_aestronglyMeasurable hη.aestronglyMeasurable
  have hdfm : AEStronglyMeasurable (fun x => deriv Φ (η x)) volume :=
    (hΦ.continuous_deriv le_rfl).comp_aestronglyMeasurable hη.aestronglyMeasurable
  have hd (t : ℝ) : ‖deriv Φ t‖ ≤ D := norm_deriv_le_of_lipschitz hLip
  have hfb (x : EuclideanSpace ℝ (Fin n)) : ‖Φ (η x)‖ ≤ D * C + ‖Φ 0‖ := by
    have h : ‖Φ (η x) - Φ 0‖ ≤ D * ‖η x‖ := by
      simpa only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] using
        hLip.dist_le_mul (η x) 0
    calc
      ‖Φ (η x)‖ ≤ ‖Φ (η x) - Φ 0‖ + ‖Φ 0‖ := norm_le_norm_sub_add _ _
      _ ≤ D * C + ‖Φ 0‖ := by
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_left (hbound x) D.2)
  have hfloc : LocallyIntegrable (fun x => Φ (η x)) volume := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (memLp_top_of_bound hfm.restrict (D * C + ‖Φ 0‖) (ae_of_all _ hfb)).integrable le_top
  have hdm (i : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => deriv Φ (η x) * a i x) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    (ha2 i S hS).of_le_mul (hdfm.restrict.mul (ha2 i S hS).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul];
        exact mul_le_mul_of_nonneg_right (hd _) (norm_nonneg _))
  refine ⟨hfloc, ⟨D * C + ‖Φ 0‖, by positivity, hfb⟩, fun i => ⟨?_, hdm i⟩⟩
  refine ⟨hfloc, ?_, ?_⟩
  · apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hdm i S hS).integrable one_le_two
  · intro ψ hψ hψc
    obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall 0
    let R := max r 0
    let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
      ⟨R + 1, R + 2, by positivity, by linarith⟩
    have hχ : ContDiff ℝ 1 (fun x => χ x) := χ.contDiff
    have hone (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ χ x = 0 := by
      have hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) χ.rIn := by
        have h := hr hx
        simp only [Metric.mem_closedBall, dist_zero_right] at h
        simp only [Metric.mem_ball, dist_zero_right]
        change ‖x‖ < R + 1
        linarith [le_max_left r 0]
      have he := χ.eventuallyEq_one_of_mem_ball hball
      refine ⟨he.eq_of_nhds, ?_⟩
      rw [he.fderiv_eq]
      exact fderiv_const_apply _
    have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport ψ) :
      ψ x = 0 ∧ fderiv ℝ ψ x = 0 := by
      have he := notMem_tsupport_iff_eventuallyEq.mp hx
      refine ⟨he.eq_of_nhds, ?_⟩
      rw [he.fderiv_eq]
      exact fderiv_const_apply _
    have hηtop : MemLp η (⊤ : ENNReal) volume :=
      memLp_top_of_bound hη.aestronglyMeasurable C (ae_of_all _ hbound)
    let b := fun x => χ x * η x
    let db := fun (k : Fin n) x =>
      χ x * a k x + fderiv ℝ (fun y => χ y) x (EuclideanSpace.basisFun (Fin n) ℝ k) * η x
    have hb : LocallyIntegrable b volume := LocallyIntegrable.continuous_mul χ.continuous hη
    have hbb (x : EuclideanSpace ℝ (Fin n)) : ‖b x‖ ≤ C := by
      simp only [b, norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      exact
        (mul_le_mul_of_nonneg_left (hbound x) χ.nonneg).trans
          (mul_le_of_le_one_left hC χ.le_one)
    have hdata (k : Fin n) :=
      (hweak k).compact_mul_data (ha2 k) (fun S _ => hηtop.restrict S) hχ χ.hasCompactSupport
    let Θ := fun t : ℝ => Φ t - Φ 0
    have hΘ : ContDiff ℝ 1 Θ := hΦ.sub contDiff_const
    have hΘLip : LipschitzWith D Θ :=
      LipschitzWith.of_dist_le_mul fun x y => by
        simpa only [Θ, dist_sub_right] using hLip.dist_le_mul x y
    have hΘ0 : Θ 0 = 0 := sub_self _
    have hderiv (t : ℝ) : deriv Θ t = deriv Φ t := deriv_sub_const _
    have hchain :=
      hasWeakDerivAlong_comp_of_compact_bounded hb hbb χ.hasCompactSupport.mul_right
        (fun k => (hdata k).1) (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2) hΘ hΘLip
        hΘ0
    have hΦb :
      HasWeakDerivAlong (fun x => Φ (b x)) (fun x => deriv Φ (b x) * db i x)
        (EuclideanSpace.basisFun (Fin n) ℝ i) :=
      ((hchain.2 i).1.const_add_mul (Φ 0) 1).congr_ae
        (ae_of_all _ fun x => by simp only [Θ, one_mul, add_sub_cancel])
        (ae_of_all _ fun x => by simp only [one_mul, hderiv, db])
    calc
      (∫ x, Φ (η x) * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
          ∫ x, Φ (b x) * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ tsupport ψ
        · simp only [b, (hone x hx).1, one_mul]
        · simp only [(hzero x hx).2, _root_.zero_apply, mul_zero]
      _ = -(∫ x, (deriv Φ (b x) * db i x) * ψ x) := hΦb.2.2 ψ hψ hψc
      _ = -(∫ x, (deriv Φ (η x) * a i x) * ψ x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ tsupport ψ
        · simp only [b, db, (hone x hx).1, (hone x hx).2, one_mul, _root_.zero_apply, zero_mul,
            add_zero]
        · simp only [(hzero x hx).1, mul_zero]

/--
**Actual shifted logarithm.** For bounded `w ≥ 0` a.e. with coordinate weak derivatives `a i` in
`L²_loc` (no compact
support) and `δ > 0`, `log (δ + max w 0)` is locally integrable and bounded, with exact weak
derivatives
`(δ + max w 0)⁻¹ a i` in `L²_loc`. -/
theorem hasWeakDerivAlong_log_max_shift_of_ae_nonneg_bounded {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong w (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x) (hδ : 0 < δ) :
    LocallyIntegrable (fun x => Real.log (δ + max (w x) 0))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖Real.log (δ + max (w x) 0)‖ ≤ B) ∧
        ∀ i : Fin n,
          HasWeakDerivAlong (fun x => Real.log (δ + max (w x) 0))
              (fun x => (δ + max (w x) 0)⁻¹ * a i x) (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact S →
                MemLp (fun x => (δ + max (w x) 0)⁻¹ * a i x) 2
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let wp := fun x => max (w x) 0
  have hae : w =ᵐ[volume] wp := by
    filter_upwards [hnonneg] with x hx
    exact (max_eq_left hx).symm
  have hwp := hw.congr hae
  have hwpb (x : EuclideanSpace ℝ (Fin n)) : ‖wp x‖ ≤ max C 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans ((hbound x).trans (le_max_left _ _))) (le_max_right _ _)
  have hwpweak (i : Fin n) := (hweak i).congr_ae hae (Filter.EventuallyEq.rfl)
  obtain ⟨Φ, D, hΦ, -, hLip, -, he⟩ :=
    exists_smooth_compact_log_shift_extension hδ (le_max_right C 0)
  have hchain :=
    hasWeakDerivAlong_comp_of_bounded (Φ := Φ) (D := D) hwp hwpb hwpweak ha2
      (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip
  have hrange (x : EuclideanSpace ℝ (Fin n)) : wp x ∈ Icc (0 : ℝ) (max C 0) :=
    ⟨le_max_right _ _, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hwpb x)⟩
  have hv (x : EuclideanSpace ℝ (Fin n)) : Real.log δ + Φ (wp x) = Real.log (δ + wp x) := by
    rw [(he (wp x) (hrange x)).1]
    ring
  have hd (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    deriv Φ (wp x) * a i x = (δ + wp x)⁻¹ * a i x := by rw [(he (wp x) (hrange x)).2]
  obtain ⟨B, hB, hBb⟩ := hchain.2.1
  have hloc : LocallyIntegrable (fun x => Real.log (δ + wp x)) volume :=
    (locallyIntegrable_const (Real.log δ)).add hchain.1 |>.congr (ae_of_all _ hv)
  refine ⟨hloc, ⟨‖Real.log δ‖ + B, by positivity, fun x => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [← hv]
    exact (norm_add_le _ _).trans (by gcongr; exact hBb x)
  · exact
      ((hchain.2.2 i).1.const_add_mul (Real.log δ) 1).congr_ae
        (ae_of_all _ fun x => by simpa only [one_mul] using hv x)
        (ae_of_all _ fun x => by simpa only [one_mul] using hd i x)
  · intro S hS
    exact MemLp.ae_eq (ae_of_all _ (hd i)) ((hchain.2.2 i).2 S hS)

/--
**Bounded weak extension of the shifted logarithm.** For bounded `w` with coordinate weak
derivatives `a k` in
`L²_loc` (no sign condition) and `δ > 0`, ONE bounded locally integrable `H` with weak derivatives
`dH k` in `L²_loc` is
chosen before every domain: `H = log δ + Φ ∘ w` for the compact smooth log profile `Φ` on `[0, C]`,
by the bounded
noncompact chain rule applied to `w` itself. On EVERY measurable `S` where `w ≥ 0` a.e., `H = log (δ
+ max w 0)` and
`dH k = (δ + max w 0)⁻¹ a k` a.e. for the restriction. No weak derivative of `log (δ + max w 0)`
itself is asserted. -/
theorem exists_bounded_weak_log_extension {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hδ : 0 < δ) :
    ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖H x‖ ≤ B) ∧
          (∀ k : Fin n,
              HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                ∀ S : Set (EuclideanSpace ℝ (Fin n)),
                  IsCompact S →
                    MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            ∀ S : Set (EuclideanSpace ℝ (Fin n)),
              MeasurableSet S →
                (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S), 0 ≤ w x) →
                  (H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
                      (fun x => Real.log (δ + max (w x) 0))) ∧
                    ∀ k : Fin n,
                      (dH k) =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
                        (fun x => (δ + max (w x) 0)⁻¹ * a k x) := by
  have hC : 0 ≤ C :=
    (norm_nonneg _).trans
      (hbound 0)
  -- one compact log profile on `[0, C]` and the bounded noncompact chain on the ORIGINAL `w`
  obtain ⟨Φ, D, hΦ, -, hLip, -, he⟩ := exists_smooth_compact_log_shift_extension hδ hC
  have hchain :=
    hasWeakDerivAlong_comp_of_bounded (Φ := Φ) (D := D) hw hbound hweak ha2
      (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip
  obtain ⟨B, hB, hBb⟩ := hchain.2.1
  refine
    ⟨fun x => Real.log δ + Φ (w x), fun k x => deriv Φ (w x) * a k x,
      (locallyIntegrable_const (Real.log δ)).add hchain.1,
      ⟨‖Real.log δ‖ + B, by positivity, fun x =>
        (norm_add_le _ _).trans (by gcongr; exact hBb x)⟩,
      fun k => ⟨?_, (hchain.2.2 k).2⟩, ?_⟩
  · simpa only [one_mul] using
      (hchain.2.2 k).1.const_add_mul (Real.log δ)
        1
  -- identification only on domains where `w ≥ 0` a.e.
  intro S _hS hS0
  have hrange :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
      0 ≤ w x ∧ w x ∈ Icc (0 : ℝ) C := by
    filter_upwards [hS0] with x hx
    exact ⟨hx, hx, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)⟩
  refine ⟨?_, fun k => ?_⟩
  · filter_upwards [hrange] with x hx
    rw [max_eq_left hx.1, (he (w x) hx.2).1]
    ring
  · filter_upwards [hrange] with x hx
    rw [max_eq_left hx.1, (he (w x) hx.2).2]

end FunctionalInequalities.Analysis

end BoundedNoncompactWeakChain

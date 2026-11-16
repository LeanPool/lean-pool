/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Mollification.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Mollifying functions with Lipschitz gradient

Smooth approximation of a `C¹` function with Lipschitz gradient by normalized bump convolutions,
with gradients
converging locally uniformly and Hessians converging almost everywhere (support for the weak Piola
identity and the
weak Bochner formula on the moment-map route to Letwin arXiv:2607.24164v1).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace FunctionalInequalities.Analysis

section StructuredSpace

variable {E : Type*}
  [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private lemma integrable_mul_of_compact_support
    [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace E]
    {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) :
    Integrable (fun x => f x * g x) μ := by
  apply (hf.mul hg).integrable_of_hasCompactSupport
  refine hcf.mono ?_
  intro x hx
  by_contra hfx
  have hfx' : f x = 0 := by
    simpa [Function.mem_support] using hfx
  have hzero : (f * g) x = 0 := by
    simp only [Pi.mul_apply, hfx', zero_mul]
  exact hx hzero

private lemma integrable_smul_of_compact_support
    {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) :
    Integrable (fun x => f x • g x) μ := by
  apply (hf.smul hg).integrable_of_hasCompactSupport
  refine hcf.mono ?_
  intro x hx
  by_contra hfx
  have hfx' : f x = 0 := by
    simpa [Function.mem_support] using hfx
  have hzero : f x • g x = 0 := by
    simp only [hfx', zero_smul]
  exact hx hzero

private lemma continuous_clm_apply
    {f : E → E →L[ℝ] ℝ} (hf : Continuous f) (v : E) :
    Continuous (fun x => f x v) := by
  have hev : Continuous (fun L : E →L[ℝ] ℝ => L v) := by
    fun_prop
  exact hev.comp hf

end NormedSpace

section FiniteDimensional

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma locallyIntegrable_fderiv_gradient
    {U : E → ℝ} {G : NNReal} (hG : LipschitzWith G (gradient U)) :
    LocallyIntegrable (fderiv ℝ (gradient U)) (volume : Measure E) := by
  refine
    (continuous_const.locallyIntegrable :
      LocallyIntegrable (fun _ : E => (G : ℝ)) (volume : Measure E)).mono
      (measurable_fderiv (𝕜 := ℝ) (f := gradient U)).aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa using norm_fderiv_le_of_lipschitz ℝ hG

private lemma gradient_convolution_normed {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) (φ : ContDiffBump (0 : E)) :
    gradient
        (convolution (φ.normed (volume : Measure E)) U (ContinuousLinearMap.lsmul ℝ ℝ)
          (volume : Measure E)) =
      convolution (φ.normed (volume : Measure E)) (gradient U) (ContinuousLinearMap.lsmul ℝ ℝ)
        (volume : Measure E) := by
  classical
  let f : E → ℝ := φ.normed (volume : Measure E)
  have hf1 : ContDiff ℝ 1 f := by simpa [f] using (φ.contDiff_normed (n := 1))
  have hcf : HasCompactSupport f := by simpa [f] using φ.hasCompactSupport_normed
  have hUloc : LocallyIntegrable U (volume : Measure E) := hU.continuous.locallyIntegrable
  have hfd : Continuous (fderiv ℝ f) := hf1.continuous_fderiv (by norm_num)
  have hcfderiv : HasCompactSupport (fderiv ℝ f) := hcf.fderiv ℝ
  funext x
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hd :=
    HasCompactSupport.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hcf hf1 hUloc
      x
  rw [hd.fderiv]
  let q : E → E →L[ℝ] ℝ := fun t => U (x - t) • fderiv ℝ f t
  have hqcont : Continuous q := by fun_prop
  have hqcf : HasCompactSupport q := by
    refine hcfderiv.mono ?_
    intro t ht
    by_contra hft
    have hft' : fderiv ℝ f t = 0 := by simpa [Function.mem_support] using hft
    have hzero : q t = 0 := by simp only [q, hft', smul_zero]
    exact ht hzero
  have hqint : Integrable q (volume : Measure E) := hqcont.integrable_of_hasCompactSupport hqcf
  have hgradint : Integrable (fun t : E => f t • gradient U (x - t)) (volume : Measure E) := by
    apply integrable_smul_of_compact_support
    · exact φ.continuous_normed
    · exact (LipschitzWith.continuous hG).comp (continuous_const.sub continuous_id)
    · exact hcf
  simp only [convolution_def]
  have hleft :
    (∫ t : E,
        ((ContinuousLinearMap.precompL E (ContinuousLinearMap.lsmul ℝ ℝ)) (fderiv ℝ f t))
          (U (x - t)) ∂(volume : Measure E)) =
      ∫ t : E, q t ∂(volume : Measure E) := by
    apply integral_congr_ae
    filter_upwards [] with t
    ext w
    change (fderiv ℝ f t) w * U (x - t) = U (x - t) * (fderiv ℝ f t) w
    ring
  rw [hleft]
  rw [ContinuousLinearMap.integral_apply hqint v]
  have hconvint :
    Integrable
      (fun t : E =>
        ((ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed (volume : Measure E) t))
          (gradient U (x - t)))
      (volume : Measure E) := by
    simpa [f, ContinuousLinearMap.lsmul_apply] using hgradint
  rw [real_inner_comm]
  rw [← integral_inner hconvint v]
  let g : E → ℝ := fun s => U (x - s)
  have htrans : ∀ s : E, (fderiv ℝ g s) v = -((fderiv ℝ U (x - s)) v) := by
    intro s
    have ht : HasFDerivAt (fun z : E => x - z) (-ContinuousLinearMap.id ℝ E) s := by
      convert (hasFDerivAt_const (x := s) x).sub (hasFDerivAt_id s) using 1 <;> ext z <;> simp
    have hcomp := (hU.differentiable (by norm_num) (x - s)).hasFDerivAt.comp s ht
    have hg : g = U ∘ HSub.hSub x := by
      funext z
      rfl
    rw [hg]
    simpa using congrArg (fun L => L v) hcomp.fderiv
  have h₁ : Integrable (fun s : E => (fderiv ℝ f s) v * g s) (volume : Measure E) := by
    apply integrable_mul_of_compact_support
    · exact continuous_clm_apply hfd v
    · exact hU.continuous.comp (continuous_const.sub continuous_id)
    · refine hcfderiv.mono ?_
      intro s hs
      by_contra hnot
      have hz : fderiv ℝ f s = 0 := by simpa [Function.mem_support] using hnot
      exact hs (by simp [hz])
  have h₂ : Integrable (fun s : E => f s * (fderiv ℝ g s) v) (volume : Measure E) := by
    apply integrable_mul_of_compact_support
    · exact hf1.continuous
    · have hUg : Continuous (fderiv ℝ U) := hU.continuous_fderiv (by norm_num)
      have hscalar : Continuous (fun s : E => (fderiv ℝ U (x - s)) v) :=
        continuous_clm_apply (hUg.comp (continuous_const.sub continuous_id)) v
      have hneg : Continuous (fun s : E => -((fderiv ℝ U (x - s)) v)) :=
        continuous_neg.comp hscalar
      simpa only [htrans] using hneg
    · exact hcf
  have h₃ : Integrable (fun s : E => f s * g s) (volume : Measure E) := by
    apply integrable_mul_of_compact_support
    · exact hf1.continuous
    · exact hU.continuous.comp (continuous_const.sub continuous_id)
    · exact hcf
  have hi :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
      (by
        intro s hs
        exact hf1.differentiable (by norm_num) s)
      (by
        intro s hs
        exact
          (hU.differentiable (by norm_num) (x - s)).comp s
            ((differentiableAt_const (c := x)).sub differentiableAt_id))
  have hi' :
    ∫ s : E, (fderiv ℝ f s) v * g s ∂volume = ∫ s : E, f s * (fderiv ℝ U (x - s)) v ∂volume := by
    calc
      ∫ s : E, (fderiv ℝ f s) v * g s ∂volume = -∫ s : E, f s * (fderiv ℝ g s) v ∂volume := by
        linarith
      _ = ∫ s : E, f s * (fderiv ℝ U (x - s)) v ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [htrans]
        ring
  have hleft' : ∫ t : E, q t v ∂volume = ∫ t : E, (fderiv ℝ f t) v * g t ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with t
    change U (x - t) * (fderiv ℝ f t) v = (fderiv ℝ f t) v * U (x - t)
    ring
  have hright :
    ∫ t : E, inner ℝ v (f t • gradient U (x - t)) ∂volume =
      ∫ t : E, f t * (fderiv ℝ U (x - t)) v ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [real_inner_smul_right]
    rw [real_inner_comm]
    rw [inner_gradient_left]
  calc
    ∫ t : E, q t v ∂volume = ∫ t : E, (fderiv ℝ f t) v * g t ∂volume := hleft'
    _ = ∫ t : E, f t * (fderiv ℝ U (x - t)) v ∂volume := hi'
    _ = ∫ t : E, inner ℝ v (f t • gradient U (x - t)) ∂volume := hright.symm
    _ =
        ∫ t : E,
          inner ℝ v
            (((ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed (volume : Measure E) t))
              (gradient U (x - t))) ∂volume := by
      simp [f, ContinuousLinearMap.lsmul_apply]

theorem exists_contDiff_approx_of_lipschitz_gradient
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) :
    ∃ Uk : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (Uk k)) ∧
      (∀ k x, ‖gradient (Uk k) x - gradient U x‖ ≤ G / ((k : ℝ) + 1)) ∧
      (∀ k, LipschitzWith G (gradient (Uk k))) ∧
      (∀ x, Tendsto (fun k => Uk k x) atTop (𝓝 (U x))) ∧
      (∀ᵐ x ∂(volume : Measure E), Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
        (𝓝 (fderiv ℝ (gradient U) x))) := by
  classical

  -- Choose shrinking mollifiers and define the smooth approximants.
  let φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ContDiffBump.mk
      (1 / (2 * ((k : ℝ) + 1)))
      (1 / ((k : ℝ) + 1))
      (by positivity)
      (by
        have hk : 0 < (k : ℝ) + 1 := by positivity
        apply (div_lt_div_iff₀ (by positivity) hk).2
        nlinarith)
  let Uk : ℕ → E → ℝ := fun k =>
    convolution
      ((φ k).normed (volume : Measure E)) U
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    dsimp [φ]
    have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro a
      rcases exists_nat_gt a with ⟨n, hn⟩
      filter_upwards [eventually_ge_atTop n] with k hk
      have hk' : (n : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hk
      linarith
    convert tendsto_inv_atTop_zero.comp hnat using 1
    ext k
    simp only [Function.comp_apply, one_div]
  have hφ' : ∀ᶠ k : ℕ in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := by
    filter_upwards [] with k
    dsimp [φ]
    have hk : 0 < (k : ℝ) + 1 := by positivity
    field_simp
    norm_num
  have hUloc : LocallyIntegrable U (volume : Measure E) :=
    hU.continuous.locallyIntegrable
  have hgradloc :
      LocallyIntegrable (fderiv ℝ (gradient U)) (volume : Measure E) :=
    locallyIntegrable_fderiv_gradient hG
  have hmeas : AEStronglyMeasurable (gradient U) (volume : Measure E) :=
    (LipschitzWith.continuous hG).aestronglyMeasurable

  -- Identify the mollified gradient and retain its uniform Lipschitz bound.
  have hgrad : ∀ k,
      gradient (Uk k) =
        convolution
          ((φ k).normed (volume : Measure E)) (gradient U)
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) := by
    intro k
    dsimp [Uk]
    exact gradient_convolution_normed hU hG (φ k)
  refine ⟨Uk, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [Uk]
    exact
      HasCompactSupport.contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ k).hasCompactSupport_normed
        (φ k).contDiff_normed
        hUloc
  · intro k x
    rw [hgrad k]
    have hdist :=
      ContDiffBump.dist_normed_convolution_le
        (φ := φ k) (x₀ := x) (ε := (G : ℝ) / ((k : ℝ) + 1)) hmeas
        (by
          intro y hy
          have hy' : dist y x < (φ k).rOut := hy
          have hh := hG.dist_le_mul y x
          have hG' : 0 ≤ (G : ℝ) := by positivity
          have hle :
              dist (gradient U y) (gradient U x) ≤
                (G : ℝ) / ((k : ℝ) + 1) := by
            calc
              dist (gradient U y) (gradient U x) ≤
                  (G : ℝ) * dist y x := hh
              _ ≤ (G : ℝ) * (φ k).rOut :=
                mul_le_mul_of_nonneg_left (le_of_lt hy') hG'
              _ = (G : ℝ) / ((k : ℝ) + 1) := by
                simp [φ, div_eq_mul_inv]
          exact hle)
    simpa [dist_eq_norm] using hdist
  · intro k
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hgrad k]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
    have h₁ :
        Integrable
          (fun t : E =>
            (φ k).normed (volume : Measure E) t • gradient U (x - t))
          (volume : Measure E) := by
      apply integrable_smul_of_compact_support
      · exact (φ k).continuous_normed
      · exact (LipschitzWith.continuous hG).comp
          (continuous_const.sub continuous_id)
      · exact (φ k).hasCompactSupport_normed
    have h₂ :
        Integrable
          (fun t : E =>
            (φ k).normed (volume : Measure E) t • gradient U (y - t))
          (volume : Measure E) := by
      apply integrable_smul_of_compact_support
      · exact (φ k).continuous_normed
      · exact (LipschitzWith.continuous hG).comp
          (continuous_const.sub continuous_id)
      · exact (φ k).hasCompactSupport_normed
    rw [dist_eq_norm]
    have hsub :
        (∫ t : E, (φ k).normed (volume : Measure E) t • gradient U (x - t) ∂volume) -
            ∫ t : E, (φ k).normed (volume : Measure E) t • gradient U (y - t) ∂volume =
          ∫ t : E,
            ((φ k).normed (volume : Measure E) t • gradient U (x - t)) -
              ((φ k).normed (volume : Measure E) t • gradient U (y - t)) ∂volume :=
      (integral_sub h₁ h₂).symm
    rw [hsub]

    -- Control the Hessians and assemble the approximation properties.
    have hbound :
        Integrable
          (fun t : E =>
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖))
          (volume : Measure E) := by
      apply integrable_mul_of_compact_support
      · exact (φ k).continuous_normed
      · exact continuous_const
      · exact (φ k).hasCompactSupport_normed
    have hnorm :
        ‖∫ t : E,
            ((φ k).normed (volume : Measure E) t • gradient U (x - t)) -
              ((φ k).normed (volume : Measure E) t • gradient U (y - t)) ∂volume‖ ≤
          ∫ t : E,
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) ∂volume := by
      apply norm_integral_le_of_norm_le hbound
      filter_upwards [] with t
      rw [← smul_sub, norm_smul]
      calc
        ‖(φ k).normed (volume : Measure E) t‖ *
              ‖gradient U (x - t) - gradient U (y - t)‖ ≤
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) := by
          rw [Real.norm_eq_abs, abs_of_nonneg ((φ k).nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [dist_eq_norm, sub_sub_sub_cancel_right] using
                hG.dist_le_mul (x - t) (y - t))
            ((φ k).nonneg_normed t)
        _ = (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) := rfl
    calc
      ‖∫ t : E,
          ((φ k).normed (volume : Measure E) t • gradient U (x - t)) -
            ((φ k).normed (volume : Measure E) t • gradient U (y - t)) ∂volume‖ ≤
          ∫ t : E,
            (φ k).normed (volume : Measure E) t *
              ((G : ℝ) * ‖x - y‖) ∂volume := hnorm
      _ = (G : ℝ) * dist x y := by
        have hrewrite :
            (fun t : E =>
              (φ k).normed (volume : Measure E) t *
                ((G : ℝ) * ‖x - y‖)) =
            (fun t : E =>
              ((G : ℝ) * ‖x - y‖) •
                (φ k).normed (volume : Measure E) t) := by
          funext t
          simp only [smul_eq_mul]
          ring
        rw [hrewrite, integral_smul]
        simp [dist_eq_norm, (φ k).integral_normed]
  · intro x
    have hcg :
        Tendsto
          (Function.uncurry (fun _ : ℕ => U))
          (atTop ×ˢ 𝓝 x) (𝓝 (U x)) := by
      change Tendsto (fun p : ℕ × E => U p.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (U x))
      exact (hU.continuous.tendsto x).comp
        (tendsto_snd : Tendsto Prod.snd (atTop ×ˢ 𝓝 x) (𝓝 x))
    simpa [Uk] using
      ContDiffBump.convolution_tendsto_right
        (φ := φ) (g := fun _ : ℕ => U) (k := fun _ : ℕ => x)
        (x₀ := x) (z₀ := U x) hφ
        (by
          filter_upwards [] with k
          exact hU.continuous.aestronglyMeasurable)
        hcg tendsto_const_nhds
  · have hconv :
        ∀ k x,
          fderiv ℝ (gradient (Uk k)) x =
            convolution
              ((φ k).normed (volume : Measure E)) (fderiv ℝ (gradient U))
              (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) x := by
      intro k x
      rw [hgrad k]
      simpa using
        (hasFDerivAt_convolution_normed_of_lipschitz
          hG (φ k) x).fderiv
    filter_upwards [
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (φ := φ) (l := atTop) (K := 2) hφ hφ' hgradloc] with x hx
    simpa [hconv] using hx

end FiniteDimensional

end StructuredSpace

end FunctionalInequalities.Analysis

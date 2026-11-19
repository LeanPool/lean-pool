/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.Implicit

/-!
# Integration against the surface measure of a `C¹` graph

The codimension-one area formula of `Analysis/Graph/Area.lean` is an identity of *measures of
sets*: `ℋ^k (Ψ '' s) = ∫_s √(1 + ‖∇g‖²)` for every measurable parameter set `s`.  That is not by
itself a change of variables for an arbitrary integrand.  This module supplies the minimal
interface the boundary flux needs, and nothing more: it is not a general area or manifold
integration library.

`map_graphChartMap_withDensity` upgrades the area formula to the identity of measures

  `map Ψ ((volume.withDensity √(1 + ‖∇g‖²)).restrict s) = ℋ^k ⌊ (Ψ '' s)`,

using injectivity of the graph parametrization (`graphChartMap_injective_of_perp`) and
measurability of its image (`measurableSet_image_graphChartMap`).  From it,
`setLIntegral_image_graphChartMap` and `setIntegral_image_graphChartMap` state the change of
variables for a nonnegative measurable integrand and for an almost everywhere strongly measurable
Banach-valued integrand:

  `∫_{Ψ '' s} f dℋ^k = ∫_s √(1 + ‖∇g y‖²) • f (Ψ y) dy`.

No integrability hypothesis appears: `integral_map` and `integral_withDensity_eq_integral_smul`
hold verbatim, both sides being zero when the integrand is not integrable.  Combined with the
normal formula `ν (Ψ y) = (ι (-∇g y) + e)/√(1 + ‖∇g y‖²)` of a boundary chart, the Jacobian
`√(1 + ‖∇g y‖²)` cancels exactly against the denominator of the unit normal; that cancellation is
carried out in `Analysis/SmoothDomain/LocalGaussGreen.lean`.

Every statement here is proved and uses only the standard axioms; the module contains no hole.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

universe u v

section GraphIntegral

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The image of a measurable parameter set under the translated graph parametrization is
measurable. -/
theorem measurableSet_image_graphChartMap (ι : H →ₗᵢ[ℝ] V) {e : V}
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (x₀ : V) {g : H → ℝ} (hg : Continuous g)
    {s : Set H} (hs : MeasurableSet s) :
    MeasurableSet (graphChartMap ι e x₀ g '' s) := by
  have himg : graphChartMap ι e x₀ g '' s = (fun x : V => x - x₀) ⁻¹' (graphMap ι e g '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      change graphMap ι e g y = graphChartMap ι e x₀ g y - x₀
      rw [graphChartMap]; abel
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      have : graphMap ι e g y = x - x₀ := hxy
      rw [graphChartMap, this]; abel
  rw [himg]
  exact (measurableSet_image_graphMap ι hperp hg hs).preimage
    (measurable_id.sub measurable_const)

/-- **The graph parametrization pushes the Jacobian-weighted Lebesgue measure to the surface
measure.**  This upgrades the codimension-one area formula, which is an identity of *measures of
sets*, into an identity of measures that can be used as a change of variables for arbitrary
integrands. -/
theorem map_graphChartMap_withDensity (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (x₀ : V) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) :
    Measure.map (graphChartMap ι e x₀ g)
        (((volume : Measure H).withDensity
            fun y => ENNReal.ofReal (graphJacobian (gradient g y))).restrict s)
      = (KLS.hausdorffNormalized V (Module.finrank ℝ H)).restrict
          (graphChartMap ι e x₀ g '' s) := by
  set Ψ : H → V := graphChartMap ι e x₀ g with hΨ
  set μ : Measure H := (volume : Measure H).withDensity
    fun y => ENNReal.ofReal (graphJacobian (gradient g y)) with hμ
  set ν : Measure V := KLS.hausdorffNormalized V (Module.finrank ℝ H) with hν
  have hcont : Continuous Ψ := by
    have h : Ψ = fun y => x₀ + (ι y + g y • e) := by
      funext y; rw [hΨ, graphChartMap, graphMap]
    rw [h]
    exact continuous_const.add (ι.continuous.add ((hg.continuous).smul continuous_const))
  have hmeasΨ : Measurable Ψ := hcont.measurable
  have hinj : Function.Injective Ψ := graphChartMap_injective_of_perp ι hperp x₀ g
  -- the area formula, read as a statement about the pushforward
  have hkey : Measure.map Ψ μ = ν.restrict (Set.range Ψ) := by
    refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply hmeasΨ hE, hμ,
      withDensity_apply _ (hE.preimage hmeasΨ),
      ← hausdorffNormalized_image_graphChartMap ι he hperp x₀ (hg.of_le le_rfl)
        (hE.preimage hmeasΨ),
      Measure.restrict_apply hE, Set.image_preimage_eq_inter_range]
  have himgmeas : MeasurableSet (Ψ '' s) :=
    measurableSet_image_graphChartMap ι hperp x₀ hg.continuous hs
  have hpre : Ψ ⁻¹' (Ψ '' s) = s := hinj.preimage_image s
  calc Measure.map Ψ (μ.restrict s)
      = Measure.map Ψ (μ.restrict (Ψ ⁻¹' (Ψ '' s))) := by rw [hpre]
    _ = (Measure.map Ψ μ).restrict (Ψ '' s) := (Measure.restrict_map hmeasΨ himgmeas).symm
    _ = (ν.restrict (Set.range Ψ)).restrict (Ψ '' s) := by rw [hkey]
    _ = ν.restrict (Ψ '' s ∩ Set.range Ψ) := Measure.restrict_restrict himgmeas
    _ = ν.restrict (Ψ '' s) := by
        rw [Set.inter_eq_self_of_subset_left (Set.image_subset_range Ψ s)]

/-- **Change of variables for a nonnegative surface integral over a piece of graph.**  The
parameter set must be measurable and the integrand measurable; no integrability is needed. -/
theorem setLIntegral_image_graphChartMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (x₀ : V) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in graphChartMap ι e x₀ g '' s, f x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y))
          * f (graphChartMap ι e x₀ g y) ∂(volume : Measure H) := by
  have hcont : Continuous (graphChartMap ι e x₀ g) := by
    have h : graphChartMap ι e x₀ g = fun y => x₀ + (ι y + g y • e) := by
      funext y; rw [graphChartMap, graphMap]
    rw [h]
    exact continuous_const.add (ι.continuous.add ((hg.continuous).smul continuous_const))
  rw [← map_graphChartMap_withDensity ι he hperp x₀ hg hs,
    lintegral_map hf hcont.measurable,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_graphJacobian_gradient hg)
      (show Measurable fun y : H => f (graphChartMap ι e x₀ g y) from
        hf.comp hcont.measurable) hs]
  rfl

/-- **Change of variables for a surface integral over a piece of graph.**  For a measurable
parameter set and an almost everywhere strongly measurable integrand, the surface integral over
the graph piece is the parameter integral of the integrand weighted by the graph Jacobian.  No
integrability hypothesis is needed: if either side fails to be integrable, both sides are `0`. -/
theorem setIntegral_image_graphChartMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (x₀ : V) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : V → E}
    (hf : AEStronglyMeasurable f
      ((KLS.hausdorffNormalized V (Module.finrank ℝ H)).restrict
        (graphChartMap ι e x₀ g '' s))) :
    ∫ x in graphChartMap ι e x₀ g '' s, f x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫ y in s, graphJacobian (gradient g y) • f (graphChartMap ι e x₀ g y)
          ∂(volume : Measure H) := by
  have hcont : Continuous (graphChartMap ι e x₀ g) := by
    have h : graphChartMap ι e x₀ g = fun y => x₀ + (ι y + g y • e) := by
      funext y; rw [graphChartMap, graphMap]
    rw [h]
    exact continuous_const.add (ι.continuous.add ((hg.continuous).smul continuous_const))
  have hJnn : Measurable fun y : H => (graphJacobian (gradient g y)).toNNReal :=
    (continuous_graphJacobian.comp (BakryEmery.continuous_gradient hg)).measurable.real_toNNReal
  have hmap := map_graphChartMap_withDensity ι he hperp x₀ hg hs
  rw [← hmap] at hf ⊢
  rw [integral_map hcont.measurable.aemeasurable hf, restrict_withDensity hs,
    show (fun y : H => ENNReal.ofReal (graphJacobian (gradient g y)))
        = fun y : H => (((graphJacobian (gradient g y)).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hJnn]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change ((graphJacobian (gradient g y)).toNNReal : ℝ≥0) • f (graphChartMap ι e x₀ g y)
      = graphJacobian (gradient g y) • f (graphChartMap ι e x₀ g y)
  rw [NNReal.smul_def, Real.coe_toNNReal _ (graphJacobian_nonneg _)]

end GraphIntegral

end FunctionalInequalities.Analysis

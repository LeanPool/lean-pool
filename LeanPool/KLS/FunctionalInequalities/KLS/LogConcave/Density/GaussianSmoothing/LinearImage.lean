/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport

/-!
# Gaussian smoothing of linear images

Two identifications for the Gaussian-smoothed image `smoothedLaw (μ.map S) s`:
- `gaussian_product_latent_map`: if `ρ.map g = μ`, the product `ρ ⊗ Probability.Gaussian.law s`
  pushed by `(y, z) ↦ S (g y) + z` is
  `smoothedLaw (μ.map S) s`;
- `exists_convex_smooth_potential_smoothed_linearEquiv`: for a log-concave `μ` with full affine
  support and an invertible continuous
  linear `S`, the smoothed image is `e^{-W} dx` with `W` smooth and convex, and the smoothed
  probability law is log-concave.

No variance, `H⁻¹`, moment-map or kernel hypothesis is used.
-/

@[expose] public section

section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_product_latent_map (ρ μ : Measure E) [IsProbabilityMeasure ρ]
    (g : E → E) (hg : Measurable g) (hmap : ρ.map g = μ)
    (S : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    (ρ.prod (Probability.Gaussian.law (V := E) s)).map (fun p => S (g p.1) + p.2) =
      smoothedLaw (μ.map S) s := by
  let γ : Measure E := Probability.Gaussian.law s
  let _ : IsProbabilityMeasure γ := Probability.Gaussian.law_probability hs
  have hp : (ρ.map (fun x => S (g x))).prod γ =
      (ρ.prod γ).map (Prod.map (fun x => S (g x)) id) := by
    simpa only [Measure.map_id, Function.comp_def] using Measure.map_prod_map ρ γ
      (S.continuous.measurable.comp hg) measurable_id
  unfold smoothedLaw Measure.conv
  rw [← hmap, Measure.map_map S.continuous.measurable hg]
  change (ρ.prod γ).map (fun p => S (g p.1) + p.2) =
    ((ρ.map (fun x => S (g x))).prod γ).map (fun p => p.1 + p.2)
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

variable [SecondCountableTopology E]

theorem exists_convex_smooth_potential_smoothed_linearEquiv (μ : ProbabilityMeasure E)
    (hLC : FunctionalInequalities.KLS.LogConcave μ) (htop : Probability.affineSupport μ = ⊤)
    (S : E ≃L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    ∃ W : E → ℝ,
      ContDiff ℝ ∞ W ∧
        ConvexOn ℝ univ W ∧
          smoothedLaw ((μ : Measure E).map S) s = (volume : Measure E).tilted (-W) ∧
            FunctionalInequalities.KLS.LogConcave
              (smoothedProbabilityLaw (Probability.mapContinuousLinearEquiv μ S) s hs) := by
  let η := Probability.mapContinuousLinearEquiv μ S
  have hη : FunctionalInequalities.KLS.LogConcave η := hLC.mapContinuousLinearEquiv S
  have hηtop : Probability.affineSupport η = ⊤ :=
    Probability.affineSupport_mapContinuousLinearEquiv_eq_top μ S htop
  have hi := hη.interior_support_nonempty_of_affineSupport_eq_top hηtop
  obtain ⟨ρ, hρ⟩ :=
    hη.exists_isBorellDensity_of_interior_support_nonempty volume hi
      (hη.absolutelyContinuous_of_interior_support_nonempty volume hi)
  exact
    ⟨potential ρ s, potential_contDiff_infty hρ hs, potential_convex hρ hs,
      smoothedLaw_eq_tilted_potential hρ hs, smoothedProbabilityLaw_logConcave hρ hs⟩

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

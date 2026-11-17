/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HminusOne
public import LeanPool.KLS.FunctionalInequalities.Probability.Variance.Quadratic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Moments
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport

/-!
# Quadratic variance under Gaussian smoothing

- `le_of_forall_inverse_noise_quadratic_error`: removing a vanishing noise error `c (2s)⁻¹ + d
  ((2s)⁻¹)²` as `s → ∞`;
- `variance_quadratic_le_smoothedLaw`: Gaussian smoothing does not decrease the variance of a
  quadratic form (finite fourth moment);
- `gaussian_smoothed_quadratic_variance_le_latent_energy`: for a log-concave `μ` with full affine
  support that is the gradient image of a
  `C¹` globally Lipschitz `u` with Lipschitz gradient and `∫ e^{-u} = 1`, the variance of `⟪Q x, x⟫`
  (self-adjoint `Q`) under the smoothed
  image `smoothedLaw (μ.map S) s` is at most `4` times the latent product energy, via the `H⁻¹`
  inequality on the smooth convex smoothed
  law.
-/

@[expose] public section

section
open MeasureTheory Set ProbabilityTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

theorem gaussian_smoothed_quadratic_variance_le_latent_energy {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : FunctionalInequalities.KLS.LogConcave μ) (hfull : Probability.affineSupport μ = ⊤)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hsource :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hQ : IsSelfAdjoint Q) {s : ℝ}
    (hs : 0 < s) :
    let P :=
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
        (Probability.Gaussian.law (V := EuclideanSpace ℝ (Fin n)) s)
    variance (fun x => ⟪Q x, x⟫) (smoothedLaw ((μ : Measure _).map S) s) ≤
      4 *
        ∑ i : Fin n,
          ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ‖S
                    (action (hessianMatrix u p.1)
                      (S.toContinuousLinearMap.adjoint (Q (EuclideanSpace.single i 1)))) +
                  (2 * s)⁻¹ • Q (EuclideanSpace.single i 1)‖ ^
              2 ∂P := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E := volume.tilted (-u)
  let P := ρ.prod (Probability.Gaussian.law (V := E) s)
  let ν := smoothedProbabilityLaw (Probability.mapContinuousLinearEquiv μ S) s hs
  let f : E → ℝ := fun x => ⟪Q x, x⟫
  let J : Fin n → ℝ := fun i =>
    ∫ p : E × E,
      ‖S
              (action (hessianMatrix u p.1)
                (S.toContinuousLinearMap.adjoint (Q (EuclideanSpace.single i 1)))) +
            (2 * s)⁻¹ • Q (EuclideanSpace.single i 1)‖ ^
        2 ∂P
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hexp
  have hgnorm (x : E) : ‖gradient u x‖ ≤ (L : ℝ) := by
    calc
      _ = ‖fderiv ℝ u x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ hL
  have hu4 : MemLp (gradient u) 4 ρ :=
    MemLp.of_bound (continuous_gradient hu).aestronglyMeasurable (L : ℝ) (ae_of_all _ hgnorm)
  have hμ4 : MemLp id 4 (μ : Measure E) := by
    rw [← hsource]
    exact
      (memLp_map_measure_iff continuous_id.aestronglyMeasurable
            (continuous_gradient hu).measurable.aemeasurable).2
        hu4
  let : IsProbabilityMeasure ((μ : Measure E).map S.toContinuousLinearMap) :=
    (Measure.isProbabilityMeasure_map_iff
      S.toContinuousLinearMap.continuous.measurable.aemeasurable).2 inferInstance
  have hν4 : MemLp id 4 (ν : Measure E) :=
    smoothedLaw_memLp_four _ (Probability.memLp_four_map_linear _ S.toContinuousLinearMap hμ4)
      hs
  have hν2 : MemLp id 2 (ν : Measure E) := hν4.mono_exponent (by norm_num)
  obtain ⟨W, hW, hWc, hνW, hνLC⟩ :=
    exists_convex_smooth_potential_smoothed_linearEquiv μ hLC hfull S hs
  have hf : ContDiff ℝ 1 f := Q.contDiff.inner ℝ contDiff_id
  have hf2 : MemLp f 2 (ν : Measure E) := Probability.memLp_quadratic_of_memLp_four hν4 Q
  have hdf (x w : E) : fderiv ℝ f x w = 2 * ⟪x, Q w⟫ := by
    have hd := Q.hasFDerivAt.inner ℝ (hasFDerivAt_id (𝕜 := ℝ) x)
    change HasFDerivAt f _ x at hd
    rw [hd.fderiv]
    change ⟪Q x, w⟫ + ⟪Q w, x⟫ = 2 * ⟪x, Q w⟫
    have hqxw : ⟪Q x, w⟫ = ⟪x, Q w⟫ := hQ.isSymmetric x w
    rw [hqxw, real_inner_comm x (Q w)]
    ring
  have hdf2 (i : Fin n) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 (ν : Measure E) := by
    apply MemLp.ae_eq (ae_of_all _ fun x => (hdf x _).symm)
    exact (hν2.inner_const (𝕜 := ℝ) (Q (EuclideanSpace.single i 1))).const_mul 2
  have hK (i : Fin n) (h : E → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure E)) ^ 2 ≤
      (4 * J i) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure E) := by
    have hd :=
      gaussian_product_compact_dual_bound μ ν hu hL hG hnorm hsource S.toContinuousLinearMap
        (Q (EuclideanSpace.single i 1)) hs rfl h hh hhc
    have hp :
      (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * h x ∂(ν : Measure E)) =
        2 * ∫ x, ⟪x, Q (EuclideanSpace.single i 1)⟫ * h x ∂(ν : Measure E) := by
      simp_rw [hdf]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    rw [hp]
    calc
      _ = 4 * (∫ x, ⟪x, Q (EuclideanSpace.single i 1)⟫ * h x ∂(ν : Measure E)) ^ 2 := by ring
      _ ≤ 4 * (J i * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure E)) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = _ := by ring
  have hv :=
    variance_le_sum_of_partial_dual_bounds volume hνLC hνW
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hWc hf hf2 hdf2 (fun i => 4 * J i) hK
  change variance f (ν : Measure E) ≤ 4 * ∑ i, J i
  simpa only [Finset.mul_sum] using hv

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

theorem variance_quadratic_le_smoothedLaw {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (mu : ProbabilityMeasure E) (h4 : MemLp (id : E → E) 4 (mu : Measure E))
    (A : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    variance (fun x : E => ⟪A x, x⟫) (mu : Measure E) ≤
      variance (fun x : E => ⟪A x, x⟫) (smoothedLaw (mu : Measure E) s) := by
  let noise : ProbabilityMeasure E :=
    ⟨Probability.Gaussian.law s, Probability.Gaussian.law_probability hs⟩
  exact
    Probability.quadratic_variance_le_centered_noise_convolution mu noise h4
      (Probability.Gaussian.memLp_four hs) (Probability.Gaussian.mean_zero hs) A

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

section
open Filter
open scoped Topology

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

theorem le_of_forall_inverse_noise_quadratic_error (a b c d : ℝ)
    (h : ∀ s : ℝ, 0 < s → a ≤ b + c * (2 * s)⁻¹ + d * ((2 * s)⁻¹) ^ 2) : a ≤ b := by
  have hden : Tendsto (fun s : ℝ => 2 * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have heps : Tendsto (fun s : ℝ => (2 * s)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp hden
  have hr : Tendsto (fun s : ℝ => b + c * (2 * s)⁻¹ + d * ((2 * s)⁻¹) ^ 2) atTop (𝓝 b) := by
    simpa using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul heps)).add
        (tendsto_const_nhds.mul (heps.pow 2))
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds hr
      (Filter.eventually_atTop.2 ⟨1, fun s hs => h s (lt_of_lt_of_le zero_lt_one hs)⟩)

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

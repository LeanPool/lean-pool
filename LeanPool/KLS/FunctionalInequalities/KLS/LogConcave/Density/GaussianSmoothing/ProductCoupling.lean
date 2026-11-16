/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HessianStein
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Core
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
public import LeanPool.KLS.FunctionalInequalities.L2.Pairing
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.SourceDualBound
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.HessianKernel

/-!
# The Gaussian product coupling of a latent source

For a `C¹` globally Lipschitz `u` with Lipschitz gradient and `∫ e^{-u} = 1`, the latent law `ρ =
e^{-u} dx`, the Gaussian `Probability.Gaussian.law s`
and a continuous linear `S`:
- integrability of the source and noise pairings on `ρ ⊗ Probability.Gaussian.law s` for bounded
  Lipschitz `C¹` tests;
- the product source Stein identity (source Stein on the first factor, the translated Gaussian
  identity on the second, Fubini);
- the compact dual Cauchy–Schwarz bound for the smoothed linear image, with the latent field `S
  (∇²u) S† v + (2s)⁻¹ v`.

No target Stein kernel or inverse transport is constructed.
-/

@[expose] public section

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

theorem gaussian_product_source_stein_pairings_integrable {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal} (hu : ContDiff ℝ 1 u)
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1) (hh : ContDiff ℝ 1 h)
    (hhLip : LipschitzWith Lh h) (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    {s : ℝ} (hs : 0 < s) :
    let P :=
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
        (Probability.Gaussian.law (V := EuclideanSpace ℝ (Fin n)) s)
    let Z := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      S (gradient u p.1) + p.2
    let F := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      S (action (hessianMatrix u p.1) (S.adjoint v))
    MemLp Z 2 P ∧
      MemLp F 2 P ∧
        MemLp (fun p => gradient h (Z p)) 2 P ∧
          Integrable (fun p => ⟪S (gradient u p.1), v⟫ * h (Z p)) P ∧
            Integrable (fun p => ⟪p.2, v⟫ * h (Z p)) P ∧
              Integrable
                  (fun p =>
                    ⟪S.adjoint v, action (hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫)
                  P ∧
                Integrable (fun p => fderiv ℝ h (Z p) v) P := by
  let E := EuclideanSpace ℝ (Fin n)
  let rho : Measure E := volume.tilted (-u)
  let nu : Measure E := Probability.Gaussian.law s
  let P := rho.prod nu
  let Z : E × E → E := fun p => S (gradient u p.1) + p.2
  let F : E × E → E := fun p => S (action (hessianMatrix u p.1) (S.adjoint v))
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hexp
  let : IsProbabilityMeasure nu := Probability.Gaussian.law_probability hs
  have hgnorm (f : E → ℝ) {K : NNReal} (hf : LipschitzWith K f) (x : E) :
    ‖gradient f x‖ ≤ (K : ℝ) := by
    calc
      ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ hf
  have hu2 : MemLp (gradient u) 2 rho :=
    MemLp.of_bound (continuous_gradient hu).aestronglyMeasurable (L : ℝ)
      (ae_of_all _ (hgnorm u hL))
  have hSU : MemLp (fun p : E × E => S (gradient u p.1)) 2 P :=
    (hu2.continuousLinearMap_comp S).comp_fst nu
  have hnoise : MemLp (fun p : E × E => p.2) 2 P :=
    (Probability.Gaussian.memLp_two hs).comp_snd rho
  have hZ2 : MemLp Z 2 P := hSU.add hnoise
  have hZmeas : Measurable Z :=
    (S.continuous.measurable.comp ((continuous_gradient hu).measurable.comp measurable_fst)).add
      measurable_snd
  have hh2 : MemLp (fun p => h (Z p)) 2 P :=
    MemLp.of_bound (hh.continuous.measurable.comp hZmeas).aestronglyMeasurable C
      (ae_of_all _ fun p => hbound (Z p))
  have hg2 : MemLp (fun p => gradient h (Z p)) 2 P :=
    MemLp.of_bound ((continuous_gradient hh).measurable.comp hZmeas).aestronglyMeasurable
      (Lh : ℝ) (ae_of_all _ fun p => hgnorm h hhLip (Z p))
  have hF2 : MemLp F 2 P :=
    ((memLp_hessian_action_of_lipschitz_gradient hG rho (S.adjoint v)).continuousLinearMap_comp
          S).comp_fst
      nu
  have hSL : Integrable (fun p : E × E => ⟪S (gradient u p.1), v⟫ * h (Z p)) P :=
    (hSU.inner_const (𝕜 := ℝ) v).integrable_mul hh2
  have hNL : Integrable (fun p : E × E => ⟪p.2, v⟫ * h (Z p)) P :=
    (hnoise.inner_const (𝕜 := ℝ) v).integrable_mul hh2
  have hdiff : ∀ᵐ y ∂rho, DifferentiableAt ℝ (gradient u) y :=
    (tilted_absolutelyContinuous (volume : Measure E) (-u)).ae_le
      (hG.ae_differentiableAt (μ := volume))
  have hSym : ∀ᵐ y ∂rho, (hessianMatrix u y).IsHermitian :=
    hdiff.mono fun y hy => hessianMatrix_isHermitian_of_differentiableAt_gradient hu hy
  have hproj : MeasurePreserving (Prod.fst : E × E → E) P rho := measurePreserving_fst
  have hSR :
    Integrable
      (fun p : E × E =>
        ⟪S.adjoint v, action (hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫)
      P := by
    apply (FunctionalInequalities.L2.integrable_inner_of_memLp hF2 hg2).congr
    filter_upwards [hproj.quasiMeasurePreserving.ae hSym] with p hp
    change ⟪S (action (hessianMatrix u p.1) (S.adjoint v)), gradient h (Z p)⟫ = _
    rw [← S.adjoint_inner_right]
    exact
      (inner_action_swap (hessianMatrix u p.1)
          (fun i j => by simpa only [star_trivial] using hp.apply j i) (S.adjoint v)
          (S.adjoint (gradient h (Z p)))).symm
  have hNR : Integrable (fun p : E × E => fderiv ℝ h (Z p) v) P := by
    apply ((hg2.inner_const (𝕜 := ℝ) v).integrable one_le_two).congr
    exact ae_of_all _ fun p => inner_gradient_left
  exact ⟨hZ2, hF2, hg2, hSL, hNL, hSR, hNR⟩

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

theorem gaussian_product_source_stein_identity {n : ℕ} {u h : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G Lh : NNReal} (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h) (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    {s : ℝ} (hs : 0 < s) :
    let P :=
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
        (Probability.Gaussian.law (V := EuclideanSpace ℝ (Fin n)) s)
    Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2))
        P ∧
      Integrable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ⟪S.adjoint v,
                action (hessianMatrix u p.1)
                  (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
              (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v)
          P ∧
        (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2) ∂P) =
          ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ⟪S.adjoint v,
                action (hessianMatrix u p.1)
                  (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
              (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v ∂P := by
  let E := EuclideanSpace ℝ (Fin n)
  let rho : Measure E := volume.tilted (-u)
  let nu : Measure E := Probability.Gaussian.law s
  let P := rho.prod nu
  let SL : E × E → ℝ := fun p => ⟪S (gradient u p.1), v⟫ * h (S (gradient u p.1) + p.2)
  let NL : E × E → ℝ := fun p => ⟪p.2, v⟫ * h (S (gradient u p.1) + p.2)
  let SR : E × E → ℝ := fun p =>
    ⟪S.adjoint v,
      action (hessianMatrix u p.1) (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫
  let NR : E × E → ℝ := fun p => fderiv ℝ h (S (gradient u p.1) + p.2) v
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hexp
  let : IsProbabilityMeasure nu := Probability.Gaussian.law_probability hs
  obtain ⟨_hZ, _hF, _hGH, hSL, hNL, hSR, hNR⟩ :=
    gaussian_product_source_stein_pairings_integrable hu hL hG hnorm hh hhLip C hbound S v hs
  have hsrc : (∫ p, SL p ∂P) = ∫ p, SR p ∂P := by
    rw [integral_prod_symm SL hSL, integral_prod_symm SR hSR]
    apply integral_congr_ae
    filter_upwards [] with z
    exact
      (source_affine_stein_identity_of_bounded_lipschitz_test hu hL hG hnorm hh hhLip C hbound S
            z v).2.2
  have hnoise : (∫ p, NL p ∂P) = (2 * s)⁻¹ * ∫ p, NR p ∂P := by
    calc
      _ = ∫ y, ∫ z, NL (y, z) ∂nu ∂rho := integral_prod NL hNL
      _ = ∫ y, (2 * s)⁻¹ * ∫ z, NR (y, z) ∂nu ∂rho := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact
          (Probability.Gaussian.translated_directional_identity_of_bounded_lipschitz_test hh
                hhLip C hbound (S (gradient u y)) v hs).2.2
      _ = (2 * s)⁻¹ * ∫ y, ∫ z, NR (y, z) ∂nu ∂rho := integral_const_mul _ _
      _ = _ := by rw [← integral_prod NR hNR]
  have hleft (p : E × E) :
    ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2) = SL p + NL p := by
    dsimp only [SL, NL]
    rw [inner_add_left, add_mul]
  have hLtotal :
    Integrable (fun p : E × E => ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2))
      P :=
    (hSL.add hNL).congr (ae_of_all _ fun p => (hleft p).symm)
  have hRtotal : Integrable (fun p : E × E => SR p + (2 * s)⁻¹ * NR p) P :=
    hSR.add (hNR.const_mul ((2 * s)⁻¹))
  refine ⟨hLtotal, hRtotal, ?_⟩
  calc
    _ = ∫ p, SL p + NL p ∂P := integral_congr_ae (ae_of_all _ hleft)
    _ = (∫ p, SL p ∂P) + ∫ p, NL p ∂P := integral_add hSL hNL
    _ = (∫ p, SR p ∂P) + (2 * s)⁻¹ * ∫ p, NR p ∂P := by rw [hsrc, hnoise]
    _ = (∫ p, SR p ∂P) + ∫ p, (2 * s)⁻¹ * NR p ∂P := by rw [integral_const_mul]
    _ = _ := (integral_add hSR (hNR.const_mul ((2 * s)⁻¹))).symm

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

theorem gaussian_product_compact_dual_bound {n : ℕ}
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G : NNReal} (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hsource :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    {s : ℝ} (hs : 0 < s)
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = smoothedLaw ((μ : Measure _).map S) s)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    let P :=
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
        (Probability.Gaussian.law (V := EuclideanSpace ℝ (Fin n)) s)
    (∫ x, ⟪x, v⟫ * h x ∂(ν : Measure _)) ^ 2 ≤
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ‖S (action (hessianMatrix u p.1) (S.adjoint v)) + (2 * s)⁻¹ • v‖ ^ 2 ∂P) *
        ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E := volume.tilted (-u)
  let γ : Measure E := Probability.Gaussian.law s
  let P := ρ.prod γ
  let Z : E × E → E := fun p => S (gradient u p.1) + p.2
  let F : E × E → E := fun p => S (action (hessianMatrix u p.1) (S.adjoint v)) + (2 * s)⁻¹ • v
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hexp
  let : IsProbabilityMeasure γ := Probability.Gaussian.law_probability hs
  have hh1 : ContDiff ℝ 1 h := hh.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Lh, hhLip⟩ :=
    Energy.WeightedGradient.lipschitzWith_of_contDiff_hasCompactSupport hh hhc
  obtain ⟨C, hC⟩ := hh.continuous.bounded_above_of_compact_support hhc
  have hZ : Measurable Z :=
    (S.continuous.measurable.comp ((continuous_gradient hu).measurable.comp measurable_fst)).add
      measurable_snd
  have hmap : P.map Z = (ν : Measure E) :=
    (gaussian_product_latent_map ρ (μ : Measure E) (gradient u)
          (continuous_gradient hu).measurable hsource S hs).trans
      hν.symm
  obtain ⟨_, hF2, _, _, _, _, _⟩ :=
    gaussian_product_source_stein_pairings_integrable hu hL hG hnorm hh1 hhLip C hC S v hs
  have hF : MemLp F 2 P := hF2.add (memLp_const ((2 * s)⁻¹ • v))
  have hpair :=
    (gaussian_product_source_stein_identity hu hL hG hnorm hh1 hhLip C hC S v hs).2.2
  have hdiff : ∀ᵐ y ∂ρ, DifferentiableAt ℝ (gradient u) y :=
    (tilted_absolutelyContinuous (volume : Measure E) (-u)).ae_le
      (hG.ae_differentiableAt (μ := volume))
  have hSym : ∀ᵐ y ∂ρ, (hessianMatrix u y).IsHermitian := by
    filter_upwards [hdiff] with y hy
    exact hessianMatrix_isHermitian_of_differentiableAt_gradient hu hy
  have hproj : MeasurePreserving (Prod.fst : E × E → E) P ρ := measurePreserving_fst
  have hright :
    (∫ p : E × E,
        ⟪S.adjoint v, action (hessianMatrix u p.1) (S.adjoint (gradient h (Z p)))⟫ +
          (2 * s)⁻¹ * fderiv ℝ h (Z p) v ∂P) =
      ∫ p, ⟪F p, gradient h (Z p)⟫ ∂P := by
    apply integral_congr_ae
    filter_upwards [hproj.quasiMeasurePreserving.ae hSym] with p hp
    dsimp only [F]
    rw [inner_add_left, real_inner_smul_left]
    congr 1
    · rw [← S.adjoint_inner_right]
      exact
        inner_action_swap (hessianMatrix u p.1)
          (fun i j => by simpa only [star_trivial] using hp.apply j i) (S.adjoint v)
          (S.adjoint (gradient h (Z p)))
    · rw [real_inner_comm (gradient h (Z p)) v, inner_gradient_left]
  have hid : (∫ x, ⟪x, v⟫ * h x ∂(ν : Measure E)) = ∫ p, ⟪F p, gradient h (Z p)⟫ ∂P := by
    calc
      _ = ∫ p, ⟪Z p, v⟫ * h (Z p) ∂P := by
        rw [← hmap]
        exact
          integral_map hZ.aemeasurable
            ((continuous_id.inner continuous_const).mul hh.continuous).aestronglyMeasurable
      _ = _ := hpair.trans hright
  exact compact_linear_pairing_sq_le_of_source_identity P ν Z F hZ hmap hF v h hh hhc hid

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

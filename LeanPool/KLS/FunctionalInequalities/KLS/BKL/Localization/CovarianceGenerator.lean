/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Coefficients
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.LogPartition
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance
public import LeanPool.KLS.FunctionalInequalities.Probability.Diffusion.Generator
/-!
# The generator of the posterior covariance

The carré-du-champ product rule for the generator, `𝓛 ∫ f dμ_p = 0` for posterior expectations, and
`𝓛⟪A x, y⟫ = −⟪A x, y⟫` (BKL arXiv:2610.05474v1, (69)).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.Probability.Diffusion

private theorem diffusionGenerator_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    diffusionGenerator b σ (fun y => u y - v y) x =
      diffusionGenerator b σ u x - diffusionGenerator b σ v x := by
  have hu' : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x := hv.differentiableAt (by norm_num)
  have hfu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsub :
      (fun y => fderiv ℝ (fun z => u z - v z) y) =ᶠ[nhds x]
        (fun y => fderiv ℝ u y - fderiv ℝ v y) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hyu hyv
    exact fderiv_fun_sub (hyu.differentiableAt (by norm_num))
      (hyv.differentiableAt (by norm_num))
  have hsecond (a c : V) :
      fderiv ℝ (fderiv ℝ (fun y => u y - v y)) x a c =
        fderiv ℝ (fderiv ℝ u) x a c - fderiv ℝ (fderiv ℝ v) x a c := by
    rw [hsub.fderiv_eq, fderiv_fun_sub hfu hfv]
    simp only [sub_apply]
  unfold diffusionGenerator
  rw [fderiv_fun_sub hu' hv']
  simp_rw [hsecond]
  simp only [sub_apply, Finset.sum_sub_distrib]
  ring


end FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/--
**Posterior expectations have zero drift** (BKL (68), deterministic generator form): for `f` bounded
on the
prior support, `𝓛(p ↦ ∫ f dμ_p) = 0` with the uncut generator of (67). -/
theorem generator_posteriorExpectation (hiso : KLS.Isotropic μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure (EuclideanSpace ℝ (Fin n))).support, ‖f x‖ ≤ C) (p : Param n) :
    generator μ hc (fun q : Param n => posteriorExpectation μ q.1 q.2 f) p = 0 := by
  have hF : ContDiff ℝ 2 (fun q : Param n => posteriorExpectation μ q.1 q.2 f) :=
    (contDiff_posteriorExpectation_joint μ hc hf hfb).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [generator_eq_partial μ hc hiso _ hF p]
  have hcancel :=
    Isotropic.compactPosterior_generator_cancellation μ hc hiso hf hC hfb p.1 p.2
      (EuclideanSpace.basisFun (Fin n) ℝ)
  dsimp only at hcancel
  simp only [EuclideanSpace.basisFun_apply] at hcancel
  exact hcancel

/--
**BKL (69) in generator form**: `𝓛A = −A`, i.e. `𝓛(p ↦ ⟪A(p) x, y⟫) = −⟪A(p) x, y⟫` for all `x, y`.
-/
theorem generator_inner_cov (hiso : KLS.Isotropic μ) (p : Param n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    generator μ hc (fun q : Param n => ⟪cov μ hc q x, y⟫) p = -⟪cov μ hc p x, y⟫ := by
  let gx : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ⟪x, z⟫
  let gy : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ⟪y, z⟫
  let gxy : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ⟪x, z⟫ * ⟪y, z⟫
  obtain ⟨Cx, hCx, hbx⟩ := exists_bound_on_support_of_compact μ hc (by fun_prop : Continuous gx)
  obtain ⟨Cy, hCy, hby⟩ := exists_bound_on_support_of_compact μ hc (by fun_prop : Continuous gy)
  obtain ⟨Cxy, hCxy, hbxy⟩ :=
    exists_bound_on_support_of_compact μ hc (by fun_prop : Continuous gxy)
  have hcovfun :
    (fun q : Param n => ⟪cov μ hc q x, y⟫) =
      (fun q =>
        posteriorExpectation μ q.1 q.2 gxy -
          posteriorExpectation μ q.1 q.2 gx * posteriorExpectation μ q.1 q.2 gy) := by
    funext q
    let :
      IsProbabilityMeasure
        ((μ : Measure (EuclideanSpace ℝ (Fin n))).tilted (quadraticExponent q.1 q.2)) :=
      isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc q.1 q.2
    have hmx :=
      memLp_two_tilted_quadraticExponent_of_compact μ hc q.1 q.2 (by fun_prop : Continuous gx)
    have hmy :=
      memLp_two_tilted_quadraticExponent_of_compact μ hc q.1 q.2 (by fun_prop : Continuous gy)
    rw [cov, Covariance.operator_inner,
      covarianceBilin_apply_eq_cov (compactPosterior_memLp_id_two μ hc q.1 q.2)]
    change
      covariance gx gy
          ((μ : Measure (EuclideanSpace ℝ (Fin n))).tilted (quadraticExponent q.1 q.2)) =
        _
    rw [covariance_eq_sub hmx hmy]
    rfl
  have hGx : ContDiff ℝ 2 (fun q : Param n => posteriorExpectation μ q.1 q.2 gx) :=
    (contDiff_posteriorExpectation_joint μ hc (by fun_prop) hbx).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hGy : ContDiff ℝ 2 (fun q : Param n => posteriorExpectation μ q.1 q.2 gy) :=
    (contDiff_posteriorExpectation_joint μ hc (by fun_prop) hby).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hGxy : ContDiff ℝ 2 (fun q : Param n => posteriorExpectation μ q.1 q.2 gxy) :=
    (contDiff_posteriorExpectation_joint μ hc (by fun_prop) hbxy).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hprod :
    ContDiffAt ℝ 2
      (fun q : Param n => posteriorExpectation μ q.1 q.2 gx * posteriorExpectation μ q.1 q.2 gy)
      p :=
    hGx.contDiffAt.mul hGy.contDiffAt
  have hzeroX :
    diffusionGenerator (drift μ hc) (noise μ hc)
        (fun q : Param n => posteriorExpectation μ q.1 q.2 gx) p =
      0 :=
    generator_posteriorExpectation μ hc hiso (by fun_prop) hCx hbx p
  have hzeroY :
    diffusionGenerator (drift μ hc) (noise μ hc)
        (fun q : Param n => posteriorExpectation μ q.1 q.2 gy) p =
      0 :=
    generator_posteriorExpectation μ hc hiso (by fun_prop) hCy hby p
  have hzeroXY :
    diffusionGenerator (drift μ hc) (noise μ hc)
        (fun q : Param n => posteriorExpectation μ q.1 q.2 gxy) p =
      0 :=
    generator_posteriorExpectation μ hc hiso (by fun_prop) hCxy hbxy p
  set A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := cov μ hc p
  set σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := inverseSqrt A
  have hnoise (k : Fin n) : noise μ hc p k = (σ (EuclideanSpace.single k 1), 0) := rfl
  have hself := (inverseSqrt_cov_props μ hc hiso p).1
  have hss := (inverseSqrt_cov_props μ hc hiso p).2
  change ∀ u v, ⟪σ u, v⟫ = ⟪u, σ v⟫ at hself
  change ∀ v, σ (σ v) = Ring.inverse A v at hss
  have hMA (z : EuclideanSpace ℝ (Fin n)) : Ring.inverse A (A z) = z := by
    have h :=
      congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T z)
        (Isotropic.compactPosterior_ringInverse_covariance μ hc hiso p.1 p.2).2.1
    simpa only [A, cov, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have hsum :
    ∑ k, ⟪A x, σ (EuclideanSpace.single k 1)⟫ * ⟪A y, σ (EuclideanSpace.single k 1)⟫ =
      ⟪A x, y⟫ := by
    calc
      ∑ k, ⟪A x, σ (EuclideanSpace.single k 1)⟫ * ⟪A y, σ (EuclideanSpace.single k 1)⟫ =
          ∑ k, ⟪σ (A x), EuclideanSpace.single k 1⟫ * ⟪EuclideanSpace.single k 1, σ (A y)⟫ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← hself (A x) (EuclideanSpace.single k 1), ←
          hself (A y) (EuclideanSpace.single k 1)]
        rw [real_inner_comm (σ (A y)) (EuclideanSpace.single k 1)]
      _ = ⟪σ (A x), σ (A y)⟫ := by
        simpa only [EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner (σ (A x)) (σ (A y))
      _ = ⟪A x, σ (σ (A y))⟫ := hself (A x) (σ (A y))
      _ = ⟪A x, y⟫ := by rw [hss, hMA]
  have hdx (k : Fin n) :
    fderiv ℝ (fun q : Param n => posteriorExpectation μ q.1 q.2 gx) p (noise μ hc p k) =
      ⟪A x, σ (EuclideanSpace.single k 1)⟫ := by
    rw [hnoise k,
      fderiv_fst_dir _ p (hGx.differentiable (by norm_num) p) (σ (EuclideanSpace.single k 1))]
    rw [fderiv_posteriorExpectation_c_apply μ hc (by fun_prop) hCx hbx p.1 p.2]
    change
      _ =
        ⟪Covariance.operator
            (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) x,
          σ (EuclideanSpace.single k 1)⟫
    rw [Covariance.operator_inner,
      covarianceBilin_apply_eq_cov (compactPosterior_memLp_id_two μ hc p.1 p.2)]
    rfl
  have hdy (k : Fin n) :
    fderiv ℝ (fun q : Param n => posteriorExpectation μ q.1 q.2 gy) p (noise μ hc p k) =
      ⟪A y, σ (EuclideanSpace.single k 1)⟫ := by
    rw [hnoise k,
      fderiv_fst_dir _ p (hGy.differentiable (by norm_num) p) (σ (EuclideanSpace.single k 1))]
    rw [fderiv_posteriorExpectation_c_apply μ hc (by fun_prop) hCy hby p.1 p.2]
    change
      _ =
        ⟪Covariance.operator
            (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) y,
          σ (EuclideanSpace.single k 1)⟫
    rw [Covariance.operator_inner,
      covarianceBilin_apply_eq_cov (compactPosterior_memLp_id_two μ hc p.1 p.2)]
    rfl
  rw [hcovfun]
  unfold generator
  rw [diffusionGenerator_sub (drift μ hc) (noise μ hc) hGxy.contDiffAt hprod]
  rw [diffusionGenerator_mul (drift μ hc) (noise μ hc) hGx.contDiffAt hGy.contDiffAt]
  rw [hzeroXY, hzeroX, hzeroY]
  simp only [mul_zero, zero_add, zero_sub]
  simp_rw [hdx, hdy]
  exact congrArg (fun t : ℝ => -t) hsum

end FunctionalInequalities.KLS.BKL.Localization

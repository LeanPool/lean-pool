/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.InverseHessianEnergy
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Curvature
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Range

/-!
# The scalar Brascamp–Lieb inequality for a given potential

Let `ν = m.tilted (−U)` be a log-concave probability law on a finite-dimensional real inner-product
space (any dimension,
zero included), `m` an additive Haar measure, and let the Hessian of `U` be positive definite at
every point (no uniform
lower bound). For a `C¹` test `f` in `L²(ν)`, not necessarily compactly supported:

* `scalar_brascamp_lieb_finite_energy` (`U ∈ C²`): if the energy `⟪∇f, H⁻¹∇f⟫` is integrable, then
  `Var_ν f ≤ ∫ ⟪∇f, H⁻¹∇f⟫ dν`;
* `scalar_brascamp_lieb_extended_energy` (`U ∈ C^∞`): with no energy premise,
  `ofReal (Var_ν f) ≤ ∫⁻ ofReal ⟪∇f, H⁻¹∇f⟫ dν`, the right side possibly infinite; `…_of_bounded`
  derives `L²` for bounded
  `f`.

Route: by Young, compact integration by parts and the ordinary-diffusion coercivity
(`compact_variational_estimate`), the
centered class of `f` satisfies `2⟪fbar, w⟫ − ‖w‖² ≤ ∫ energy` on the compact smooth diffusion images
`w`, which are dense in the
centered classes (`center_mem_closure_compactSmoothDiffusionImage`). This is the inequality of
Letwin, arXiv:2607.24164v1,
Lemma A.6, for a GIVEN potential: the source moment map, its Euler–Lagrange identification,
push-forward and regularity, and
therefore A.6 for the source law and Theorem 2.5, are not provided. The one-use Hilbert-closure and
`L²`-pairing helpers are private here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace


namespace FunctionalInequalities.KLS.LogConcave

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A continuous quadratic sublevel bound on a set controls the norm of any
point of its closure when that point is also the vector in the pairing. -/
theorem norm_sq_le_of_mem_closure_quadratic_bound
    (z : H) {S : Set H} {C : ℝ} (hz : z ∈ closure S)
    (hbound : ∀ w ∈ S, 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C) :
    ‖z‖ ^ 2 ≤ C := by
  have hcontinuous :
      Continuous (fun w : H => (2 : ℝ) * ⟪z, w⟫ - ‖w‖ ^ 2) :=
    (continuous_const.mul (continuous_const.inner continuous_id)).sub
      (continuous_id.norm.pow 2)
  have hclosed : IsClosed {w : H | 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C} :=
    isClosed_le hcontinuous continuous_const
  have hclosure : closure S ⊆ {w : H | 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C} :=
    closure_minimal (fun w hw => hbound w hw) hclosed
  have h := hclosure hz
  change 2 * ⟪z, z⟫ - ‖z‖ ^ 2 ≤ C at h
  rw [real_inner_self_eq_norm_sq] at h
  linarith only [h]

end Hilbert

section RealL2

variable {α : Type*} [MeasurableSpace α]

/-- The scalar pairing of actual `toLp` classes is the integral of the
product of their original functions. -/
theorem real_inner_toLp {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/-- Centering the first argument does not change its pairing with a
mean-zero second argument. The constant term is explicitly removed. -/
theorem inner_center_left_of_mean_zero
    (ν : ProbabilityMeasure α) (F w : Lp ℝ 2 (ν : Measure α))
    (hw : FunctionalInequalities.L2.mean ν w = 0) :
    ⟪FunctionalInequalities.L2.center ν F, w⟫ = ⟪F, w⟫ := by
  have hc :
      FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν F) =
        FunctionalInequalities.L2.mean ν F • FunctionalInequalities.L2.const ν 1 := by
    simpa only [mul_one] using
      (FunctionalInequalities.L2.const_smul ν
        (FunctionalInequalities.L2.mean ν F) 1)
  have hcw : ⟪FunctionalInequalities.L2.const ν 1, w⟫ = 0 := by
    rw [real_inner_comm]
    exact hw
  change
    ⟪F - FunctionalInequalities.L2.const ν (FunctionalInequalities.L2.mean ν F), w⟫ =
      ⟪F, w⟫
  rw [inner_sub_left, hc, real_inner_smul_left, hcw, mul_zero, sub_zero]

end RealL2

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Compactness of the diffusion test gives integrability of both pairings,
even though the `C¹` function paired against it need not have compact support. -/
theorem compact_pairing_identity
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U f u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 1 f)
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    Integrable (fun x => f x * (-weightedLaplacian U u x)) (ν : Measure E) ∧
      Integrable (fun x => ⟪gradient f x, gradient u x⟫) (ν : Measure E) ∧
      (∫ x, f x * (-weightedLaplacian U u x) ∂(ν : Measure E)) =
        ∫ x, ⟪gradient f x, gradient u x⟫ ∂(ν : Measure E) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hLs : HasCompactSupport (fun x => -weightedLaplacian U u x) := by
    simpa only [Function.comp_def] using
      ((hasCompactSupport_weightedLaplacian U huc).comp_left
        (g := fun t : ℝ => -t) (by simp))
  have hGs : HasCompactSupport (fun x => ⟪gradient f x, gradient u x⟫) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hasCompactSupport_gradient huc) fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by rw [hz, inner_zero_right])
  have hpairInt :
      Integrable (fun x => f x * (-weightedLaplacian U u x)) (ν : Measure E) :=
    (hf.continuous.mul (continuous_weightedLaplacian hU hu2).neg).integrable_of_hasCompactSupport
      hLs.mul_left
  have hgradInt :
      Integrable (fun x => ⟪gradient f x, gradient u x⟫) (ν : Measure E) :=
    ((continuous_gradient hf).inner (continuous_gradient hu1)).integrable_of_hasCompactSupport
      hGs
  refine ⟨hpairInt, hgradInt, ?_⟩
  have hibp := integral_inner_gradient_tilted m hU hu2 huc hf
  rw [← hνU] at hibp
  calc
    (∫ x, f x * (-weightedLaplacian U u x) ∂(ν : Measure E)) =
        ∫ x, -weightedLaplacian U u x * f x ∂(ν : Measure E) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    _ = ∫ x, ⟪gradient u x, gradient f x⟫ ∂(ν : Measure E) := hibp.symm
    _ = ∫ x, ⟪gradient f x, gradient u x⟫ ∂(ν : Measure E) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)

omit [SecondCountableTopology E] in
/-- Every literal compact smooth diffusion image has mean zero, by compact
integration by parts against the constant function one. -/
theorem compact_diffusion_toLp_mean_zero
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    FunctionalInequalities.L2.mean ν
      ((memLp_neg_weightedLaplacian (ν := ν) hU hu huc).toLp
        (fun x => -weightedLaplacian U u x)) = 0 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hibp := integral_inner_gradient_tilted m
    (g := fun _ : E => (1 : ℝ)) hU hu2 huc contDiff_const
  rw [← hνU] at hibp
  rw [FunctionalInequalities.L2.mean_toLp]
  simpa only [gradient_fun_const, inner_zero_right, integral_zero, mul_one]
    using hibp.symm

/-- The actual compact-test variational estimate, obtained from operator
Young, compact integration by parts, and ordinary diffusion coercivity.
The pairing and diffusion-square integrability are retained in the conclusion. -/
theorem compact_variational_estimate
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    {U f u : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (hf : ContDiff ℝ 1 f)
    (henergy : Integrable
      (fun x => ⟪gradient f x, Ring.inverse (hessianOperator U x) (gradient f x)⟫)
      (ν : Measure E))
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    Integrable (fun x => f x * (-weightedLaplacian U u x)) (ν : Measure E) ∧
      Integrable (fun x => weightedLaplacian U u x ^ 2) (ν : Measure E) ∧
      2 * (∫ x, f x * (-weightedLaplacian U u x) ∂(ν : Measure E)) -
          (∫ x, weightedLaplacian U u x ^ 2 ∂(ν : Measure E)) ≤
        ∫ x, ⟪gradient f x,
          Ring.inverse (hessianOperator U x) (gradient f x)⟫ ∂(ν : Measure E) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  obtain ⟨hpairInt, hgradInt, hpair⟩ :=
    compact_pairing_identity m hνU hU1 hf hu huc
  obtain ⟨hH, hL, hcoer⟩ :=
    compact_ordinary_diffusion_coercivity m hU hu huc
  rw [← hνU] at hH hL hcoer
  have hyoung := integral_mono (hgradInt.const_mul 2) (henergy.add hH)
    (fun x => hessian_inverse_young hU x (hPD x) (gradient f x) (gradient u x))
  simp only [Pi.add_apply] at hyoung
  rw [integral_const_mul, integral_add henergy hH] at hyoung
  refine ⟨hpairInt, hL, ?_⟩
  rw [hpair]
  linarith only [hyoung, hcoer]

/-- Finite-energy scalar Brascamp--Lieb for a given `C²` positive-definite
potential and its actual probability law. The test function is only `C¹`
and square-integrable, and need not have compact support. All dimensions,
including zero, are allowed. No uniform lower Hessian bound is assumed. -/
theorem scalar_brascamp_lieb_finite_energy
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν)
    {U f : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (ν : Measure E))
    (henergy : Integrable
      (fun x => inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x))) (ν : Measure E)) :
    ProbabilityTheory.variance f (ν : Measure E) ≤
      ∫ x, inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x)) ∂(ν : Measure E) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  let F : Lp ℝ 2 (ν : Measure E) := hf2.toLp f
  let C : ℝ := ∫ x, inner ℝ (gradient f x)
    (Ring.inverse (hessianOperator U x) (gradient f x)) ∂(ν : Measure E)
  have hQ : ∀ w ∈ compactSmoothDiffusionImage (ν := ν) hU1,
      2 * ⟪FunctionalInequalities.L2.center ν F, w⟫ - ‖w‖ ^ 2 ≤ C := by
    rintro w ⟨u, hu, huc, rfl⟩
    let hL : MemLp (fun x => -weightedLaplacian U u x) 2 (ν : Measure E) :=
      memLp_neg_weightedLaplacian (ν := ν) hU1 hu huc
    let W : Lp ℝ 2 (ν : Measure E) :=
      hL.toLp (fun x => -weightedLaplacian U u x)
    change 2 * ⟪FunctionalInequalities.L2.center ν F, W⟫ - ‖W‖ ^ 2 ≤ C
    have hmean : FunctionalInequalities.L2.mean ν W = 0 :=
      compact_diffusion_toLp_mean_zero m hνU hU1 hu huc
    have hinner : ⟪F, W⟫ =
        ∫ x, f x * (-weightedLaplacian U u x) ∂(ν : Measure E) :=
      real_inner_toLp hf2 hL
    have hnorm : ‖W‖ ^ 2 =
        ∫ x, weightedLaplacian U u x ^ 2 ∂(ν : Measure E) := by
      simpa only [W, Real.norm_eq_abs, abs_neg, sq_abs] using
        (FunctionalInequalities.L2.norm_toLp_sq hL)
    rw [inner_center_left_of_mean_zero ν F W hmean, hinner, hnorm]
    exact (compact_variational_estimate m hνU hU hPD hf henergy hu huc).2.2
  have hclosure : FunctionalInequalities.L2.center ν F ∈
      closure (compactSmoothDiffusionImage (ν := ν) hU1) :=
    center_mem_closure_compactSmoothDiffusionImage m hν hνU hU1 F
  have hnorm : ‖FunctionalInequalities.L2.center ν F‖ ^ 2 ≤ C :=
    norm_sq_le_of_mem_closure_quadratic_bound
      (FunctionalInequalities.L2.center ν F) hclosure hQ
  have hvariance : (FunctionalInequalities.L2.variance ν F : ℝ) =
      ProbabilityTheory.variance f (ν : Measure E) :=
    (FunctionalInequalities.L2.coe_variance_eq_pointwise ν F).trans
      (ProbabilityTheory.variance_congr hf2.coeFn_toLp)
  rw [← hvariance, FunctionalInequalities.L2.coe_variance]
  exact hnorm

/-- Extended-energy scalar Brascamp--Lieb for a given smooth positive-definite
potential and its actual log-concave probability law. The test is merely `C¹`
and in `L²`. No integrability or finiteness premise is imposed on its energy. -/
theorem scalar_brascamp_lieb_extended_energy
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν)
    {U f : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (ν : Measure E)) :
    ENNReal.ofReal (ProbabilityTheory.variance f (ν : Measure E)) ≤
      ∫⁻ x, ENNReal.ofReal (inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x))) ∂(ν : Measure E) := by
  let e : E → ℝ := fun x => inner ℝ (gradient f x)
    (Ring.inverse (hessianOperator U x) (gradient f x))
  have hU2 : ContDiff ℝ 2 U :=
    hU.of_le (WithTop.coe_le_coe.mpr le_top)
  have hm : AEStronglyMeasurable e (ν : Measure E) :=
    (continuous_inverse_hessian_gradient_energy hU hPD hf).aestronglyMeasurable
  have hn : 0 ≤ᵐ[(ν : Measure E)] e :=
    Filter.Eventually.of_forall fun x =>
      inverse_hessian_gradient_energy_nonneg hU2 hPD x
  change ENNReal.ofReal (ProbabilityTheory.variance f (ν : Measure E)) ≤
    ∫⁻ x, ENNReal.ofReal (e x) ∂(ν : Measure E)
  by_cases ht : (∫⁻ x, ENNReal.ofReal (e x) ∂(ν : Measure E)) = (⊤ : ENNReal)
  · rw [ht]
    exact le_top
  · have hi : Integrable e (ν : Measure E) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hm hn).mp ht
    have hb := scalar_brascamp_lieb_finite_energy m hν hνU hU2 hPD hf hf2 hi
    change ProbabilityTheory.variance f (ν : Measure E) ≤
      ∫ x, e x ∂(ν : Measure E) at hb
    calc
      ENNReal.ofReal (ProbabilityTheory.variance f (ν : Measure E)) ≤
          ENNReal.ofReal (∫ x, e x ∂(ν : Measure E)) :=
        ENNReal.ofReal_le_ofReal hb
      _ = ∫⁻ x, ENNReal.ofReal (e x) ∂(ν : Measure E) := by
        rw [integral_eq_lintegral_of_nonneg_ae hn hm, ENNReal.ofReal_toReal ht]

/-- Bounded `C¹` tests satisfy the extended-energy endpoint: their `L²`
property is derived from the bound and the actual probability law. -/
theorem scalar_brascamp_lieb_extended_energy_of_bounded
    {ν : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν)
    {U f : E → ℝ} (hνU : (ν : Measure E) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ U x v v)
    (hf : ContDiff ℝ 1 f)
    (hbounded : ∃ C : ℝ, ∀ x : E, ‖f x‖ ≤ C) :
    ENNReal.ofReal (ProbabilityTheory.variance f (ν : Measure E)) ≤
      ∫⁻ x, ENNReal.ofReal (inner ℝ (gradient f x)
        (Ring.inverse (hessianOperator U x) (gradient f x))) ∂(ν : Measure E) := by
  obtain ⟨C, hC⟩ := hbounded
  have hf2 : MemLp f 2 (ν : Measure E) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  exact scalar_brascamp_lieb_extended_energy m hν hνU hU hPD hf hf2

end FiniteDimensional

end FunctionalInequalities.KLS.LogConcave

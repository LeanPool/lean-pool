/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Density
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Cumulant
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Basic

/-!
# Derivatives of the logarithmic Laplace transform of the suspension (BKL (111), (112))

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 29. For a regular law
`μ = e^{-V}dx/Z`, `f ∈ C²` with bounded Hessian and `N` chosen by (110), the joint law `ν` of
`(S, X₁, …, X_N)` has a logarithmic Laplace transform `Λ_ν` that is smooth near `0`
(`exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw`) and factorizes
(`logLaplace_jointLaw_factorization`); differentiating the factorization along `e₀` at a point
with vanishing `S`-coordinate gives (111):
`∂_{e₀} Λ_ν(0, z₁, …, z_N) = (σ√N)⁻¹ Σ_i F_f(z_i)`.

The noise factor has zero derivative (`η_β` is centered) and each copy factor is differentiated
through the graph law `(f(x), x)_* μ`. Differentiating `d` more times along copy directions gives
(112), `cumulant_jointLaw_none_entries`: the mixed cumulants `κ^ν_{d+1}(e₀, e_{(i_k, j_k)})` vanish
unless all `i_k` coincide, and then equal `d!/(σ√N) · T_d f(e_{j_1}, …, e_{j_d})`. The helpers
(block selection, local slot calculus, spatial slice) are private to this boundary.

The first-derivative steps are also exposed by `hasDerivAt_log_integral_exp_laplaceMeasure_zero`,
`tiltAverage_inner_eq_fderiv_logLaplace_of_lt` and `hasDerivAt_log_integral_exp_copy`.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-! Private helper lemmas for the first-derivative formula. -/

open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff

private theorem local_laplace_derivative_and_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) {r : ℝ} (hexp : Integrable (fun y => Real.exp (r * ‖y‖)) ν) {q : E}
    (hq : ‖q‖ < r) :
    HasFDerivAt (fun w : E => ∫ y, Real.exp ⟪w, y⟫ ∂ν)
        (∫ y, Real.exp ⟪q, y⟫ • weightedExpD (fun _ : E => (1 : ℝ)) y ∂ν) q ∧
      Integrable (fun y => Real.exp ⟪q, y⟫ • weightedExpD (fun _ : E => (1 : ℝ)) y) ν := by
  have hgi : ∀ t < r, Integrable (fun y : E => Real.exp (t * ‖y‖) * ‖(1 : ℝ)‖) ν := by
    intro t ht
    refine hexp.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with y
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg y))
  have hDgi :=
    weightedExpD_integrable_lt (g := fun _ : E => (1 : ℝ)) measurable_const.aestronglyMeasurable
      hgi
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul, mul_one] using
      weightedExp_integral_hasFDerivAt_of_lt ν measurable_const.aestronglyMeasurable hgi hq
  · refine (hDgi ‖q‖ hq).mono' ?_ ?_
    · exact
        ((by fun_prop : Continuous (fun y : E => Real.exp ⟪q, y⟫)).aestronglyMeasurable).smul
          (weightedExpD_meas measurable_const.aestronglyMeasurable)
    · filter_upwards [] with y
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (real_inner_le_norm q y))
          (norm_nonneg _)

/-- The local mixed first derivative, derived from the actual Euclidean graph norm moment. -/
private theorem graph_log_integral_hasDerivAt_zero {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {r : ℝ} (_hr : 0 < r)
    (hexp :
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
        (μ.map
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
              EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ)) (tiltAverage μ f z)
      0 := by
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Option (Fin n)) := fun x =>
    WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j
  let Γ := μ.map g
  have hgm : Measurable g := by
    dsimp [g]
    apply (WithLp.measurable_toLp 2 _).comp
    rw [measurable_pi_iff]
    intro o
    cases o with
    | none => exact hf
    | some j => exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  let _ : IsProbabilityMeasure Γ := (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 inferInstance
  let q : EuclideanSpace ℝ (Option (Fin n)) :=
    WithLp.toLp 2 fun o => Option.elim o 0 fun j => z j
  let e0 : EuclideanSpace ℝ (Option (Fin n)) := EuclideanSpace.basisFun (Option (Fin n)) ℝ none
  have hqnorm : ‖q‖ = ‖z‖ := by
    have hsq : ‖q‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
      change (0 : ℝ) ^ 2 + ∑ j : Fin n, (z j) ^ 2 = ‖z‖ ^ 2
      rw [← EuclideanSpace.real_norm_sq_eq]
      norm_num
    nlinarith [norm_nonneg q, norm_nonneg z]
  have hq : ‖q‖ < r := hqnorm.trans_lt hz
  obtain ⟨hZ, hDint⟩ := local_laplace_derivative_and_integrable Γ hexp hq
  let D : EuclideanSpace ℝ (Option (Fin n)) →L[ℝ] ℝ :=
    ∫ y,
      Real.exp ⟪q, y⟫ • weightedExpD (fun _ : EuclideanSpace ℝ (Option (Fin n)) => (1 : ℝ)) y ∂Γ
  have hinner (w : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ⟪w • e0 + q, g x⟫ = w * f x + ⟪z, x⟫ := by
    simp [g, q, e0, PiLp.inner_apply, Fintype.sum_option, mul_comm]
  have hmap (w : ℝ) :
    (∫ y, Real.exp ⟪w • e0 + q, y⟫ ∂Γ) = ∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ := by
    dsimp [Γ]
    rw [integral_map hgm.aemeasurable
        ((by fun_prop :
            Continuous
              (fun y : EuclideanSpace ℝ (Option (Fin n)) =>
                Real.exp ⟪w • e0 + q, y⟫)).aestronglyMeasurable)]
    simp_rw [hinner]
  have hNumΓ : Integrable (fun y => Real.exp ⟪q, y⟫ * y none) Γ := by
    have he := (ContinuousLinearMap.apply ℝ ℝ e0).integrable_comp hDint
    change
      Integrable
        (fun y =>
          (Real.exp ⟪q, y⟫ •
              weightedExpD (fun _ : EuclideanSpace ℝ (Option (Fin n)) => (1 : ℝ)) y)
            e0)
        Γ at he
    simpa only [smul_apply, weightedExpD, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, smul_eq_mul, mul_one, e0, EuclideanSpace.inner_basisFun_real] using
      he
  have hDe0 : D e0 = ∫ x, Real.exp ⟪z, x⟫ * f x ∂μ := by
    dsimp [D]
    rw [ContinuousLinearMap.integral_apply hDint]
    simp only [smul_apply, weightedExpD, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, smul_eq_mul, mul_one, e0, EuclideanSpace.inner_basisFun_real]
    dsimp [Γ]
    rw [integral_map hgm.aemeasurable hNumΓ.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with x
    have hi : ⟪q, g x⟫ = ⟪z, x⟫ := by simpa using hinner 0 x
    rw [hi]
    rfl
  have hline : HasDerivAt (fun w : ℝ => w • e0 + q) e0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).add_const q
  have hZline : HasDerivAt (fun w : ℝ => ∫ y, Real.exp ⟪w • e0 + q, y⟫ ∂Γ) (D e0) 0 := by
    have hZ' : HasFDerivAt (fun v => ∫ y, Real.exp ⟪v, y⟫ ∂Γ) D ((0 : ℝ) • e0 + q) := by
      simpa only [zero_smul, zero_add] using hZ
    exact hZ'.comp_hasDerivAt 0 hline
  have hQ :
    HasDerivAt (fun w : ℝ => ∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ * f x ∂μ) 0 := by
    simpa only [hmap, hDe0] using hZline
  have hZint : Integrable (fun y => Real.exp ⟪q, y⟫) Γ := by
    refine
      hexp.mono'
        ((by fun_prop :
            Continuous
              (fun y : EuclideanSpace ℝ (Option (Fin n)) =>
                Real.exp ⟪q, y⟫)).aestronglyMeasurable)
        ?_
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact
      Real.exp_le_exp.mpr
        ((real_inner_le_norm q y).trans (mul_le_mul_of_nonneg_right hq.le (norm_nonneg y)))
  have hZpos : 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
    have hp := integral_exp_pos hZint
    have heq : (∫ y, Real.exp ⟪q, y⟫ ∂Γ) = ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      simpa only [zero_smul, zero_add, zero_mul, zero_add] using hmap 0
    rwa [heq] at hp
  have htilt :
    tiltAverage μ f z = (∫ x, Real.exp ⟪z, x⟫ * f x ∂μ) / (∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul, div_eq_mul_inv]
    rw [show
        (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * f x) =
          (fun x => (Real.exp ⟪z, x⟫ * f x) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹)
        by funext x; ring,
      integral_mul_const]
  simpa only [zero_mul, zero_add, ← htilt] using
    hQ.log (by simpa only [zero_mul, zero_add] using hZpos.ne')

/-- Scalar rescaling of the actual local graph derivative; no differentiability premise. -/
private theorem graph_log_integral_hasDerivAt_scaled {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) (c : ℝ) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp ((c * w) * f x + ⟪z, x⟫) ∂μ))
      (c * tiltAverage μ f z) 0 := by
  have hbase := graph_log_integral_hasDerivAt_zero μ hf hr hexp z hz
  have hbase' : HasDerivAt
      (fun v : ℝ => Real.log (∫ x, Real.exp (v * f x + ⟪z, x⟫) ∂μ))
      (tiltAverage μ f z) (c * (0 : ℝ)) := by simpa only [mul_zero] using hbase
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hbase'.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul c)

/-- The source copy coefficient in (111), with beta>0 and N>0 retained. -/
private theorem source_copy_log_integral_hasDerivAt {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (_hβ : 0 < β) (_hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp
        (w / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
          ⟪z, x⟫) ∂μ))
      (tiltAverage μ f z /
        (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)) 0 := by
  have h := graph_log_integral_hasDerivAt_scaled μ hf hr hexp z hz
    ((FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The actual source Laplace-noise log factor has derivative zero, from its proved mean. -/
private theorem source_noise_log_integral_hasDerivAt {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun w : ℝ => Real.log (∫ s : ℝ, Real.exp
      (w / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s)
        ∂FunctionalInequalities.Probability.Line.laplaceMeasure β)) 0 0 := by
  open FunctionalInequalities.Probability.Line in
  let _ : IsProbabilityMeasure (laplaceMeasure β) := isProbabilityMeasure_laplaceMeasure hβ
  have hmgf : HasDerivAt (ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β)) 0 0 := by
    have h := ProbabilityTheory.hasDerivAt_mgf (X := id)
      (FunctionalInequalities.Probability.Line.zero_mem_interior_integrableExpSet_laplaceMeasure hβ)
    simpa only [zero_mul, Real.exp_zero, mul_one, id_eq,
      FunctionalInequalities.Probability.Line.integral_id_laplaceMeasure hβ] using h
  have hval : ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β) 0 = 1 := by
    simp [ProbabilityTheory.mgf]
  have hlog : HasDerivAt (fun v : ℝ => Real.log (ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β) v)) 0 0 := by
    simpa only [hval, zero_div] using hmgf.log (by rw [hval]; norm_num)
  have hlog' : HasDerivAt (fun v : ℝ => Real.log (ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β) v)) 0
      ((0 : ℝ) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) := by
    simpa only [zero_div] using hlog
  simpa only [Function.comp_def, ProbabilityTheory.mgf, id_eq, zero_mul] using
    hlog'.comp 0 ((hasDerivAt_id (0 : ℝ)).div_const
      (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β))

open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology

private theorem copy_parameter_norm_le {n N : ℕ} (z : JointSpace N n) (i : Fin N) :
    ‖(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖z‖ := by
  let zi : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun j => z (some (i, j))
  have hi : ‖zi‖ ^ 2 = ∑ j : Fin n, z (some (i, j)) ^ 2 := EuclideanSpace.real_norm_sq_eq zi
  have hz : ‖z‖ ^ 2 = z none ^ 2 + ∑ k : Fin N, ∑ j : Fin n, z (some (k, j)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option, Fintype.sum_prod_type]
  have hle : (∑ j : Fin n, z (some (i, j)) ^ 2) ≤
      ∑ k : Fin N, ∑ j : Fin n, z (some (k, j)) ^ 2 :=
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (f := fun k : Fin N => ∑ j : Fin n, z (some (k, j)) ^ 2)
      (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (z (some (k, j)))) (Finset.mem_univ i)
  change ‖zi‖ ≤ ‖z‖
  nlinarith [hi, hz, sq_nonneg (z none), norm_nonneg zi, norm_nonneg z]

private theorem integrable_exp_inner_of_norm_radius {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E) {r : ℝ}
    (hexp : Integrable (fun p => Real.exp (r * ‖p‖)) ν) (q : E) (hq : ‖q‖ ≤ r) :
    Integrable (fun p => Real.exp ⟪q, p⟫) ν := by
  refine
    hexp.mono' ((by fun_prop : Continuous (fun p : E => Real.exp ⟪q, p⟫)).aestronglyMeasurable)
      ?_
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact
    Real.exp_le_exp.mpr
      ((real_inner_le_norm q p).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg p)))

/-- Full actual joint-law HasDerivAt identity (111), under genuine local analytic radii. -/
private theorem joint_first_derivative_of_radii {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β rJ rG : ℝ} (hβ : 0 < β) (hN : 0 < N) (_hrJ : 0 < rJ) (hrG : 0 < rG)
    (hjoint : Integrable (fun p : JointSpace N n => Real.exp (rJ * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hgraph : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (rG * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : JointSpace N n) (hzero : z none = 0) (hz : ‖z‖ < min rJ rG) :
    HasDerivAt (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N)
        (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
      ((∑ i : Fin N, tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  let e0 : JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  let noise : ℝ → ℝ := fun w => Real.log
    (∫ s : ℝ, Real.exp (w / sigma β * s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β)
  let copy : Fin N → ℝ → ℝ := fun i w => Real.log (∫ x, Real.exp
    (w / (sigma β * Real.sqrt N) * f x +
      ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ)
  have hzJ : ‖z‖ < rJ := hz.trans_le (min_le_left rJ rG)
  have hzG : ‖z‖ < rG := hz.trans_le (min_le_right rJ rG)
  have hsmall : ∀ᶠ w : ℝ in 𝓝 0, ‖w • e0 + z‖ < rJ := by
    have hc : Continuous (fun w : ℝ => ‖w • e0 + z‖) := by fun_prop
    exact (hc.tendsto 0).eventually_lt_const (by simpa only [zero_smul, zero_add] using hzJ)
  have hnone (w : ℝ) : (w • e0 + z) none = w := by simp [e0, hzero]
  have hcopyparam (w : ℝ) (i : Fin N) :
      (WithLp.toLp 2 fun j => (w • e0 + z) (some (i, j)) : EuclideanSpace ℝ (Fin n)) =
        WithLp.toLp 2 (fun j => z (some (i, j))) := by
    ext j
    simp [e0]
  have heq :
      (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N) (w • e0 + z)) =ᶠ[𝓝 0]
        fun w => noise w + ∑ i : Fin N, copy i w := by
    filter_upwards [hsmall] with w hw
    have hint := integrable_exp_inner_of_norm_radius (jointLaw μ f β (sigma β) N)
      hjoint (w • e0 + z) hw.le
    have h := logLaplace_jointLaw_factorization μ hf hβ hN (w • e0 + z) hint
    simpa only [hnone, hcopyparam, noise, copy] using h
  have hNoise : HasDerivAt noise 0 0 :=
    source_noise_log_integral_hasDerivAt hβ
  have hCopy (i : Fin N) : HasDerivAt (copy i)
      (tiltAverage μ f (WithLp.toLp 2 fun j => z (some (i, j))) / (sigma β * Real.sqrt N)) 0 :=
    source_copy_log_integral_hasDerivAt μ hf hβ hN hrG hgraph
      (WithLp.toLp 2 fun j => z (some (i, j)))
      ((copy_parameter_norm_le z i).trans_lt hzG)
  have hSum : HasDerivAt (fun w : ℝ => ∑ i : Fin N, copy i w)
      (∑ i : Fin N, tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j))) / (sigma β * Real.sqrt N)) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hCopy i)
  have hRHS : HasDerivAt (fun w : ℝ => noise w + ∑ i : Fin N, copy i w)
      ((∑ i : Fin N, tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
    simpa only [zero_add, Finset.sum_div] using hNoise.fun_add hSum
  exact hRHS.congr_of_eventuallyEq heq

/-- Source-path entry: graph moments are derived internally from the actual joint and mu radii. -/
private theorem exists_joint_first_derivative_neighborhood {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r s : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r) (hs : 0 < s)
    (hjoint : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hμ : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : JointSpace N n, z none = 0 → ‖z‖ < δ →
      HasDerivAt (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N)
          (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
        ((∑ i : Fin N, tiltAverage μ f
          (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  obtain ⟨rG, hrG, hgraph⟩ := exists_graph_norm_moment_from_joint μ hf hβ hN hr hs hjoint hμ
  refine ⟨min r rG, lt_min hr hrG, ?_⟩
  intro z hz0 hz
  exact joint_first_derivative_of_radii μ hf hβ hN hr hrG hjoint hgraph z hz0 hz

open FunctionalInequalities
open scoped ContDiff

/-- The actual source construction supplies both radii: no joint, graph or f moment premise.
This is the chosen-positive-N local germ (111), retaining the source condition (110). -/
private theorem source_joint_first_derivative {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hNpos : 0 < N) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hN : β / Real.sqrt N * M ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : JointSpace N n, z none = 0 → ‖z‖ < δ →
      HasDerivAt (fun w : ℝ => logLaplace
          (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)
          (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
        ((∑ i : Fin N, tiltAverage (volume.tilted fun x => -V x) f
          (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted fun x => -V x
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hint
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ⟨μ, inferInstance⟩
  have hμlc : KLS.LogConcave ν :=
    KLS.LogConcave.logConcave_of_eq_tilted (ν := ν) rfl hV.continuous
      (convexOn_of_hessian_ge hV ha.le hVa)
  obtain ⟨s, hs, hμ, _⟩ := hμlc.exists_integrable_exp_norm_contDiffOn_logLaplace
  obtain ⟨r, hr, hjoint, _⟩ := exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV hf hVa hfM hN hint
  exact exists_joint_first_derivative_neighborhood μ
    hf.continuous.measurable hβ hNpos hr hs hjoint hμ

/-- **BKL (111)** for the source's chosen `N`. -/
theorem fderiv_logLaplace_jointLaw_none {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
    (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a) :
    ∃ r > 0, ∀ z : JointSpace N n, ‖z‖ < r → z none = 0 →
      fderiv ℝ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z
          (EuclideanSpace.single none 1) =
        (sigma β * Real.sqrt N)⁻¹ *
          ∑ i, tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j))) := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hint : Integrable (fun x => Real.exp (-V x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hV.integrable_exp_neg
  obtain ⟨δ, hδ, h111⟩ := source_joint_first_derivative
    V f hV.pos hβ hN hV2 hf hint hV.lower hfM h110
  obtain ⟨r, hr, _, hcd⟩ := exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
    V f hβ hV2 hf hV.lower hfM h110 hint
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro z hz hz0
  have hzδ : ‖z‖ < δ := hz.trans_le (min_le_left δ r)
  have hzr : ‖z‖ < r := hz.trans_le (min_le_right δ r)
  have hdiff : DifferentiableAt ℝ
      (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z := by
    apply (hcd.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hzr))).differentiableAt
    simp
  let e0 : JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  have hline : HasDerivAt (fun w : ℝ => w • e0 + z) e0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).add_const z
  have hF : HasFDerivAt (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N))
      (fderiv ℝ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z)
      ((fun w : ℝ => w • e0 + z) 0) := by simpa using hdiff.hasFDerivAt
  have hd := hF.comp_hasDerivAt 0 hline
  have heq := hd.unique (h111 z hz0 hzδ)
  have hμeq : (hV.law : Measure _) = volume.tilted (fun x => -V x) := rfl
  simpa only [hμeq, e0, EuclideanSpace.basisFun_apply, div_eq_mul_inv, mul_comm] using heq

/-! ### (112): mixed cumulants with one `e₀` direction -/

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Local continuous-linear restriction of an iterated derivative. -/
private theorem iteratedFDeriv_comp_clm_at {f : E → F} (L : G →L[ℝ] E)
    {x : G} {d : ℕ} (hf : ContDiffAt ℝ d f (L x)) :
    iteratedFDeriv ℝ d (f ∘ L) x =
      (iteratedFDeriv ℝ d f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn' le_rfl (by simp)
  have hfU' : ContDiffOn ℝ d f U := by simpa using hfU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hfU' hU.uniqueDiffOn
    hpre.uniqueDiffOn hxU (i := d) le_rfl
  rw [iteratedFDerivWithin_of_isOpen d hpre hxU,
    iteratedFDerivWithin_of_isOpen d hU hxU] at h
  exact h

section FiniteIndex

variable {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- Each summand sees only its own copy. -/
private theorem iteratedFDeriv_copy_apply
    (f : E → F) (i : ι) (x : ι → E) {d : ℕ}
    (hf : ContDiffAt ℝ d f (x i)) (labels : Fin d → ι) (v : Fin d → E) :
    iteratedFDeriv ℝ d (fun y : ι → E => f (y i)) x
      (fun k => Pi.single (labels k) (v k)) =
      if ∀ k, labels k = i then iteratedFDeriv ℝ d f (x i) v else 0 := by
  classical
  have h := iteratedFDeriv_comp_clm_at
    (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E) (x := x) hf
  change iteratedFDeriv ℝ d
    (f ∘ (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)) x _ = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.proj_apply]
  split_ifs with hi
  · congr 1
    funext k
    simp [hi k]
  · obtain ⟨k, hk⟩ := not_forall.mp hi
    exact (iteratedFDeriv ℝ d f (x i)).map_coord_zero k (by simp [Ne.symm hk])

/-- Positive-order derivatives select a single copy precisely when every label agrees.
Repeated labels and repeated vector directions are retained in the multilinear evaluation. -/
private theorem iteratedFDeriv_sum_copies_select
    (f : ι → E → F) (x : ι → E) (d : ℕ) (k0 : Fin d)
    (hf : ∀ i, ContDiffAt ℝ d (f i) (x i))
    (labels : Fin d → ι) (v : Fin d → E) :
    iteratedFDeriv ℝ d (fun y : ι → E => ∑ i, f i (y i)) x
      (fun k => Pi.single (labels k) (v k)) =
      if ∀ k, labels k = labels k0 then
        iteratedFDeriv ℝ d (f (labels k0)) (x (labels k0)) v else 0 := by
  classical
  have hsum := iteratedFDeriv_fun_sum_apply (u := Finset.univ)
    (f := fun i (y : ι → E) => f i (y i)) (x := x) (n := d)
    (fun i _ => (hf i).comp x
      (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).contDiff.contDiffAt)
  rw [hsum]
  simp only [sum_apply]
  simp_rw [iteratedFDeriv_copy_apply _ _ _ (hf _)]
  split_ifs with hsame
  · rw [Finset.sum_eq_single (labels k0)]
    · simp [hsame]
    · intro i _ hi
      have hnot : ¬ ∀ k, labels k = i := fun h => hi (h k0).symm
      simp [hnot]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hnot : ¬ ∀ k, labels k = i := by
      intro hi
      exact hsame (fun k => (hi k).trans (hi k0).symm)
    simp [hnot]

end FiniteIndex

/-! Local symmetry and the mixed-derivative bridge in BKL (112).
The function is smooth on an open neighborhood, not on the whole ambient space. -/

open Filter Set
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local exchange of the first two directions; all remaining directions are retained. -/
private theorem iteratedFDeriv_swap_front_on {g : E → F} {U : Set E}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v w : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) g x (Fin.cons v (Fin.cons w h)) =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons w (Fin.cons v h)) := by
  have hgat : ContDiffAt ℝ ∞ g x := (hg x hx).contDiffAt (hU.mem_nhds hx)
  have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ n g) x :=
    hgat.iteratedFDeriv_right (m := ∞) (by norm_cast)
  have ha : ContDiffAt ℝ ∞ (fun y => iteratedFDeriv ℝ n g y h) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F h).contDiff.contDiffAt.comp x hd
  have heq (a : E) :
      (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons a h)) =ᶠ[𝓝 x]
        fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ n g z h) y a := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hd' := ((hg y hy).contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right
      (i := n) (m := ∞) (by norm_cast)
    simpa using (hd'.differentiableAt (by simp)).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons a h)
  have hleft :=
    (hgat.differentiableAt_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp)).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons v (Fin.cons w h))
  have hright :=
    (hgat.differentiableAt_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp)).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons w (Fin.cons v h))
  rw [hleft, hright]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [(heq w).fderiv_eq, (heq v).fderiv_eq]
  rw [fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiableAt (by norm_num))
      (differentiableAt_const w),
    fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiableAt (by norm_num))
      (differentiableAt_const v)]
  simpa using (ha.isSymmSndFDerivAt (by simp)).eq v w

/-- Move the distinguished direction from the first to the last slot locally. -/
private theorem iteratedFDeriv_cons_snoc_on {g : E → F} {U : Set E}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g x (Fin.cons v h) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc h v) := by
  induction n generalizing x with
  | zero =>
      congr 1
      ext i
      fin_cases i
      simp [Fin.snoc_zero]
  | succ n ih =>
      have hgat : ContDiffAt ℝ ∞ g x := (hg x hx).contDiffAt (hU.mem_nhds hx)
      rw [← Fin.cons_self_tail h]
      rw [iteratedFDeriv_swap_front_on hg hU n x hx v (h 0) (Fin.tail h)]
      rw [← Fin.cons_snoc_eq_snoc_cons]
      have heq :
          (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons v (Fin.tail h))) =ᶠ[𝓝 x]
            fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.snoc (Fin.tail h) v) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih y hy (Fin.tail h)
      rw [(hgat.differentiableAt_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp)).iteratedFDeriv_succ_apply_left',
        (hgat.differentiableAt_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp)).iteratedFDeriv_succ_apply_left']
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun a : E →L[ℝ] F => a (h 0)) heq.fderiv_eq

/-- Derivatives of the local first directional derivative are mixed higher derivatives,
with the distinguished vector in the source's first slot. -/
private theorem iteratedFDeriv_directional_on {g : E → F} {U : Set E}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (d : ℕ) (x : E) (hx : x ∈ U) (v : E) (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun y => fderiv ℝ g y v) x h =
      iteratedFDeriv ℝ (d + 1) g x (Fin.cons v h) := by
  have hgat : ContDiffAt ℝ ∞ g x := (hg x hx).contDiffAt (hU.mem_nhds hx)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) x := hgat.fderiv_right (by simp)
  have heval := (ContinuousLinearMap.apply ℝ F v).iteratedFDeriv_comp_left hd
    (i := d) (by norm_cast; simp)
  have hs := iteratedFDeriv_cons_snoc_on hg hU d x hx v h
  have ht := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := g) (x := x) (Fin.snoc h v)
  simp only [Fin.init_snoc, Fin.snoc_last] at ht
  rw [ht] at hs
  have heval' : iteratedFDeriv ℝ d (fun y => fderiv ℝ g y v) x h =
      iteratedFDeriv ℝ d (fderiv ℝ g) x h v := by
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_def, ContinuousLinearMap.apply_apply] using
      congrArg (fun a : E [×d]→L[ℝ] F => a h) heval
  exact heval'.trans hs.symm

/-! Higher mixed derivatives follow from the separately proved first-derivative germ;
no mixed derivative identity is assumed. -/

open scoped ContDiff Topology
open Filter Set

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

section FiniteIndex

variable {ι : Type*}
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Smoothness of a separated copy sum at zero implies smoothness of each summand at zero.
The other copies contribute only a constant after a single-copy linear restriction. -/
private theorem contDiffAt_component_of_copy_sum
    (F : ι → E → ℝ) {d : ℕ}
    (hF : ContDiffAt ℝ d (fun y : ι → E => ∑ j, F j (y j)) 0) (i : ι) :
    ContDiffAt ℝ d (F i) 0 := by
  classical
  have hr : ContDiffAt ℝ d (fun t : E => ∑ j, F j ((Pi.single i t : ι → E) j)) 0 := by
    let L : E →L[ℝ] (ι → E) := ContinuousLinearMap.single ℝ (fun _ : ι => E) i
    have hF' : ContDiffAt ℝ d (fun y : ι → E => ∑ j, F j (y j)) (L 0) := by
      simpa using hF
    simpa [L, Function.comp_def] using hF'.comp 0 L.contDiff.contDiffAt
  let c : ℝ := ∑ j ∈ Finset.univ.erase i, F j 0
  have hsplit (t : E) : (∑ j, F j ((Pi.single i t : ι → E) j)) = c + F i t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hji]
    · simp
  have hsub := hr.sub (contDiffAt_const (c := c))
  convert hsub using 1
  funext t
  rw [hsplit]
  ring

omit [DecidableEq ι] in
/-- A nonzero scalar multiple of a separated sum can be peeled without any integrability input. -/
private theorem contDiffAt_component_of_scaled_copy_sum
    (F : ι → E → ℝ) {d : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hF : ContDiffAt ℝ d (fun y : ι → E => c * ∑ j, F j (y j)) 0) (i : ι) :
    ContDiffAt ℝ d (F i) 0 := by
  classical
  have hprod := (contDiffAt_const (c := c⁻¹)).mul hF
  have hsum : ContDiffAt ℝ d (fun y : ι → E => ∑ j, F j (y j)) 0 := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hprod
  exact contDiffAt_component_of_copy_sum F hsum i

/-- Local (111) on a linear spatial slice implies the finite-copy mixed derivative rule. -/
private theorem mixed_copies_from_first_derivative_germ (g : G → ℝ) (L : (ι → E) →L[ℝ] G)
    (e : G) (F : ι → E → ℝ) (c : ℝ) (x : ι → E) {U : Set G} (hU : IsOpen U) (hx : L x ∈ U)
    (hg : ContDiffOn ℝ ∞ g U) (d : ℕ) (k0 : Fin d) (hF : ∀ i, ContDiffAt ℝ d (F i) (x i))
    (hfirst : (fun y => fderiv ℝ g (L y) e) =ᶠ[𝓝 x] fun y => c * ∑ i, F i (y i))
    (labels : Fin d → ι) (v : Fin d → E) :
    iteratedFDeriv ℝ (d + 1) g (L x) (Fin.cons e (fun k => L (Pi.single (labels k) (v k)))) =
      if ∀ k, labels k = labels k0 then c * iteratedFDeriv ℝ d (F (labels k0)) (x (labels k0)) v
      else 0 := by
  classical
  let q : Fin d → ι → E := fun k => Pi.single (labels k) (v k)
  have hgat : ContDiffAt ℝ ∞ g (L x) := (hg (L x) hx).contDiffAt (hU.mem_nhds hx)
  have hdirectional : ContDiffAt ℝ d (fun y => fderiv ℝ g y e) (L x) := by
    exact
      ((ContinuousLinearMap.apply ℝ ℝ e).contDiff.contDiffAt.comp (L x)
            (hgat.fderiv_right (m := ∞) (by simp))).of_le
        (by norm_cast; simp)
  have hrestrict := iteratedFDeriv_comp_clm_at L hdirectional
  have hrestrict' :
    iteratedFDeriv ℝ d (fun y => fderiv ℝ g (L y) e) x q =
      iteratedFDeriv ℝ d (fun y => fderiv ℝ g y e) (L x) (fun k => L (q k)) := by
    simpa only [Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply] using
      congrArg (fun a => a q) hrestrict
  have hmixed := iteratedFDeriv_directional_on hg hU d (L x) hx e (fun k => L (q k))
  have heq := (hfirst.iteratedFDeriv ℝ d).self_of_nhds
  have hsum : ContDiffAt ℝ d (fun y : ι → E => ∑ i, F i (y i)) x := by
    exact
      ContDiffAt.sum
        (fun i _ =>
          (hF i).comp x (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E).contDiff.contDiffAt)
  have hscale := iteratedFDeriv_const_smul_apply' (a := c) hsum
  have hscale' :
    iteratedFDeriv ℝ d (fun y : ι → E => c * ∑ i, F i (y i)) x q =
      c * iteratedFDeriv ℝ d (fun y : ι → E => ∑ i, F i (y i)) x q := by
    simpa only [smul_eq_mul, smul_apply] using congrArg (fun a => a q) hscale
  calc
    _ = iteratedFDeriv ℝ d (fun y => fderiv ℝ g (L y) e) x q := (hrestrict'.trans hmixed).symm
    _ = iteratedFDeriv ℝ d (fun y : ι → E => c * ∑ i, F i (y i)) x q :=
      congrArg (fun a => a q) heq
    _ = c * iteratedFDeriv ℝ d (fun y : ι → E => ∑ i, F i (y i)) x q := hscale'
    _ = _ := by
      rw [iteratedFDeriv_sum_copies_select F x d k0 hF labels v]
      split_ifs <;> simp

end FiniteIndex

/--
Actual spatial slice in the source's joint space: auxiliary coordinate zero, copies intact. -/
noncomputable def jointSpatialSlice (N n : ℕ) :
    (Fin N → EuclideanSpace ℝ (Fin n)) →L[ℝ]
      FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n :=
  (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Option (Fin N × Fin n) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun o =>
      match o with
      | none => 0
      | some ij => (EuclideanSpace.proj ij.2).comp (ContinuousLinearMap.proj ij.1))

@[simp] theorem jointSpatialSlice_none {N n : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin n)) :
    jointSpatialSlice N n x none = 0 := rfl

@[simp] theorem jointSpatialSlice_some {N n : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin n))
    (i : Fin N) (j : Fin n) : jointSpatialSlice N n x (some (i, j)) = x i j := rfl

private theorem jointSpatialSlice_single {N n : ℕ} (i : Fin N) (j : Fin n) :
    jointSpatialSlice N n (Pi.single i (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      EuclideanSpace.single (some (i, j)) 1 := by
  ext o
  cases o with
  | none => simp
  | some ij =>
      rcases ij with ⟨i', j'⟩
      by_cases hi : i' = i
      · subst i'
        simp [EuclideanSpace.basisFun_apply]
      · simp [hi, EuclideanSpace.basisFun_apply, Prod.ext_iff]

/-! BKL (112) follows from the first-derivative identity (111) by higher differentiation
and the factorial calculation in the original regular-law setting. No separate L2 premise is needed.
This does not assert Proposition 7.1's final operator inequality. -/

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace ContDiff Topology

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
/--
BKL (112), derived from actual local (111), local smoothness of the actual joint log-Laplace,
and the finite-copy derivative selection rule. The same-copy tensor retains all repeated slots. -/
theorem cumulant_jointLaw_none_entries {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
    (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a) {d : ℕ} (hd : 1 ≤ d) (I : Fin d → Fin N)
    (J : Fin d → Fin n) :
    cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
        (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (I k, J k)) 1) =
      if ∀ k k', I k = I k' then
        (d.factorial : ℝ) / (sigma β * Real.sqrt N) *
          taylorTensor (hV.law : Measure _) f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
      else 0 := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := hV.law
  let ν : Measure (JointSpace N n) := jointLaw μ f β (sigma β) N
  let L := jointSpatialSlice N n
  let k0 : Fin d := ⟨0, by omega⟩
  have hμeq : μ = volume.tilted (fun x => -V x) := rfl
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨r, hr, _, hcd⟩ :=
    exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw V f hβ hV2 hf hV.lower hfM h110
      hV.integrable_exp_neg
  have hcd' : ContDiffOn ℝ ∞ (logLaplace ν) (Metric.ball 0 r) := by
    simpa only [ν, hμeq] using hcd
  obtain ⟨δ, hδ, h111⟩ := fderiv_logLaplace_jointLaw_none hN V hV hβ hf hfM h110
  have hfirst :
    (fun y => fderiv ℝ (logLaplace ν) (L y) (EuclideanSpace.single none 1)) =ᶠ[𝓝 0]
      fun y : Fin N → EuclideanSpace ℝ (Fin n) =>
      (sigma β * Real.sqrt N)⁻¹ * ∑ i, tiltAverage μ f (y i) := by
    have hpre : L ⁻¹' Metric.ball 0 δ ∈ 𝓝 0 :=
      (Metric.isOpen_ball.preimage L.continuous).mem_nhds (by simp [hδ])
    filter_upwards [hpre] with y hy
    have hyδ : ‖L y‖ < δ := by simpa using hy
    have heq := h111 (L y) hyδ (jointSpatialSlice_none y)
    simpa only [ν, μ, L, jointSpatialSlice_some, WithLp.toLp_ofLp] using heq
  have hF :
    ∀ i : Fin N, ContDiffAt ℝ d (tiltAverage μ f) ((0 : Fin N → EuclideanSpace ℝ (Fin n)) i) := by
    intro i
    have hgat : ContDiffAt ℝ ∞ (logLaplace ν) (L 0) := by
      simpa using hcd'.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
    have hdir :
      ContDiffAt ℝ d (fun y => fderiv ℝ (logLaplace ν) (L y) (EuclideanSpace.single none 1))
        0 := by
      have hdirinf :
        ContDiffAt ℝ ∞ (fun y => fderiv ℝ (logLaplace ν) (L y) (EuclideanSpace.single none 1))
          0 := by
        simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
          ((ContinuousLinearMap.apply ℝ ℝ
                    (EuclideanSpace.single none 1)).contDiff.contDiffAt.comp
                (L 0) (hgat.fderiv_right (m := ∞) (by simp))).comp
            0 L.contDiff.contDiffAt
      exact hdirinf.of_le (by norm_cast; simp)
    have hscaled :
      ContDiffAt ℝ d
        (fun y : Fin N → EuclideanSpace ℝ (Fin n) =>
          (sigma β * Real.sqrt N)⁻¹ * ∑ j, tiltAverage μ f (y j))
        0 :=
      hdir.congr_of_eventuallyEq hfirst.symm
    have hσ : 0 < sigma β := by
      apply Real.sqrt_pos.mpr
      positivity
    have hc : (sigma β * Real.sqrt N)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne')
    exact
      contDiffAt_component_of_scaled_copy_sum (fun _ : Fin N => tiltAverage μ f) hc hscaled i
  have hmixed :=
    mixed_copies_from_first_derivative_germ (logLaplace ν) L (EuclideanSpace.single none 1)
      (fun _ : Fin N => tiltAverage μ f) ((sigma β * Real.sqrt N)⁻¹) 0 Metric.isOpen_ball
      (by simpa using hr) hcd' d k0 hF hfirst I
      (fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
  have hsame : (∀ k, I k = I k0) ↔ (∀ k k', I k = I k') := by
    constructor
    · intro h k k'
      exact (h k).trans (h k').symm
    · intro h k
      exact h k k0
  simp only [L, map_zero, jointSpatialSlice_single, Pi.zero_apply, hsame] at hmixed
  change iteratedFDeriv ℝ (d + 1) (logLaplace ν) 0 _ = _
  rw [hmixed]
  split_ifs
  · have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    simp only [taylorTensor, smul_apply, smul_eq_mul, div_eq_mul_inv]
    field_simp [hfac]
    rfl
  · rfl

end FunctionalInequalities.KLS.LogConcave.Suspension

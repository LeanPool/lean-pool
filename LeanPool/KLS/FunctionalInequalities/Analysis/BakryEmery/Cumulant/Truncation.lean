/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
public import Mathlib.Probability.ConditionalProbability

/-!
# Cumulants of ball truncations converge

For a probability measure with one exponential moment `∫ e^{r‖x‖} < ∞`, the cumulants of the
conditional laws on
the balls `B(0, R)` converge to its cumulants as `R → ∞` (`tendsto_cumulant_cond_closedBall`):
cumulants are a fixed
continuous function (Faà di Bruno, `FormalMultilinearSeries.taylorComp`) of the moment jets at `0`,
and the
truncated moment tensors converge. Used to reduce BKL arXiv:2610.05474v1, Theorem 4.1, to compactly
supported laws
(p. 19, end of Section 6).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

section CondHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Operator-norm distance between the moment tensors of `ν[|s]` and `ν`. -/
theorem norm_iteratedFDeriv_laplace_cond_sub_le (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ)
    {s : Set E} (hs : MeasurableSet s) (hs0 : ν s ≠ 0) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|s])) 0 -
        iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0‖ ≤
      |((ν s)⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν := by
  have : IsProbabilityMeasure (ν[|s]) := cond_isProbabilityMeasure hs0
  have hexp' : Integrable (fun x => Real.exp (r * ‖x‖)) (ν[|s]) :=
    (hexp.restrict (s := s)).smul_measure (ENNReal.inv_ne_top.2 hs0)
  have hpow := FunctionalInequalities.Probability.integrable_norm_pow_of_exp ν hr hexp d
  have hM : 0 ≤ ∫ x, ‖x‖ ^ d ∂ν := integral_nonneg fun x => by positivity
  have he : 0 ≤ ∫ x in sᶜ, ‖x‖ ^ d ∂ν := integral_nonneg fun x => by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun h => ?_
  rw [sub_apply, iteratedFDeriv_laplace_zero (ν[|s]) hr hexp' d h,
    iteratedFDeriv_laplace_zero ν hr hexp d h]
  have hint := FunctionalInequalities.Probability.integrable_prod_inner_of_exp ν hr hexp d h
  have hP : 0 ≤ ∏ j, ‖h j‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
  have hcond : ∫ x, ∏ j, ⟪x, h j⟫ ∂(ν[|s]) =
      ((ν s)⁻¹).toReal * ∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν := by
    simp only [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
  have hsplit := integral_add_compl hs hint
  have hbound : ∀ᵐ x ∂ν, ‖∏ j, ⟪x, h j⟫‖ ≤ ‖x‖ ^ d * ∏ j, ‖h j‖ :=
    ae_of_all _ fun x => FunctionalInequalities.Analysis.Tensor.norm_prod_inner_le d h x
  have hA : ‖∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ (∫ x, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := by
    calc
      ‖∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ ∫ x in s, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂ν :=
        norm_integral_le_of_norm_le (hpow.mul_const _).restrict (ae_restrict_of_ae hbound)
      _ ≤ ∫ x, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂ν :=
        setIntegral_le_integral (hpow.mul_const _) (ae_of_all _ fun x => by positivity)
      _ = (∫ x, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := integral_mul_const _ _
  have hA' : ‖∫ x in sᶜ, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ (∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := by
    calc
      ‖∫ x in sᶜ, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ ∫ x in sᶜ, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂ν :=
        norm_integral_le_of_norm_le (hpow.mul_const _).restrict (ae_restrict_of_ae hbound)
      _ = (∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := integral_mul_const _ _
  rw [hcond, ← hsplit]
  set c := ((ν s)⁻¹).toReal
  set A := ∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν
  set A' := ∫ x in sᶜ, ∏ j, ⟪x, h j⟫ ∂ν
  calc
    ‖c * A - (A + A')‖ = ‖(c - 1) * A - A'‖ := by congr 1; ring
    _ ≤ ‖(c - 1) * A‖ + ‖A'‖ := norm_sub_le _ _
    _ = |c - 1| * ‖A‖ + ‖A'‖ := by rw [norm_mul, Real.norm_eq_abs]
    _ ≤ |c - 1| * ((∫ x, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖) + (∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) hA'
    _ = (|c - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem eventually_measure_closedBall_ne_zero (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ᶠ R : ℕ in atTop, ν (Metric.closedBall (0 : E) R) ≠ 0 := by
  have hmono : Monotone fun R : ℕ => Metric.closedBall (0 : E) (R : ℝ) := fun m n hmn =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hB : Tendsto (fun R : ℕ => ν (Metric.closedBall (0 : E) R)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [Metric.iUnion_closedBall_nat, measure_univ] at this
  filter_upwards [hB.eventually (lt_mem_nhds (zero_lt_one' ENNReal))] with R hR
  exact hR.ne'

/-- Moment tensors of the ball truncations converge in operator norm. -/
theorem tendsto_iteratedFDeriv_laplace_cond_closedBall (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ) :
    Tendsto
      (fun R : ℕ =>
        iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R])) 0)
      atTop (𝓝 (iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0)) := by
  have hpow := FunctionalInequalities.Probability.integrable_norm_pow_of_exp ν hr hexp d
  have hmono : Monotone fun R : ℕ => Metric.closedBall (0 : E) (R : ℝ) := fun m n hmn =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hmeas : ∀ R : ℕ, MeasurableSet (Metric.closedBall (0 : E) (R : ℝ)) := fun R =>
    Metric.isClosed_closedBall.measurableSet
  have hB : Tendsto (fun R : ℕ => ν (Metric.closedBall (0 : E) R)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [Metric.iUnion_closedBall_nat, measure_univ] at this
  have hc : Tendsto (fun R : ℕ => ((ν (Metric.closedBall (0 : E) R))⁻¹).toReal) atTop (𝓝 1) := by
    have h1 : Tendsto (fun R : ℕ => (ν (Metric.closedBall (0 : E) R)).toReal) atTop (𝓝 1) := by
      have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hB
      simpa [Function.comp_def] using this
    have := h1.inv₀ one_ne_zero
    simpa [ENNReal.toReal_inv] using this
  have hm :
    Tendsto (fun R : ℕ => ∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ d ∂ν) atTop
      (𝓝 (∫ x, ‖x‖ ^ d ∂ν)) := by
    have := tendsto_setIntegral_of_monotone hmeas hmono hpow.integrableOn
    rwa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine
    squeeze_zero' (g := fun R : ℕ =>
      |((ν (Metric.closedBall (0 : E) R))⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν +
        ((∫ x, ‖x‖ ^ d ∂ν) - ∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ d ∂ν))
      (Eventually.of_forall fun R => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_measure_closedBall_ne_zero ν] with R hR
    have h1 := norm_iteratedFDeriv_laplace_cond_sub_le ν hr hexp d (hmeas R) hR
    have h2 := integral_add_compl (hmeas R) hpow
    calc
      _ ≤ _ := h1
      _ =
          |((ν (Metric.closedBall (0 : E) R))⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν +
            ((∫ x, ‖x‖ ^ d ∂ν) - ∫ x in Metric.closedBall (0 : E) R, ‖x‖ ^ d ∂ν) := by
        rw [← h2]; ring
  · have :=
      ((hc.sub_const 1).abs.mul_const (∫ x, ‖x‖ ^ d ∂ν)).add
        ((tendsto_const_nhds (x := ∫ x, ‖x‖ ^ d ∂ν)).sub hm)
    simpa using this

/-- The cumulant tensor as the Faà di Bruno composition of the Taylor jets of `log` at `1` and of
the Laplace transform at `0`. -/
theorem cumulant_eq_taylorComp (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    cumulant μ k = (ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1).taylorComp
      (ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) 0) k := by
  have hgi : ∀ t < r,
      Integrable (fun x : E => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
    intro t ht
    simpa only [norm_one, mul_one] using
      Probability.integrable_exp_mul_norm_of_le hexp ht.le
  have hZ : ContDiffOn ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, mul_one] using
      weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable hgi
  have hpos : ∀ z ∈ Metric.ball (0 : E) r, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa using hz
    have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
      refine (hgi ‖z‖ hz').mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
      · filter_upwards [] with x
        simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    exact integral_exp_pos hzint
  have hU : UniqueDiffOn ℝ (Metric.ball (0 : E) r) := Metric.isOpen_ball.uniqueDiffOn
  have hf : HasFTaylorSeriesUpToOn k (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (ftaylorSeriesWithin ℝ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r))
      (Metric.ball 0 r) :=
    (hZ.of_le (WithTop.coe_le_coe.mpr le_top)).ftaylorSeriesWithin hU
  have hg : HasFTaylorSeriesUpToOn k Real.log (ftaylorSeriesWithin ℝ Real.log {0}ᶜ) {0}ᶜ :=
    (Real.contDiffOn_log (n := k)).ftaylorSeriesWithin isOpen_compl_singleton.uniqueDiffOn
  have hmaps : Set.MapsTo (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) {0}ᶜ :=
    fun z hz => (hpos z hz).ne'
  have hcomp := hg.comp hf hmaps
  have h0 : (0 : E) ∈ Metric.ball (0 : E) r := Metric.mem_ball_self hr
  have heq := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hU h0
  have hZ0 : (∫ x, Real.exp ⟪(0 : E), x⟫ ∂μ) = 1 := by simp
  rw [hZ0] at heq
  have hlog : logLaplace μ = Real.log ∘ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := rfl
  unfold cumulant
  rw [hlog, ← iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball h0, ← heq]

end CondHelpers

/--
**Cumulants of ball truncations converge** (BKL arXiv:2610.05474v1, p. 19, reduction to compactly
supported laws): for a probability measure with one exponential moment `∫ e^{r‖x‖} < ∞` (`r > 0`, as
given by Borell's lemma for log-concave laws), the cumulants of the conditional laws on the balls
`B(0, R)` converge to those of the measure as `R → ∞`. -/
theorem tendsto_cumulant_cond_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (k : ℕ) :
    Tendsto (fun R : ℕ => cumulant (ν[|Metric.closedBall (0 : E) R]) k) atTop
      (𝓝 (cumulant ν k)) := by
  have h0 : (0 : E) ∈ Metric.ball (0 : E) r := Metric.mem_ball_self hr
  set q : FormalMultilinearSeries ℝ ℝ ℝ := ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1 with hq
  set p : ℕ → FormalMultilinearSeries ℝ E ℝ := fun R =>
    ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R]))
      (Metric.ball 0 r) 0 with
    hp
  set p' : FormalMultilinearSeries ℝ E ℝ :=
    ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) (Metric.ball 0 r) 0 with hp'
  have hcum :
    ∀ᶠ R : ℕ in atTop, cumulant (ν[|Metric.closedBall (0 : E) R]) k = q.taylorComp (p R) k := by
    filter_upwards [eventually_measure_closedBall_ne_zero ν] with R hR
    have : IsProbabilityMeasure (ν[|Metric.closedBall (0 : E) R]) :=
      cond_isProbabilityMeasure hR
    have hexp' : Integrable (fun x => Real.exp (r * ‖x‖)) (ν[|Metric.closedBall (0 : E) R]) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    exact cumulant_eq_taylorComp (ν[|Metric.closedBall (0 : E) R]) hr hexp' k
  have hlim : ∀ j : ℕ, Tendsto (fun R => p R j) atTop (𝓝 (p' j)) := by
    intro j
    have := tendsto_iteratedFDeriv_laplace_cond_closedBall ν hr hexp j
    simp only [hp, hp', ftaylorSeriesWithin]
    simp only [iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball h0]
    exact this
  rw [cumulant_eq_taylorComp ν hr hexp k]
  have hlittle :=
    FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO (l := atTop) (p₁ := fun _ : ℕ =>
      q) (p₂ := fun _ : ℕ => q) (q₁ := p) (q₂ := fun _ : ℕ => p') (f := fun _ : ℕ => (1 : ℝ))
      (n := k) (fun j _ => isBoundedUnder_const) (fun j _ => by simp)
      (fun j _ => (hlim j).norm.isBoundedUnder_le) (fun j _ => isBoundedUnder_const)
      (fun j _ => (Asymptotics.isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 (hlim j)))
  rw [Asymptotics.isLittleO_one_iff] at hlittle
  exact (tendsto_sub_nhds_zero_iff.1 hlittle).congr' (hcum.mono fun R h => h.symm)

end FunctionalInequalities.Analysis.BakryEmery

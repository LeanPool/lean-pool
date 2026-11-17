/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Positive
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.LocalThirdCumulant
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Transport
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.InverseSqrt
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.Probability.Conditioning

/-!
# Reduction of BKL Theorem 4.1 to compactly supported laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19: Theorem 4.1 is proved first for compactly supported
isotropic log-concave laws (`CumulantBoundCompact`), whose localization coefficients are smooth and
bounded. `LetwinCompactBound` is Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for
compactly supported laws: the interface between the Letwin stream and the Theorem 4.1 stream. It
gives
the base case `CumulantBoundCompact 2 8` (BKL Lemma 4.2). Both names are hypotheses; neither
Letwin's
theorem nor Theorem 4.1 is proved here.
`exists_compact_moment_approximation` approximates every isotropic log-concave law, in all mixed
linear moments of
degree at most four, by centered and covariance-whitened growing-ball truncations: compactly
supported isotropic
log-concave laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/--
`CumulantBound d b` restricted to compactly supported laws: `R^ν_{d+1} ≤ b Id` for every compactly
supported isotropic log-concave probability measure in every dimension (BKL arXiv:2610.05474v1, p.
19:
Theorem 4.1 is proved for compactly supported laws first). This names the hypothesis. -/
def CumulantBoundCompact (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν →
      _root_.FunctionalInequalities.KLS.LogConcave ν →
        IsCompact (ν : Measure (EuclideanSpace ℝ (Fin m))).support →
          ∀ u : EuclideanSpace ℝ (Fin m),
            ∑ J : Fin d → Fin m,
                cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                    (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^
                  2 ≤
              b * ‖u‖ ^ 2

/--
Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for compactly supported isotropic
log-concave laws in positive dimension: the input of BKL Lemma 4.2 used by the localization
argument.
This names the hypothesis; it is the interface between the Letwin and the Theorem 4.1 streams. -/
def LetwinCompactBound : Prop :=
  ∀ (n : ℕ),
    0 < n →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        _root_.FunctionalInequalities.KLS.LogConcave μ →
          KLS.Isotropic μ →
            IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support →
              LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))

/-- **Base case of the compact induction** (BKL Lemma 4.2 for compactly supported laws): the compact
Letwin bound gives `CumulantBoundCompact 2 8`. -/
theorem cumulantBoundCompact_two_of_letwinCompact (h : LetwinCompactBound) :
    CumulantBoundCompact 2 8 := by
  classical
  intro n μ hiso hLC hcompact u
  cases n with
  | zero =>
    have hs : (∑ J : Fin 2 → Fin 0, cumulant (μ : Measure _) 3
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin 0) ℝ (J k)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro J _hJ
      exact Fin.elim0 (J 0)
    rw [hs]
    positivity
  | succ n =>
    let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    have hbound := LogConcave.sum_sq_cumulant_three_le_of_letwin μ hLC hiso
      (h (n + 1) (Nat.succ_pos _) μ hLC hiso hcompact) b u
    have heq : (∑ J : Fin 2 → Fin (n + 1), cumulant (μ : Measure _) 3
        (Fin.cons u fun k => b (J k)) ^ 2) =
        ∑ j, ∑ k, cumulant (μ : Measure _) 3 ![u, b j, b k] ^ 2 := by
      exact Analysis.Tensor.sum_finTwo_arrow_cons b u
        (fun v => cumulant (μ : Measure _) 3 v ^ 2)
    change (∑ J : Fin 2 → Fin (n + 1), cumulant (μ : Measure _) 3
      (Fin.cons u fun k => b (J k)) ^ 2) ≤ _
    rw [heq]
    exact hbound

/-- A bound for all laws restricts to compactly supported ones. -/
theorem CumulantBound.compact {d : ℕ} {b : ℝ} (h : CumulantBound d b) :
    CumulantBoundCompact d b := by exact fun m ν hiso hLC _ u => h m ν hiso hLC u

end FunctionalInequalities.KLS.LogConcave.Suspension

namespace FunctionalInequalities.KLS.LogConcave.Suspension

section CompactToGeneral

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

/-! Reduction to compactly supported laws (BKL p. 19 and end of Section 6):
`cumulantBound_of_compact`. -/

open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis

section OperatorHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end OperatorHelpers

section MeasureHelpers

variable {E : Type*} [NormedAddCommGroup E]

/-- A ball truncation has exponential moments of every order. -/
theorem integrable_exp_cond_closedBall [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ν : Measure E) [IsFiniteMeasure ν] (R : ℕ)
    (hR : ν (Metric.closedBall (0 : E) R) ≠ 0) (t : ℝ) :
    Integrable (fun x => Real.exp (t * ‖x‖)) (ν[|Metric.closedBall (0 : E) R]) := by
  have hres :
    Integrable (fun x => Real.exp (t * ‖x‖)) (ν.restrict (Metric.closedBall (0 : E) R)) := by
    refine (integrable_const (Real.exp (|t| * R))).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hx' : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    calc
      t * ‖x‖ ≤ |t| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg x)
      _ ≤ |t| * R := mul_le_mul_of_nonneg_left hx' (abs_nonneg t)
  exact hres.smul_measure (ENNReal.inv_ne_top.2 hR)

section InnerProduct

variable [InnerProductSpace ℝ E]

/-- A ball truncation is compactly supported. -/
theorem isCompact_support_cond_closedBall [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) (R : ℕ) :
    IsCompact (ν[|Metric.closedBall (0 : E) R]).support := by
  refine (isCompact_closedBall (0 : E) R).of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed Metric.isClosed_closedBall ?_)
  rw [mem_ae_iff, cond_apply Metric.isClosed_closedBall.measurableSet]
  simp

/--
**Standardisation of a compactly supported log-concave law** with positive invertible covariance:
the
law of `σ (x - a)`, with `σ = Cov^{-1/2}` and `a` the mean, is isotropic, log-concave and compactly
supported. -/
theorem exists_standardized [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (μ : ProbabilityMeasure E) (hLC : LogConcave μ)
    (hc : IsCompact (μ : Measure E).support)
    (hpos : (Covariance.operator (μ : Measure E)).IsPositive)
    (hunit : IsUnit (Covariance.operator (μ : Measure E))) :
    ∃ (η : ProbabilityMeasure E) (W : E ≃L[ℝ] E),
      (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (μ : Measure E)) ∧
        KLS.Isotropic η ∧
          LogConcave η ∧
            IsCompact (η : Measure E).support ∧
              (η : Measure E) =
                (μ : Measure E).map (fun x => W (x - ∫ y, y ∂(μ : Measure E))) := by
  let A : E →L[ℝ] E := Covariance.operator (μ : Measure E)
  let σ : E →L[ℝ] E := inverseSqrt A
  have hσ : IsUnit σ := by
    change IsUnit (inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
    exact inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
  let W : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hσ.unit
  have hW : (W : E →L[ℝ] E) = σ := by
    change (↑hσ.unit : E →L[ℝ] E) = σ
    exact hσ.unit_spec
  have hWx : ∀ x, W x = σ x := fun x => by rw [← hW]; rfl
  let a : E := ∫ y, y ∂(μ : Measure E)
  let ν' : ProbabilityMeasure E := Probability.translateLaw μ (-a)
  let η : ProbabilityMeasure E := Probability.mapContinuousLinearEquiv ν' W
  have hηcoe : (η : Measure E) = (ν' : Measure E).map W := rfl
  have hmeas : Measurable fun x : E => W (x - a) :=
    (W.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hmap : (η : Measure E) = (μ : Measure E).map (fun x => W (x - a)) := by
    rw [hηcoe, Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add (-a))]
    congr 1
    funext x
    simp [neg_add_eq_sub]
  have hμlp : MemLp id 2 (μ : Measure E) := hLC.memLp_id_two
  have hint : Integrable id (μ : Measure E) := hμlp.integrable (by norm_num)
  have ht : MemLp id 2 (ν' : Measure E) := Probability.memLp_id_two_translateLaw μ (-a) hμlp
  have hηlp : MemLp id 2 (η : Measure E) := by
    rw [hηcoe,
      memLp_map_measure_iff measurable_id.aestronglyMeasurable W.continuous.aemeasurable]
    simpa [Function.comp_def] using (W : E →L[ℝ] E).comp_memLp' ht
  have hzero : ∫ x, x ∂(ν' : Measure E) = 0 :=
    Probability.integral_id_translateLaw_neg_integral μ hint
  have hmean : ∫ x, x ∂(η : Measure E) = 0 := by
    rw [hηcoe]
    change ∫ x, id x ∂((ν' : Measure E).map W) = 0
    rw [integral_map W.continuous.aemeasurable hηlp.aestronglyMeasurable]
    simp only [id_eq]
    rw [W.integral_comp_comm]
    simpa using congrArg W hzero
  have hself : (σ.adjoint : E →L[ℝ] E) = σ := (inverseSqrt_spec A hpos hunit).2.1.adjoint_eq
  have halg : (σ.comp A).comp σ = 1 := by
    ext x
    simpa [σ, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T x) (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
  have hiso : KLS.Isotropic η := by
    refine ⟨hηlp, hmean, ?_⟩
    rw [hηcoe, Covariance.operator_map_continuousLinearEquiv, Covariance.operator_translateLaw,
      hW, hself]
    exact halg
  have hLCη : LogConcave η := (hLC.translateLaw (-a)).mapContinuousLinearEquiv W
  have hcη : IsCompact (η : Measure E).support := by
    have hK : IsCompact ((fun x : E => W (x - a)) '' (μ : Measure E).support) :=
      hc.image (W.continuous.comp (continuous_id.sub continuous_const))
    refine
      hK.of_isClosed_subset Measure.isClosed_support
        (Measure.support_subset_of_isClosed hK.isClosed ?_)
    have hinj : Function.Injective fun x : E => W (x - a) := fun x y hxy =>
      sub_left_injective (W.injective hxy)
    rw [mem_ae_iff, hmap, Measure.map_apply hmeas hK.isClosed.measurableSet.compl,
      Set.preimage_compl, Set.preimage_image_eq _ hinj]
    exact Measure.measure_compl_support
  exact ⟨η, W, hW, hiso, hLCη, hcη, hmap⟩

end InnerProduct

end MeasureHelpers

/--
**Reduction to compactly supported laws** (BKL arXiv:2610.05474v1, p. 19 and the end of Section 6,
"standard
approximation argument"): a cumulant bound for compactly supported isotropic log-concave laws holds
for all isotropic
log-concave laws, for every order `d + 1 ≥ 2`. -/
theorem cumulantBound_of_compact {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : CumulantBoundCompact d b) :
    CumulantBound d b := by
  classical
  intro m ν hiso hLC u
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff ν).1 hLC).exists_integrable_exp_norm
  let E := EuclideanSpace ℝ (Fin m)
  let νR : ℕ → Measure E := fun R => (ν : Measure E)[|Metric.closedBall (0 : E) R]
  let Sg : ℕ → E →L[ℝ] E := fun R => Covariance.operator (νR R)
  let T : ℕ → E →L[ℝ] E := fun R => inverseSqrt (Sg R)
  have hmass : ∀ᶠ R : ℕ in atTop, (ν : Measure E) (Metric.closedBall (0 : E) R) ≠ 0 :=
    eventually_measure_closedBall_ne_zero (ν : Measure E)
  have hcum2 := tendsto_cumulant_cond_closedBall (ν : Measure E) hr hexp 2
  have hcumd := tendsto_cumulant_cond_closedBall (ν : Measure E) hr hexp (d + 1)
  have hSg : Tendsto Sg atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hcum2
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hcum2
    filter_upwards [hmass] with R hR
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    have hexpR : Integrable (fun x => Real.exp (r * ‖x‖)) (νR R) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    refine FunctionalInequalities.Analysis.opNorm_le_of_inner_eq fun v w => ?_
    simp only [sub_apply]
    rw [cumulant_two_eq_covariance_of_integrable_exp
        ((ν : Measure E)[|Metric.closedBall (0 : E) R]) hr hexpR v w,
      cumulant_two_eq_covariance_of_integrable_exp (ν : Measure E) hr hexp v w,
      hiso.covariance_identity]
    simp [Sg, νR, inner_sub_left]
  have hpos : ∀ R, (Sg R).IsPositive := fun R =>
    (ContinuousLinearMap.isPositive_iff' _).mpr
      ⟨Covariance.operator_isSelfAdjoint _, fun v => by
        rw [Covariance.operator_inner];
        exact ProbabilityTheory.covarianceBilin_self_nonneg v⟩
  have hlt : ∀ᶠ R in atTop, ‖Sg R - 1‖ < 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hSg).eventually (gt_mem_nhds one_pos)
  have hunit : ∀ᶠ R in atTop, IsUnit (Sg R) :=
    hlt.mono fun R hR =>
      isUnit_of_inner_self_pos _ fun v hv =>
        FunctionalInequalities.Analysis.inner_self_pos_of_norm_sub_one_lt hR hv
  have hT : Tendsto T atTop (𝓝 1) :=
    FunctionalInequalities.Analysis.tendsto_inverseSqrt_one hSg (Eventually.of_forall hpos)
      hunit
  have hbound :
    ∀ᶠ R in atTop,
      ∑ J : Fin d → Fin m,
          cumulant (νR R) (d + 1)
              (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
            2 ≤
        b * ‖u‖ ^ 2 := by
    filter_upwards [hmass, hunit] with R hR hu
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    let μR : ProbabilityMeasure E := ⟨νR R, inferInstance⟩
    have hLCR : LogConcave μR := hLC.cond (convex_closedBall _ _) Metric.isClosed_closedBall hR
    have hcR : IsCompact (μR : Measure E).support :=
      isCompact_support_cond_closedBall (ν : Measure E) R
    obtain ⟨η, W, hW, hiso', hLC', hc', hmap⟩ := exists_standardized μR hLCR hcR (hpos R) hu
    have hb := h m η hiso' hLC' hc' u
    have hexpR : ∀ t : ℝ, Integrable (fun x => Real.exp (t * ‖x‖)) (νR R) :=
      integrable_exp_cond_closedBall (ν : Measure E) R hR
    have hk : 2 ≤ d + 1 := by omega
    have hself :
      (inverseSqrt (Covariance.operator (μR : Measure E))).adjoint =
        inverseSqrt (Covariance.operator (μR : Measure E)) :=
      (inverseSqrt_spec _ (hpos R) hu).2.1.adjoint_eq
    calc
      ∑ J : Fin d → Fin m,
            cumulant (νR R) (d + 1)
                (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
              2 =
          ∑ J : Fin d → Fin m,
            cumulant (η : Measure E) (d + 1)
                (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^
              2 := by
        refine Finset.sum_congr rfl fun J _ => ?_
        congr 1
        rw [hmap, cumulant_map_affine W _ (μR : Measure E) hexpR hk, hW]
        congr 1
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp only [Fin.cons_zero, hself]; rfl
        · simp only [Fin.cons_succ, hself]; rfl
      _ ≤ b * ‖u‖ ^ 2 := hb
  have hlim :
    Tendsto
      (fun R =>
        ∑ J : Fin d → Fin m,
          cumulant (νR R) (d + 1)
              (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^
            2)
      atTop
      (𝓝
        (∑ J : Fin d → Fin m,
          cumulant (ν : Measure E) (d + 1)
              (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^
            2)) := by
    refine tendsto_finsetSum _ fun J _ => ?_
    refine (hcumd.eval ?_).pow 2
    rw [tendsto_pi_nhds]
    have hTv : ∀ v : E, Tendsto (fun R => T R v) atTop (𝓝 v) := fun v => by
      have := ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto 1).comp hT
      simpa [Function.comp_def] using this
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [Fin.cons_zero] using hTv u
    · simpa only [Fin.cons_succ] using hTv (EuclideanSpace.basisFun (Fin m) ℝ (J k))
  exact le_of_tendsto hlim hbound

end CompactToGeneral

end FunctionalInequalities.KLS.LogConcave.Suspension

section CompactMomentApproximation

open MeasureTheory ProbabilityTheory Filter Topology Metric
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/--
**Compact moment approximation**: an isotropic log-concave law is the limit, in all mixed linear
moments of degree
`≤ 4`, of compactly supported isotropic log-concave laws, namely its growing-ball truncations,
centered and whitened by
the inverse square root of their covariance (the tail beyond the radius where the covariance is
invertible). -/
theorem exists_compact_moment_approximation {n : ℕ}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hLC : KLS.LogConcave ν)
    (hiso : KLS.Isotropic ν) :
    ∃ η : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      (∀ k,
          KLS.LogConcave (η k) ∧
            KLS.Isotropic (η k) ∧
              IsCompact (η k : Measure (EuclideanSpace ℝ (Fin n))).support) ∧
        ∀ d ≤ 4,
          ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
            Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(η k : Measure (EuclideanSpace ℝ (Fin n))))
              atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(ν : Measure (EuclideanSpace ℝ (Fin n))))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff ν).1 hLC).exists_integrable_exp_norm
  let νR : ℕ → Measure E := fun R => (ν : Measure E)[|Metric.closedBall (0 : E) R]
  let Sg : ℕ → E →L[ℝ] E := fun R => Covariance.operator (νR R)
  let T : ℕ → E →L[ℝ] E := fun R => inverseSqrt (Sg R)
  let a : ℕ → E := fun R => ∫ x, x ∂(νR R)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, νR, id_eq, hiso.mean_zero] using
      Probability.tendsto_integral_cond_closedBall (ν : Measure E)
        (hiso.memLp_two.integrable (by norm_num))
  have hmass : ∀ᶠ R : ℕ in atTop, (ν : Measure E) (Metric.closedBall (0 : E) R) ≠ 0 :=
    eventually_measure_closedBall_ne_zero (ν : Measure E)
  have hcum2 := tendsto_cumulant_cond_closedBall (ν : Measure E) hr hexp 2
  have hSg : Tendsto Sg atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hcum2
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hcum2
    filter_upwards [hmass] with R hR
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    have hexpR : Integrable (fun x => Real.exp (r * ‖x‖)) (νR R) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    refine FunctionalInequalities.Analysis.opNorm_le_of_inner_eq fun v w => ?_
    simp only [sub_apply]
    rw [cumulant_two_eq_covariance_of_integrable_exp
        ((ν : Measure E)[|Metric.closedBall (0 : E) R]) hr hexpR v w,
      cumulant_two_eq_covariance_of_integrable_exp (ν : Measure E) hr hexp v w,
      hiso.covariance_identity]
    simp [Sg, νR, inner_sub_left]
  have hpos : ∀ R, (Sg R).IsPositive := fun R =>
    (ContinuousLinearMap.isPositive_iff' _).mpr
      ⟨Covariance.operator_isSelfAdjoint _, fun v => by
        rw [Covariance.operator_inner];
        exact covarianceBilin_self_nonneg v⟩
  have hlt : ∀ᶠ R in atTop, ‖Sg R - 1‖ < 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hSg).eventually (gt_mem_nhds one_pos)
  have hunit : ∀ᶠ R in atTop, IsUnit (Sg R) :=
    hlt.mono fun R hR =>
      isUnit_of_inner_self_pos _ fun v hv =>
        FunctionalInequalities.Analysis.inner_self_pos_of_norm_sub_one_lt hR hv
  have hT : Tendsto T atTop (𝓝 1) :=
    FunctionalInequalities.Analysis.tendsto_inverseSqrt_one hSg (Eventually.of_forall hpos)
      hunit
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hmass.and hunit)
  have happrox (k : ℕ) :
    ∃ η : ProbabilityMeasure E,
      KLS.LogConcave η ∧
        KLS.Isotropic η ∧
          IsCompact (η : Measure E).support ∧
            (η : Measure E) = (νR (k + N)).map (fun x => T (k + N) (x - a (k + N))) := by
    obtain ⟨hm, hu⟩ := hN (k + N) (by omega)
    have : IsProbabilityMeasure (νR (k + N)) := cond_isProbabilityMeasure hm
    let μR : ProbabilityMeasure E := ⟨νR (k + N), inferInstance⟩
    have hLCR : KLS.LogConcave μR :=
      hLC.cond (convex_closedBall _ _) Metric.isClosed_closedBall hm
    have hcR : IsCompact (μR : Measure E).support :=
      isCompact_support_cond_closedBall (ν : Measure E) (k + N)
    obtain ⟨η, W, hW, hiso', hLC', hc', hmap⟩ := exists_standardized μR hLCR hcR (hpos _) hu
    refine ⟨η, hLC', hiso', hc', ?_⟩
    change (η : Measure E) = (νR (k + N)).map (fun x => (W : E →L[ℝ] E) (x - a (k + N))) at hmap
    rwa [hW] at hmap
  choose η hηLC hηiso hηcompact hηmap using happrox
  refine ⟨η, fun k => ⟨hηLC k, hηiso k, hηcompact k⟩, ?_⟩
  intro d _hd v
  have h :=
    Probability.tendsto_integral_prod_inner_affine_cond_closedBall (ν : Measure E) d
      (FunctionalInequalities.Probability.integrable_norm_pow_of_exp _ hr hexp d) T a hT ha v
  have htail : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
  apply (h.comp htail).congr'
  exact
    Eventually.of_forall fun k => by
      dsimp only [Function.comp_def]
      rw [hηmap k, integral_map (by fun_prop) (by fun_prop)]

end FunctionalInequalities.KLS.LogConcave.Suspension

end CompactMomentApproximation

/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Markov
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Dirichlet
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic

/-!
# Markov property of the log-concave heat semigroup

This module proves the Markov property used by the semigroup proof of
`thm:logconcave-cheeger-poincare-comparison`. The closed weighted-gradient energy of a
full-dimensional log-concave probability law is Markovian under every normal contraction. The
abstract Beurling--Deny resolvent theorem from `Analysis/Semigroup/Generated/Markov.lean` then shows
that
the heat semigroup preserves positivity and constants, is sub-Markov, preserves integrals,
satisfies `|P_t f| ≤ P_t |f|`, and contracts finite essential bounds.

The only concrete analytic step is the Markov property of the closed energy. A normal contraction
is mollified on the real line using the `NormalContraction.smoothed` family.
For a weighted-gradient test `g`, the smooth composition obeys the classical chain rule and its
weighted gradient is a scalar of `B (gradient g)`, with scalar of norm at most one. These composed
tests converge in `L²` to the nonsmooth contraction and give the required recovery sequence for
the sequential relaxation. No almost-everywhere chain rule for the nonsmooth contraction is used.

This file provides no Bakry--Émery `Γ`-calculus, no small-time heat estimate, and
no step of Buser's inequality.
-/

@[expose] public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Topology
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.Euclidean
open FunctionalInequalities.Analysis.Semigroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)

namespace MarkovProof

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- At a differentiability point of `g`, composing with a smooth real function scales the
gradient by the one-dimensional derivative applied to one. -/
theorem gradient_comp_eq_smul {ψ : ℝ → ℝ} {g : V → ℝ} {x : V}
    (hψ : DifferentiableAt ℝ ψ (g x)) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y ↦ ψ (g y)) x = (fderiv ℝ ψ (g x) 1) • gradient g x := by
  change gradient (ψ ∘ g) x = _
  apply (InnerProductSpace.toDual ℝ V).injective
  rw [map_smul, toDual_gradient, toDual_gradient, fderiv_comp x hψ hg]
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, smul_apply]
  have hscalar : fderiv ℝ g x v = (fderiv ℝ g x v) • (1 : ℝ) := by simp
  conv_lhs => rw [hscalar, map_smul]
  simp only [smul_eq_mul]
  ring

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Smoothly composing a differentiable test with a mollified normal contraction cannot increase
the norm of its weighted gradient at that point. -/
theorem norm_weightedGradient_comp_smoothed_le (φ : NormalContraction) (j : ℕ)
    {g : V → ℝ} {x : V} (hg : DifferentiableAt ℝ g x) :
    ‖WeightedGradient.apply B (fun y ↦ φ.smoothed j (g y)) x‖ ≤
      ‖WeightedGradient.apply B g x‖ := by
  have hψ : DifferentiableAt ℝ (φ.smoothed j) (g x) :=
    (φ.contDiff_smoothed j).differentiable (by simp) _
  rw [WeightedGradient.apply, gradient_comp_eq_smul hψ hg, map_smul, norm_smul]
  have hvalue : ‖fderiv ℝ (φ.smoothed j) (g x) 1‖ ≤ 1 := by
    calc
      ‖fderiv ℝ (φ.smoothed j) (g x) 1‖ ≤ ‖fderiv ℝ (φ.smoothed j) (g x)‖ * ‖(1 : ℝ)‖ :=
        (fderiv ℝ (φ.smoothed j) (g x)).le_opNorm 1
      _ ≤ 1 := by simpa using φ.norm_fderiv_smoothed_le j (g x)
  rw [Real.norm_eq_abs] at hvalue
  change |fderiv ℝ (φ.smoothed j) (g x) 1| * ‖B (gradient g x)‖ ≤ ‖B (gradient g x)‖
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hvalue (norm_nonneg _)

/-- The mollified composition of a weighted-gradient test is again a test. -/
theorem compSmoothed (hac : (ν : Measure V) ≪ m) {g : V → ℝ} (h : WeightedGradient.IsTest ν B g)
    (φ : NormalContraction) (j : ℕ) :
    WeightedGradient.IsTest ν B (fun x ↦ φ.smoothed j (g x)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := h.1
    refine ⟨K, ?_⟩
    change LipschitzWith K (φ.smoothed j ∘ g)
    simpa only [one_mul] using (φ.lipschitzWith_smoothed j).comp hK
  · refine
      MemLp.of_le ((memLp_const ‖φ.smoothed j 0‖).add h.memLp.norm)
        ((φ.contDiff_smoothed j).continuous.comp h.continuous).aestronglyMeasurable
        (ae_of_all _ fun x ↦ ?_)
    change ‖φ.smoothed j (g x)‖ ≤ ‖‖φ.smoothed j 0‖ + ‖g x‖‖
    rw [Real.norm_eq_abs (‖φ.smoothed j 0‖ + ‖g x‖),
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hlip := (φ.lipschitzWith_smoothed j).dist_le_mul (g x) 0
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, sub_zero] at hlip
    calc
      ‖φ.smoothed j (g x)‖ = ‖(φ.smoothed j (g x) - φ.smoothed j 0) + φ.smoothed j 0‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖φ.smoothed j (g x) - φ.smoothed j 0‖ + ‖φ.smoothed j 0‖ := norm_add_le _ _
      _ ≤ ‖g x‖ + ‖φ.smoothed j 0‖ := by gcongr
      _ = ‖φ.smoothed j 0‖ + ‖g x‖ := add_comm _ _
  · refine
      MemLp.of_le h.memLp_apply.norm
        (WeightedGradient.measurable_apply B _).aestronglyMeasurable ?_
    filter_upwards [hac.ae_le
        (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
          h.1.choose_spec.locallyLipschitz m)] with
      x hx
    simpa using norm_weightedGradient_comp_smoothed_le B φ j hx

/-- The class of a mollified composition is uniformly close in `L²(ν)` to composition by the
original normal contraction. -/
theorem norm_toLp_compSmoothed_sub_le (hac : (ν : Measure V) ≪ m) {g : V → ℝ}
    (h : WeightedGradient.IsTest ν B g) (φ : NormalContraction) (j : ℕ) :
    ‖(compSmoothed m B hac h φ j).memLp.toLp (fun x ↦ φ.smoothed j (g x)) -
      φ.compL2 (ν : Measure V) (h.memLp.toLp g)‖ ≤ 2 * LipschitzApproximation.radius j := by
  have hbound : ∀ᵐ x ∂(ν : Measure V),
      ‖((compSmoothed m B hac h φ j).memLp.toLp (fun x ↦ φ.smoothed j (g x)) -
        φ.compL2 (ν : Measure V) (h.memLp.toLp g)) x‖ ≤
          2 * LipschitzApproximation.radius j := by
    filter_upwards [Lp.coeFn_sub
      ((compSmoothed m B hac h φ j).memLp.toLp (fun x ↦ φ.smoothed j (g x)))
      (φ.compL2 (ν : Measure V) (h.memLp.toLp g)),
      MemLp.coeFn_toLp (compSmoothed m B hac h φ j).memLp,
      φ.coeFn_compL2 (ν : Measure V) (h.memLp.toLp g), MemLp.coeFn_toLp h.memLp]
      with x hsub hsmooth hcomp hg
    rw [hsub, Pi.sub_apply, hsmooth, hcomp, hg]
    exact φ.norm_smoothed_sub_le j (g x)
  have hnorm := Lp.norm_le_of_ae_bound
    (mul_nonneg two_pos.le (LipschitzApproximation.radius_pos j).le) hbound
  rw [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] at hnorm
  exact hnorm

/-- On the raw weighted-gradient domain, the mollified contraction does not increase the
operator norm. -/
theorem norm_operator_compSmoothed_le (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {g : V → ℝ}
    (h : WeightedGradient.IsTest ν B g) (φ : NormalContraction) (j : ℕ) :
    ‖WeightedGradient.operator ν B hac
        ⟨(compSmoothed m B hac h φ j).memLp.toLp (fun x ↦ φ.smoothed j (g x)),
          WeightedGradient.toLp_mem_domain_operator ν B hac (compSmoothed m B hac h φ j)⟩‖ ≤
      ‖WeightedGradient.operator ν B hac
        ⟨h.memLp.toLp g, WeightedGradient.toLp_mem_domain_operator ν B hac h⟩‖ := by
  rw [WeightedGradient.operator_apply ν B hac hfr (compSmoothed m B hac h φ j)
      (WeightedGradient.toLp_mem_domain_operator ν B hac (compSmoothed m B hac h φ j)) rfl,
    WeightedGradient.operator_apply ν B hac hfr h
      (WeightedGradient.toLp_mem_domain_operator ν B hac h) rfl]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [MemLp.coeFn_toLp (compSmoothed m B hac h φ j).memLp_apply,
    MemLp.coeFn_toLp h.memLp_apply,
    hac.ae_le
      (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
        h.1.choose_spec.locallyLipschitz m)] with x hsmooth hg hx
  rw [hsmooth, hg]
  exact norm_weightedGradient_comp_smoothed_le B φ j hx

end MarkovProof

/-- Every normal contraction satisfies the relaxed contraction bound for the full-dimensional
weighted-gradient pre-energy. -/
theorem weighted_relaxedContractionBound (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (φ : NormalContraction) :
    (PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).RelaxedContractionBound
      (φ.compL2 (ν : Measure V)) := by
  intro f
  change (hν.weightedOperator m B hi).domain at f
  let hac := hν.absolutelyContinuous_haar m hi
  obtain ⟨g, hg, hfg⟩ :=
    (WeightedGradient.mem_domain_operator_iff ν B hac (f : Lp ℝ 2 (ν : Measure V))).mp f.2
  let q : ℕ → (hν.weightedOperator m B hi).domain := fun j ↦
    ⟨(MarkovProof.compSmoothed m B hac hg φ j).memLp.toLp
        (fun x ↦ φ.smoothed j (g x)),
      WeightedGradient.toLp_mem_domain_operator ν B hac
        (MarkovProof.compSmoothed m B hac hg φ j)⟩
  have hconv : Tendsto
      (fun j ↦ (PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).toAmbient (q j)) atTop
      (𝓝 (φ.compL2 (ν : Measure V)
        ((PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).toAmbient f))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j ↦ norm_nonneg _)
      (fun j ↦ ?_) (by simpa using LipschitzApproximation.tendsto_radius.const_mul (2 : ℝ))
    simpa only [PreEnergy.ofLinearPMap_toAmbient, q, hfg] using
      MarkovProof.norm_toLp_compSmoothed_sub_le m B hac hg φ j
  let s : (PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).ApproximatingSequence
      (φ.compL2 (ν : Measure V)
        ((PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).toAmbient f)) :=
    ⟨q, hconv⟩
  refine (PreEnergy.sequentialRelaxation_le_sequenceEnergy
    (PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)) s).trans ?_
  refine (liminf_le_liminf (Eventually.of_forall fun j ↦ ?_)).trans_eq (liminf_const _)
  apply ENNReal.coe_le_coe.mpr
  simp only [PreEnergy.ofLinearPMap_energy]
  apply pow_le_pow_left₀ (show (0 : NNReal) ≤ _ from bot_le)
  apply NNReal.coe_le_coe.mp
  change ‖hν.weightedOperator m B hi (q j)‖ ≤ ‖hν.weightedOperator m B hi f‖
  have hf : f =
      ⟨hg.memLp.toLp g, WeightedGradient.toLp_mem_domain_operator ν B hac hg⟩ :=
    Subtype.ext hfg
  rw [hf]
  exact MarkovProof.norm_operator_compSmoothed_le m B hac
    (hν.frontier_support_eq_zero hi) hg φ j

/-- The sequential relaxation of the full-dimensional weighted-gradient energy is Markovian. -/
theorem weighted_relaxation_markovian (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Markovian (ν : Measure V)
      (PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).sequentialRelaxation := by
  intro φ f
  exact PreEnergy.RelaxedContractionBound.sequentialRelaxation_comp_le
    (PreEnergy.ofLinearPMap (hν.weightedOperator m B hi))
    (weighted_relaxedContractionBound m B hν hi φ)
    (φ.lipschitz.lipschitzWith_compLp φ.map_zero).continuous f

/-- The squared-norm energy of the closed weighted gradient is Markovian. -/
theorem closedWeightedOperator_markovian (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Markovian (ν : Measure V)
      (PreEnergy.normSqEnergy (hν.closedWeightedOperator m B hi)) := by
  rw [← PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy
    (hν.weightedOperator m B hi) (hν.weightedOperator_isClosable m B hi)]
  exact weighted_relaxation_markovian m B hν hi

/-- The constant one belongs to the domain of the closed weighted gradient. -/
theorem one_mem_domain_closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    L2.const ν 1 ∈ (hν.closedWeightedOperator m B hi).domain := by
  let hac := hν.absolutelyContinuous_haar m hi
  rw [WeightedGradient.L2_const_eq_toLp]
  exact (hν.weightedOperator m B hi).le_closure.1
    (WeightedGradient.toLp_mem_domain_operator ν B hac (WeightedGradient.IsTest.const 1))

/-- The closed weighted gradient annihilates the constant one. -/
theorem closedWeightedOperator_one_eq_zero (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    hν.closedWeightedOperator m B hi
        ⟨L2.const ν 1, one_mem_domain_closedWeightedOperator m B hν hi⟩ = 0 := by
  let hac := hν.absolutelyContinuous_haar m hi
  let honeRaw : L2.const ν 1 ∈ (hν.weightedOperator m B hi).domain := by
    rw [WeightedGradient.L2_const_eq_toLp]
    exact WeightedGradient.toLp_mem_domain_operator ν B hac (WeightedGradient.IsTest.const 1)
  let oneRaw : (hν.weightedOperator m B hi).domain := ⟨L2.const ν 1, honeRaw⟩
  have hraw : hν.weightedOperator m B hi oneRaw = 0 := by
    rw [WeightedGradient.operator_apply ν B hac (hν.frontier_support_eq_zero hi)
      (WeightedGradient.IsTest.const 1) honeRaw (WeightedGradient.L2_const_eq_toLp ν 1)]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (WeightedGradient.IsTest.const
      (ν := ν) (B := B) 1).memLp_apply, Lp.coeFn_zero V 2 (ν : Measure V)] with x hx hzero
    rw [hx, hzero]
    exact congrFun (WeightedGradient.apply_const B 1) x
  have hclosure := (hν.weightedOperator m B hi).le_closure.2
    (x := oneRaw)
    (y := ⟨L2.const ν 1, one_mem_domain_closedWeightedOperator m B hν hi⟩) rfl
  rw [← hclosure, hraw]

/-! ## Markov properties of the concrete heat semigroup -/

namespace HeatSemigroup

/-- The heat semigroup of a full-dimensional log-concave law preserves positivity. -/
theorem positive (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : 0 ≤ f) :
    0 ≤ HeatSemigroup.operator m B hν hi ht f := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.positive
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi)
    (closedWeightedOperator_markovian m B hν hi) ht hf

/-- The heat semigroup is order preserving. -/
theorem mono (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    {f g : Lp ℝ 2 (ν : Measure V)} (hfg : f ≤ g) :
    HeatSemigroup.operator m B hν hi ht f ≤ HeatSemigroup.operator m B hν hi ht g := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.mono
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi)
    (closedWeightedOperator_markovian m B hν hi) ht hfg

/-- The heat semigroup fixes the constant one. -/
theorem one (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht (L2.const ν 1) = L2.const ν 1 := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.one
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero m B hν hi)

/-- Upper-one functions remain upper bounded by one under the heat semigroup. -/
theorem le_one (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ≤ L2.const ν 1) :
    HeatSemigroup.operator m B hν hi ht f ≤ L2.const ν 1 := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.le_one
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi)
    (closedWeightedOperator_markovian m B hν hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero m B hν hi) hf

/-- Combined Markov bound: `0 ≤ f ≤ 1` implies `0 ≤ P_t f ≤ 1`. -/
theorem subMarkov (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 (ν : Measure V)} (hf0 : 0 ≤ f) (hf1 : f ≤ L2.const ν 1) :
    0 ≤ HeatSemigroup.operator m B hν hi ht f ∧
      HeatSemigroup.operator m B hν hi ht f ≤ L2.const ν 1 := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.subMarkov
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi)
    (closedWeightedOperator_markovian m B hν hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero m B hν hi) hf0 hf1

/-- The heat semigroup preserves the `L²` mean. -/
theorem mean (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) :
    L2.mean ν (HeatSemigroup.operator m B hν hi ht f) = L2.mean ν f := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.mean
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero m B hν hi) f

/-- The heat semigroup preserves the integral of every `L²` function. -/
theorem integral (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) :
    (∫ x, HeatSemigroup.operator m B hν hi ht f x ∂(ν : Measure V)) =
      ∫ x, f x ∂(ν : Measure V) := by
  rw [← L2.mean_eq_integral, ← L2.mean_eq_integral]
  exact HeatSemigroup.mean m B hν hi ht f

/-- Absolute values are dominated pointwise in the `L²` order by applying the heat semigroup to
the absolute value. -/
theorem abs_le (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) :
    |HeatSemigroup.operator m B hν hi ht f| ≤ HeatSemigroup.operator m B hν hi ht |f| := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.abs_le
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi)
    (closedWeightedOperator_markovian m B hν hi) ht f

/-- Every finite symmetric essential bound is contracted by the heat semigroup. -/
theorem abs_le_const (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) {C : ℝ} (hC : 0 ≤ C)
    (hf : |f| ≤ C • L2.const ν 1) :
    |HeatSemigroup.operator m B hν hi ht f| ≤ C • L2.const ν 1 := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.abs_le_const
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi)
    (closedWeightedOperator_markovian m B hν hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero m B hν hi) f hC hf

end HeatSemigroup

end FunctionalInequalities.KLS.LogConcave

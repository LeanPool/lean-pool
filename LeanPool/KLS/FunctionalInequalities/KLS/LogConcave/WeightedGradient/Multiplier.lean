/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Leibniz
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.LinearPMap
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure
public import LeanPool.KLS.FunctionalInequalities.L2.BoundedMultiplier
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.AdjointClosure

/-!
# Smooth compactly supported multipliers on the domain of the closed weighted gradient

`Energy/WeightedGradient/Leibniz.lean` proves the product rule on the **test class**: the
weighted gradient of a product of two bounded tests is `g₁ (B ∇g₂) + g₂ (B ∇g₁)`. That rule does
not by itself say anything about `Tbar = hν.closedWeightedOperator m B hi`, whose domain contains
the test classes but is defined as a graph closure, so a general element of it carries no
classical derivative. This module proves the two statements that a closed operator needs:

* `exists_seq_smooth_tendsto_graph`: smooth compactly supported classes are a **graph-norm core**
  of `Tbar`, in the explicit sequential form. This is `closure_domRestrict_eq_of_smoothCore_le`
  unpacked through `Submodule.topologicalClosure`; together with the classical product rule on
  tests and the bounded multiplication operators it is the only input below.
* `toLp_mul_mem_closedWeightedOperator_domain` and `coeFn_closedWeightedOperator_toLp_mul`: for
  `φ ∈ C_c^∞(V)` and **every** `x ∈ D(Tbar)`, the class of `φ x` again lies in `D(Tbar)` and
  `Tbar (φ x) = φ (Tbar x) + x (B ∇φ)` almost everywhere.

The second statement is an honest extension of the test-class rule, not a restatement: its input
`x` is an arbitrary form-domain element, and the proof goes through closedness of `Tbar` and the
two bounded multiplication operators of `L2/BoundedMultiplier.lean`. Boundedness of `φ` and of
`B ∇φ` — both automatic for a smooth compactly supported `φ` — is what makes the two limits
converge; no boundedness of `x` is assumed and none is available.

Nothing here is a statement about the generator `Tbar†Tbar`, about a semigroup, or about `Γ₂`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Core

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **Smooth compactly supported classes are a graph-norm core of `Tbar`.** Every `x ∈ D(Tbar)` is the
`L²` limit of classes `[gₙ]` of smooth compactly supported functions whose weighted gradients
`[B ∇gₙ]` converge in `L²` to `Tbar x`. This is the sequential form of
`closure_domRestrict_eq_of_smoothCore_le`; it controls the function and its **first** derivative
only, and says nothing about any second-order quantity. -/
theorem exists_seq_smooth_tendsto_graph (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hgc : ∀ n, HasCompactSupport (g n)),
      Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))
          atTop (𝓝 (x : Lp ℝ 2 (ν : Measure V))) ∧
        Tendsto (fun n => (IsTest.of_contDiff_hasCompactSupport ν B (hg n)
            (hgc n)).memLp_apply.toLp (apply B (g n))) atTop
          (𝓝 (hν.closedWeightedOperator m B hi x)) := by
  classical
  have hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  have hScl : ((hν.weightedOperator m B hi).domRestrict (smoothCore ν)).closure =
      hν.closedWeightedOperator m B hi :=
    hν.closure_domRestrict_eq_of_smoothCore_le m B hi le_rfl
      (smoothCore_le_domain_operator ν B hac)
  have hSc : ((hν.weightedOperator m B hi).domRestrict (smoothCore ν)).IsClosable :=
    (hν.weightedOperator_isClosable m B hi).leIsClosable LinearPMap.domRestrict_le
  have hgraph : ((x : Lp ℝ 2 (ν : Measure V)), hν.closedWeightedOperator m B hi x)
      ∈ ((hν.weightedOperator m B hi).domRestrict (smoothCore ν)).graph.topologicalClosure := by
    rw [hSc.graph_closure_eq_closure_graph, hScl]
    exact (hν.closedWeightedOperator m B hi).mem_graph x
  obtain ⟨f, hf⟩ :=
    (Energy.mem_graph_topologicalClosure_iff
      ((hν.weightedOperator m B hi).domRestrict (smoothCore ν)) _).mp hgraph
  have hmem : ∀ n, ∃ (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g),
      (f n : Lp ℝ 2 (ν : Measure V))
        = (memLp_of_contDiff_hasCompactSupport ν hg hgc).toLp g :=
    fun n => (Submodule.mem_inf.mp (f n).2).1
  choose g hg hgc hgeq using hmem
  have hval : ∀ n, (hν.weightedOperator m B hi).domRestrict (smoothCore ν) (f n) =
      (IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.toLp
        (apply B (g n)) := by
    intro n
    have hdom : (f n : Lp ℝ 2 (ν : Measure V)) ∈ (hν.weightedOperator m B hi).domain :=
      (Submodule.mem_inf.mp (f n).2).2
    erw [LinearPMap.domRestrict_apply (x := f n) (y := ⟨_, hdom⟩) rfl]
    exact operator_apply ν B hac (hν.frontier_support_eq_zero hi)
      (IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)) hdom (hgeq n)
  refine ⟨g, hg, hgc, ?_, ?_⟩
  · have h1 : Tendsto (fun n => (f n : Lp ℝ 2 (ν : Measure V))) atTop
        (𝓝 (x : Lp ℝ 2 (ν : Measure V))) := by
      have h := (continuous_fst.tendsto ((x : Lp ℝ 2 (ν : Measure V)),
        hν.closedWeightedOperator m B hi x)).comp hf
      simpa [Function.comp_def] using h
    exact h1.congr fun n => hgeq n
  · have h2 : Tendsto
        (fun n => (hν.weightedOperator m B hi).domRestrict (smoothCore ν) (f n)) atTop
        (𝓝 (hν.closedWeightedOperator m B hi x)) := by
      have h := (continuous_snd.tendsto ((x : Lp ℝ 2 (ν : Measure V)),
        hν.closedWeightedOperator m B hi x)).comp hf
      simpa [Function.comp_def] using h
    exact h2.congr fun n => hval n

end Core

section Multiplier

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- A smooth compactly supported multiplier preserves `L²(ν)`. -/
theorem memLp_mul_of_contDiff_hasCompactSupport {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (u : Lp ℝ 2 (ν : Measure V)) :
    MemLp (fun y => φ y * u y) 2 (ν : Measure V) := by
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hb : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ M :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
  simpa only [smul_eq_mul] using
    L2.memLp_bddSmul (H := ℝ) hφ.continuous.aestronglyMeasurable hb u

/-- **Leibniz rule for the closed weighted gradient against a smooth compactly supported
multiplier.** For `φ ∈ C_c^∞(V)` and **every** `x ∈ D(Tbar)` the class of `φ x` lies in `D(Tbar)`, and

`Tbar (φ x) = φ (Tbar x) + x (B ∇φ)`  almost everywhere.

The proof approximates `x` in the graph norm by smooth compactly supported `gₙ`
(`exists_seq_smooth_tendsto_graph`), applies the classical product rule to `φ gₙ`, and passes to
the limit: both `φ` and `B ∇φ` are bounded, so multiplication by either is a bounded operator on
`L²`, and closedness of `Tbar` identifies the limit. No boundedness or differentiability of `x` is
used. -/
theorem exists_mem_domain_closedWeightedOperator_toLp_mul {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ hmem : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain,
      ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
        =ᵐ[(ν : Measure V)] fun y =>
          φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
            + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y := by
  classical
  have hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  have hβcont : Continuous (apply B φ) :=
    B.continuous.comp (Analysis.BakryEmery.continuous_gradient hφ1)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨N, hN⟩ := hβcont.bounded_above_of_compact_support (hasCompactSupport_apply B hφc)
  have hMb : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ M :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
  have hNb : ∀ᵐ y ∂(ν : Measure V), ‖apply B φ y‖ ≤ N := Filter.Eventually.of_forall hN
  set cm := L2.bddSmulL (H := ℝ) hφ.continuous.aestronglyMeasurable hMb with hcm
  set cv := L2.bddSmulL (H := V) hφ.continuous.aestronglyMeasurable hMb with hcv
  set cr := L2.bddSmulRightL (H := V) hβcont.aestronglyMeasurable hNb with hcr
  obtain ⟨g, hg, hgc, h1, h2⟩ := hν.exists_seq_smooth_tendsto_graph m B hi x
  -- the smooth products and their membership
  have hprod : ∀ n, ContDiff ℝ ∞ fun y => φ y * g n y := fun n => hφ.mul (hg n)
  have hprodc : ∀ n, HasCompactSupport fun y => φ y * g n y := fun n => hφc.mul_right
  have htest : ∀ n, IsTest ν B fun y => φ y * g n y := fun n =>
    IsTest.of_contDiff_hasCompactSupport ν B (hprod n) (hprodc n)
  have hdom : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hprod n) (hprodc n)).toLp
      (fun y => φ y * g n y) ∈ (hν.closedWeightedOperator m B hi).domain := fun n =>
    hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi (htest n)
  -- the first convergence
  have e1 : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hprod n) (hprodc n)).toLp
      (fun y => φ y * g n y)
      = cm ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
    intro n
    refine Lp.ext ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν (hprod n) (hprodc n)).coeFn_toLp,
      L2.coeFn_bddSmulL (H := ℝ) hφ.continuous.aestronglyMeasurable hMb
        ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
      (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp] with y hy1 hy2 hy3
    rw [hy1, hcm, hy2, hy3, smul_eq_mul]
  have e0 : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
      (x : Lp ℝ 2 (ν : Measure V))).toLp _ = cm (x : Lp ℝ 2 (ν : Measure V)) := by
    refine Lp.ext ?_
    filter_upwards [(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).coeFn_toLp,
      L2.coeFn_bddSmulL (H := ℝ) hφ.continuous.aestronglyMeasurable hMb
        (x : Lp ℝ 2 (ν : Measure V))] with y hy1 hy2
    rw [hy1, hcm, hy2, smul_eq_mul]
  have hconv1 : Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hprod n)
      (hprodc n)).toLp (fun y => φ y * g n y)) atTop
      (𝓝 ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _)) := by
    rw [e0]
    exact ((cm.continuous.tendsto _).comp h1).congr fun n => (e1 n).symm
  -- the second convergence
  have e2 : ∀ n, hν.closedWeightedOperator m B hi ⟨_, hdom n⟩
      = cv ((IsTest.of_contDiff_hasCompactSupport ν B (hg n)
          (hgc n)).memLp_apply.toLp (apply B (g n)))
        + cr ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
    intro n
    have hrep := hν.closedWeightedOperator_apply_toLp m B hi (htest n)
    have hsub : (⟨_, hdom n⟩ : (hν.closedWeightedOperator m B hi).domain)
        = ⟨(htest n).memLp.toLp _, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi
            (htest n)⟩ := rfl
    rw [hsub, hrep]
    refine Lp.ext ?_
    filter_upwards [(htest n).memLp_apply.coeFn_toLp,
      Lp.coeFn_add (cv ((IsTest.of_contDiff_hasCompactSupport ν B (hg n)
          (hgc n)).memLp_apply.toLp (apply B (g n))))
        (cr ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))),
      L2.coeFn_bddSmulL (H := V) hφ.continuous.aestronglyMeasurable hMb
        ((IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.toLp
          (apply B (g n))),
      L2.coeFn_bddSmulRightL (H := V) hβcont.aestronglyMeasurable hNb
        ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
      (IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.coeFn_toLp,
      (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp,
      IsTest.apply_mul_ae (m := m) hac (IsTest.of_contDiff_hasCompactSupport ν B hφ hφc)
        (IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n))] with
      y hy1 hy2 hy3 hy4 hy5 hy6 hy7
    rw [hy1, hy2, Pi.add_apply, hcv, hy3, hcr, hy4, hy5, hy6, hy7]
  have hconv2 : Tendsto (fun n => hν.closedWeightedOperator m B hi ⟨_, hdom n⟩) atTop
      (𝓝 (cv (hν.closedWeightedOperator m B hi x) + cr (x : Lp ℝ 2 (ν : Measure V)))) := by
    refine Tendsto.congr (fun n => (e2 n).symm) ?_
    exact (((cv.continuous.tendsto _).comp h2).add ((cr.continuous.tendsto _).comp h1))
  obtain ⟨hmem, heq⟩ := exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m B hi) hdom hconv1 hconv2
  refine ⟨hmem, ?_⟩
  rw [heq]
  filter_upwards [Lp.coeFn_add (cv (hν.closedWeightedOperator m B hi x))
      (cr (x : Lp ℝ 2 (ν : Measure V))),
    L2.coeFn_bddSmulL (H := V) hφ.continuous.aestronglyMeasurable hMb
      (hν.closedWeightedOperator m B hi x),
    L2.coeFn_bddSmulRightL (H := V) hβcont.aestronglyMeasurable hNb
      (x : Lp ℝ 2 (ν : Measure V))] with y hy1 hy2 hy3
  rw [hy1, Pi.add_apply, hcv, hy2, hcr, hy3]

/-- The domain clause of `exists_mem_domain_closedWeightedOperator_toLp_mul`. -/
theorem toLp_mul_mem_closedWeightedOperator_domain {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain) :
    (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain :=
  (hν.exists_mem_domain_closedWeightedOperator_toLp_mul m B hi hφ hφc x).choose

/-- The value clause of `exists_mem_domain_closedWeightedOperator_toLp_mul`. -/
theorem coeFn_closedWeightedOperator_toLp_mul {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain)
    (hmem : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain) :
    ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
      =ᵐ[(ν : Measure V)] fun y =>
        φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
          + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y :=
  (hν.exists_mem_domain_closedWeightedOperator_toLp_mul m B hi hφ hφc x).choose_spec

end Multiplier

end FunctionalInequalities.KLS.LogConcave

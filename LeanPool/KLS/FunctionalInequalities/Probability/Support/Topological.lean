/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Topological support under pushforward, restriction and density

For an open-positive measure: the support of a continuous pushforward is the closure of the range;
restriction to a closed
set equal to the closure of its interior (in particular a closed convex set with nonempty interior)
has that set as support;
an a.e. nonzero density preserves the support, so `1_K e^{−W} μ` has support `K`.
-/

@[expose] public section

section

namespace FunctionalInequalities.Probability

section PushforwardRestriction

open Set MeasureTheory
open scoped Topology

/--
For an open-positive `μ` and continuous `f`, the support of `f_* μ` is the closure of the range of
`f`. -/
theorem support_map_eq_closure_range {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.IsOpenPosMeasure] {f : X → Y} (hf : Continuous f) :
    (μ.map f).support = closure (range f) := by
  ext y
  rw [Measure.support_eq_forall_isOpen, mem_ofPred_eq, mem_closure_iff]
  constructor
  · intro hy V hV hyV
    have hp := hy V hyV hV
    rw [Measure.map_apply hf.measurable hV.measurableSet] at hp
    by_contra hn
    have he : f ⁻¹' V = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hn ⟨f x, hx, mem_range_self x⟩
    simp [he] at hp
  · intro hy V hyV hV
    obtain ⟨z, hzV, x, rfl⟩ := hy V hV hyV
    rw [Measure.map_apply hf.measurable hV.measurableSet]
    exact (hf.isOpen_preimage V hV).measure_pos μ ⟨x, hzV⟩

/--
For an open-positive `μ` and closed `K` with `closure (interior K) = K`, the support of the
restriction `μ|_K` is `K`. -/
theorem support_restrict_eq_of_closure_interior {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {K : Set X} (hK : IsClosed K) (hKi : closure (interior K) = K) :
    (μ.restrict K).support = K := by
  apply Subset.antisymm
  · exact (Measure.support_restrict_subset.trans inter_subset_left).trans_eq hK.closure_eq
  · have hh : closure (interior K) ⊆ (μ.restrict K).support := by
      apply closure_minimal _ Measure.isClosed_support
      intro x hx
      exact Measure.interior_inter_support ⟨hx, by rw [Measure.support_eq_univ]; trivial⟩
    rwa [hKi] at hh

/--
For an open-positive `μ` on a real normed space and a closed convex `K` with nonempty interior, the
support of `μ|_K` is
`K`. -/
theorem support_restrict_eq_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) [μ.IsOpenPosMeasure]
    {K : Set E} (hc : Convex ℝ K) (hK : IsClosed K) (hi : (interior K).Nonempty) :
    (μ.restrict K).support = K :=
  support_restrict_eq_of_closure_interior μ hK
    ((hc.closure_interior_eq_closure_of_nonempty_interior hi).trans hK.closure_eq)

end PushforwardRestriction

section PositiveDensity

open Set MeasureTheory
open scoped Topology ENNReal

/-- An a.e. measurable density that is a.e. nonzero does not change the support. -/
theorem support_withDensity_eq_of_ae_ne_zero {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) {w : X → ℝ≥0∞}
    (hw : AEMeasurable w μ) (hn : ∀ᵐ x ∂μ, w x ≠ 0) :
    (μ.withDensity w).support = μ.support :=
  Subset.antisymm (withDensity_absolutelyContinuous μ w).support_mono
    (withDensity_absolutelyContinuous' hw hn).support_mono

/--
For an open-positive `μ`, a closed convex `K` with nonempty interior and continuous `W`, the support
of `1_K e^{−W} μ`
is `K`. -/
theorem support_indicator_exp_neg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsOpenPosMeasure] {K : Set E}
    (hc : Convex ℝ K) (hK : IsClosed K) (hi : (interior K).Nonempty) {W : E → ℝ}
    (hW : Continuous W) :
    (μ.withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))).support = K := by
  rw [withDensity_indicator hK.measurableSet]
  have hw : Measurable (fun p => ENNReal.ofReal (Real.exp (-W p))) :=
    Measurable.ennreal_ofReal (Real.continuous_exp.measurable.comp hW.measurable.neg)
  exact
    (support_withDensity_eq_of_ae_ne_zero (μ.restrict K) hw.aemeasurable
          (Filter.Eventually.of_forall (fun x => by positivity))).trans
      (support_restrict_eq_of_convex μ hc hK hi)

end PositiveDensity

end FunctionalInequalities.Probability
